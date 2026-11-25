// SPDX-FileCopyrightText: 2026 ARMSX2 Contributors
// SPDX-License-Identifier: GPL-3.0+

package com.armsx2

import android.content.ContentValues
import android.content.Context
import android.media.MediaCodec
import android.media.MediaCodecInfo
import android.media.MediaFormat
import android.media.MediaMuxer
import android.opengl.EGL14
import android.opengl.EGLConfig
import android.opengl.EGLContext
import android.opengl.EGLDisplay
import android.opengl.EGLExt
import android.opengl.EGLSurface
import android.opengl.GLES11Ext
import android.opengl.GLES20
import android.os.Build
import android.os.Bundle
import android.os.Environment
import android.provider.MediaStore
import android.util.Log
import android.view.Surface
import androidx.compose.runtime.mutableStateOf
import androidx.core.content.edit
import com.armsx2.input.ControllerMappings
import com.armsx2.runtime.MainActivityRuntime
import com.armsx2.ui.touch.TouchButtonId
import com.armsx2.ui.touch.TouchControls
import kr.co.iefriends.pcsx2.NativeApp
import java.io.File
import java.nio.ByteBuffer
import java.nio.ByteOrder
import java.nio.FloatBuffer
import java.text.SimpleDateFormat
import java.util.ArrayDeque
import java.util.Date
import java.util.Locale
import java.util.concurrent.atomic.AtomicBoolean

private const val TAG = "GameplayRecorder"
private const val ALBUM = "ARMSX2"
private const val SAMPLE_RATE = 48000
private const val AUDIO_CHANNELS = 2
private const val AUDIO_BITRATE = 128_000
private const val VIDEO_BITRATE_720P = 8_000_000
private const val VIDEO_BITRATE_1080P = 12_000_000
private const val VIDEO_BITRATE_480P = 4_000_000
private const val MAX_RING_BYTES = 128L * 1024L * 1024L

/**
 * Emulated-time gameplay video recorder and instant-replay (Save Clip) buffer.
 *
 * Captures frames directly from the GS renderer (via GSRemotePlay) and raw mixed audio from
 * SPU2 before output volume, mute, or time-stretching. Both video and audio are timestamped on
 * the emulated SPU2 audio clock, so recordings and saved clips always play back at 1x normal speed
 * with full-volume game audio even when fast-forwarding or muted.
 */
object GameplayRecorder {
    private const val PREF_CLIP_SECONDS = "recording.clipSeconds"
    private const val PREF_MAX_HEIGHT = "recording.maxHeight"
    const val DEFAULT_CLIP_SECONDS = 30
    const val MIN_CLIP_SECONDS = 5
    const val MAX_CLIP_SECONDS = 120

    val isRecording = mutableStateOf(false)
    val isBuffering = mutableStateOf(false)

    private val lock = Any()
    private val running = AtomicBoolean(false)

    private var appContext: Context? = null
    private var captureThread: Thread? = null
    private var audioThread: Thread? = null

    private var liveWanted = false
    private var replayWanted = false

    // Formats published by MediaCodec once INFO_OUTPUT_FORMAT_CHANGED fires.
    @Volatile
    private var videoFormat: MediaFormat? = null
    @Volatile
    private var audioFormat: MediaFormat? = null
    @Volatile
    private var videoCodecRef: MediaCodec? = null

    // Live recording muxer state (guarded by muxLock).
    private val muxLock = Any()
    private var liveMuxer: MediaMuxer? = null
    private var liveTempFile: File? = null
    private var liveVideoTrack = -1
    private var liveAudioTrack = -1
    private var liveStarted = false
    private var liveWaitingKeyframe = false
    private var liveBasePtsUs = -1L
    private var liveLastVideoPtsUs = -1L
    private var liveLastAudioPtsUs = -1L
    private val livePreQueue = ArrayDeque<EncodedPacket>()

    // Rolling replay buffer (guarded by ringLock).
    private val ringLock = Any()
    private val replayRing = ArrayDeque<EncodedPacket>()
    private var ringBytes = 0L

    private class EncodedPacket(
        val isVideo: Boolean,
        val data: ByteArray,
        val flags: Int,
        val ptsUs: Long,
    )

    fun clipSeconds(): Int =
        MainActivityRuntime.prefs.getInt(PREF_CLIP_SECONDS, DEFAULT_CLIP_SECONDS)
            .coerceIn(MIN_CLIP_SECONDS, MAX_CLIP_SECONDS)

    fun setClipSeconds(seconds: Int) {
        MainActivityRuntime.prefs.edit {
            putInt(PREF_CLIP_SECONDS, seconds.coerceIn(MIN_CLIP_SECONDS, MAX_CLIP_SECONDS))
        }
    }

    fun maxHeight(): Int =
        MainActivityRuntime.prefs.getInt(PREF_MAX_HEIGHT, 720).let {
            if (it == 480 || it == 720 || it == 1080) it else 720
        }

    fun setMaxHeight(height: Int) {
        val clamped = if (height == 480 || height == 720 || height == 1080) height else 720
        MainActivityRuntime.prefs.edit { putInt(PREF_MAX_HEIGHT, clamped) }
    }

    /** True if the user has the Save Clip on-screen button enabled or a Save Clip hotkey bound. */
    fun isReplayFeatureAvailable(): Boolean {
        val layout = TouchControls.activeLayout.value
        val buttonOn = layout.buttons.any { it.id == TouchButtonId.SAVE_CLIP && it.enabled }
        if (buttonOn) return true
        val hotkey = runCatching {
            ControllerMappings.hotkeyKeycode(ControllerMappings.SysHotkey.SAVE_CLIP)
        }.getOrDefault(0)
        return hotkey != 0
    }

    /** Syncs the background replay buffer with whether a Save Clip control is active and a VM is running. */
    fun syncReplayBuffer(context: Context, vmRunning: Boolean) {
        val wantReplay = vmRunning && isReplayFeatureAvailable()
        var needStart = false
        var needStop = false
        synchronized(lock) {
            appContext = context.applicationContext
            if (wantReplay == replayWanted) return
            replayWanted = wantReplay
            isBuffering.value = wantReplay
            if (wantReplay && !running.get()) {
                needStart = true
            } else if (!wantReplay && !liveWanted && running.get()) {
                needStop = true
            }
        }
        if (needStart) {
            // The GS renderer may still be initializing right after VM boot; retry briefly.
            kotlin.concurrent.thread(isDaemon = true, name = "rec-sync") {
                for (attempt in 0 until 10) {
                    val stillWanted = synchronized(lock) { replayWanted && !running.get() }
                    if (!stillWanted) return@thread
                    if (startSession(context.applicationContext)) return@thread
                    Thread.sleep(300)
                }
            }
        }
        if (needStop) stopSession()
    }

    /** Toggles live gameplay recording on/off. */
    fun toggleRecording(context: Context): Boolean {
        return if (isRecording.value) {
            stopRecording(context)
            false
        } else {
            startRecording(context)
        }
    }

    fun startRecording(context: Context): Boolean {
        val ctx = context.applicationContext
        if (!NativeApp.hasActiveVM()) {
            showToast(ctx, "No game running")
            return false
        }
        var needStart = false
        synchronized(lock) {
            appContext = ctx
            if (liveWanted) return true
            val temp = File(ctx.cacheDir, "armsx2_rec_${System.currentTimeMillis()}.mp4")
            synchronized(muxLock) {
                resetLiveMuxerLocked()
                liveTempFile = temp
                liveWaitingKeyframe = true
                liveBasePtsUs = -1L
                liveLastVideoPtsUs = -1L
                liveLastAudioPtsUs = -1L
                livePreQueue.clear()
            }
            liveWanted = true
            isRecording.value = true
            if (!running.get()) {
                needStart = true
            } else {
                // Encoder is already running for replay buffer: request a fresh IDR frame.
                requestSyncFrame()
            }
        }
        if (needStart && !startSession(ctx)) {
            synchronized(lock) {
                liveWanted = false
                isRecording.value = false
            }
            synchronized(muxLock) {
                liveTempFile?.delete()
                resetLiveMuxerLocked()
            }
            showToast(ctx, "Recording unavailable on this renderer or during Remote Play")
            return false
        }
        showToast(ctx, "Recording started")
        return true
    }

    fun stopRecording(context: Context) {
        val ctx = context.applicationContext
        var fileToPublish: File? = null
        var muxerToClose: MediaMuxer? = null
        var hadFrames = false
        var shouldStopSession = false

        synchronized(lock) {
            if (!liveWanted) return
            liveWanted = false
            isRecording.value = false
            shouldStopSession = !replayWanted
        }

        synchronized(muxLock) {
            muxerToClose = liveMuxer
            fileToPublish = liveTempFile
            hadFrames = liveStarted && liveLastVideoPtsUs >= 0L
            resetLiveMuxerLocked()
        }

        if (shouldStopSession) {
            stopSession()
        }

        kotlin.concurrent.thread(isDaemon = true, name = "rec-finalize") {
            runCatching { muxerToClose?.stop() }
            runCatching { muxerToClose?.release() }
            val f = fileToPublish
            if (f != null && hadFrames && f.exists() && f.length() > 0L) {
                val savedName = publishVideo(ctx, f, prefix = "ARMSX2_Rec")
                f.delete()
                if (savedName != null) {
                    showToast(ctx, "Saved recording: $savedName")
                } else {
                    showToast(ctx, "Failed to save recording")
                }
            } else {
                f?.delete()
                showToast(ctx, "Recording stopped (no frames)")
            }
        }
    }

    /** Saves the last [clipSeconds] of buffered gameplay into Movies/ARMSX2. */
    fun saveClip(context: Context) {
        val ctx = context.applicationContext
        if (!NativeApp.hasActiveVM()) {
            showToast(ctx, "No game running")
            return
        }
        if (!running.get()) {
            syncReplayBuffer(ctx, true)
            showToast(ctx, "Replay buffer started — try again in a moment")
            return
        }

        val vFmt = videoFormat
        val aFmt = audioFormat
        if (vFmt == null || aFmt == null) {
            showToast(ctx, "Clip buffer warming up…")
            return
        }

        val windowUs = clipSeconds() * 1_000_000L
        val snapshot: List<EncodedPacket>
        synchronized(ringLock) {
            if (replayRing.isEmpty()) {
                showToast(ctx, "Clip buffer empty")
                return
            }
            val latestPts = replayRing.last().ptsUs
            val cutoffPts = (latestPts - windowUs).coerceAtLeast(0L)
            var startIdx = -1
            var lastKeyframeBeforeCutoff = -1
            var i = 0
            for (pkt in replayRing) {
                if (pkt.isVideo && (pkt.flags and MediaCodec.BUFFER_FLAG_KEY_FRAME) != 0) {
                    if (pkt.ptsUs <= cutoffPts) {
                        lastKeyframeBeforeCutoff = i
                    } else if (startIdx == -1) {
                        startIdx = i
                    }
                }
                i++
            }
            val chosenStart = when {
                lastKeyframeBeforeCutoff >= 0 -> lastKeyframeBeforeCutoff
                startIdx >= 0 -> startIdx
                else -> -1
            }
            if (chosenStart < 0) {
                showToast(ctx, "Clip buffer waiting for keyframe…")
                return
            }
            snapshot = replayRing.drop(chosenStart)
        }

        val basePts = snapshot.first().ptsUs
        val actualSec = ((snapshot.last().ptsUs - basePts) / 1_000_000L).toInt().coerceAtLeast(1)

        kotlin.concurrent.thread(isDaemon = true, name = "rec-save-clip") {
            val temp = File(ctx.cacheDir, "armsx2_clip_${System.currentTimeMillis()}.mp4")
            var muxer: MediaMuxer? = null
            var wroteVideo = false
            try {
                muxer = MediaMuxer(temp.absolutePath, MediaMuxer.OutputFormat.MUXER_OUTPUT_MPEG_4)
                val vTrack = muxer.addTrack(vFmt)
                val aTrack = muxer.addTrack(aFmt)
                muxer.start()

                val info = MediaCodec.BufferInfo()
                var lastV = -1L
                var lastA = -1L
                for (pkt in snapshot) {
                    if ((pkt.flags and MediaCodec.BUFFER_FLAG_CODEC_CONFIG) != 0) continue
                    val rawPts = (pkt.ptsUs - basePts).coerceAtLeast(0L)
                    val pts = if (pkt.isVideo) {
                        val p = if (rawPts <= lastV) lastV + 1L else rawPts
                        lastV = p
                        wroteVideo = true
                        p
                    } else {
                        val p = if (rawPts <= lastA) lastA + 1L else rawPts
                        lastA = p
                        p
                    }
                    info.set(0, pkt.data.size, pts, pkt.flags)
                    muxer.writeSampleData(if (pkt.isVideo) vTrack else aTrack, ByteBuffer.wrap(pkt.data), info)
                }
                muxer.stop()
                muxer.release()
                muxer = null

                if (wroteVideo && temp.exists() && temp.length() > 0L) {
                    val savedName = publishVideo(ctx, temp, prefix = "ARMSX2_Clip_${actualSec}s")
                    temp.delete()
                    if (savedName != null) {
                        showToast(ctx, "Saved ${actualSec}s clip: $savedName")
                    } else {
                        showToast(ctx, "Failed to save clip")
                    }
                } else {
                    temp.delete()
                    showToast(ctx, "Clip had no video frames")
                }
            } catch (t: Throwable) {
                Log.e(TAG, "saveClip failed", t)
                runCatching { muxer?.stop() }
                runCatching { muxer?.release() }
                temp.delete()
                showToast(ctx, "Failed to save clip")
            }
        }
    }

    /** Stops live recording (saving it) and tears down any background replay buffer on pause/exit. */
    fun onGameStoppedOrPaused(context: Context) {
        if (isRecording.value) {
            stopRecording(context)
        }
        var shouldStop = false
        synchronized(lock) {
            replayWanted = false
            isBuffering.value = false
            if (running.get() && !liveWanted) {
                shouldStop = true
            }
        }
        if (shouldStop) {
            stopSession()
        }
    }

    private fun startSession(context: Context): Boolean {
        val maxH = maxHeight()
        val maxW = when (maxH) {
            1080 -> 1920
            480 -> 854
            else -> 1280
        }
        if (!NativeApp.recStart(maxW, maxH, true)) {
            return false
        }

        synchronized(ringLock) {
            replayRing.clear()
            ringBytes = 0L
        }
        videoFormat = null
        audioFormat = null
        running.set(true)

        captureThread = kotlin.concurrent.thread(isDaemon = true, name = "rec-video") {
            runVideoLoop(maxW, maxH)
        }
        audioThread = kotlin.concurrent.thread(isDaemon = true, name = "rec-audio") {
            runAudioLoop()
        }
        return true
    }

    private fun stopSession() {
        running.set(false)
        NativeApp.recStop()
        runCatching { captureThread?.join(1500) }
        runCatching { audioThread?.join(1500) }
        captureThread = null
        audioThread = null
        videoCodecRef = null
        videoFormat = null
        audioFormat = null
        synchronized(ringLock) {
            replayRing.clear()
            ringBytes = 0L
        }
    }

    private fun runVideoLoop(maxW: Int, maxH: Int) {
        val info = LongArray(6)
        var rgbaBuf = ByteBuffer.allocateDirect(maxW * maxH * 4)
        var hardware = true

        var encoder: MediaCodec? = null
        var egl: GlInputSurface? = null
        var encW = 0
        var encH = 0
        var lastPtsUs = -1L

        val textures = IntArray(4)
        val images = LongArray(4)
        val generations = IntArray(4) { -1 }
        var readbackTex = 0
        var readbackW = 0
        var readbackH = 0

        val outInfo = MediaCodec.BufferInfo()

        try {
            while (running.get()) {
                val res = NativeApp.recPollVideo(rgbaBuf, info, 50)
                if (res == -1) break
                if (res == 0) {
                    encoder?.let { drainCodec(it, isVideo = true, outInfo) }
                    continue
                }
                if (res == -2) {
                    val needBytes = (info[0].toInt() * info[1].toInt() * 4).coerceAtLeast(4096)
                    if (rgbaBuf.capacity() < needBytes) {
                        rgbaBuf = ByteBuffer.allocateDirect(needBytes)
                    }
                    continue
                }

                val srcW = info[0].toInt().coerceAtLeast(16)
                val srcH = info[1].toInt().coerceAtLeast(16)
                val slot = info[2].toInt()
                val gen = info[3].toInt()
                val seq = info[4].toInt()
                val rawPtsUs = info[5]

                if (NativeApp.recIsPaused()) {
                    if (res == 2) NativeApp.recReleaseFrame(slot, seq)
                    continue
                }

                if (encoder == null) {
                    // Align to even dimensions for H.264.
                    encW = (srcW and 1.inv()).coerceAtLeast(16)
                    encH = (srcH and 1.inv()).coerceAtLeast(16)
                    val bitrate = when {
                        encH >= 1000 -> VIDEO_BITRATE_1080P
                        encH <= 500 -> VIDEO_BITRATE_480P
                        else -> VIDEO_BITRATE_720P
                    }
                    val fmt = MediaFormat.createVideoFormat(MediaFormat.MIMETYPE_VIDEO_AVC, encW, encH).apply {
                        setInteger(MediaFormat.KEY_COLOR_FORMAT, MediaCodecInfo.CodecCapabilities.COLOR_FormatSurface)
                        setInteger(MediaFormat.KEY_BIT_RATE, bitrate)
                        setInteger(MediaFormat.KEY_FRAME_RATE, 60)
                        setInteger(MediaFormat.KEY_I_FRAME_INTERVAL, 1)
                    }
                    val codec = MediaCodec.createEncoderByType(MediaFormat.MIMETYPE_VIDEO_AVC)
                    codec.configure(fmt, null, null, MediaCodec.CONFIGURE_FLAG_ENCODE)
                    val inputSurface = codec.createInputSurface()
                    codec.start()

                    egl = GlInputSurface(inputSurface, encW, encH)
                    egl.makeCurrent()
                    GLES20.glGenTextures(4, textures, 0)
                    val tmp = IntArray(1)
                    GLES20.glGenTextures(1, tmp, 0)
                    readbackTex = tmp[0]

                    encoder = codec
                    videoCodecRef = codec
                }

                val ptsUs = if (rawPtsUs <= lastPtsUs) lastPtsUs + 1L else rawPtsUs
                lastPtsUs = ptsUs

                val surfaceRenderer = egl!!
                if (res == 2) {
                    if (!hardware || slot !in 0..3) {
                        NativeApp.recReleaseFrame(slot, seq)
                        continue
                    }
                    if (generations[slot] != gen) {
                        if (images[slot] != 0L) {
                            NativeApp.remotePlayDestroyImage(images[slot])
                            images[slot] = 0L
                        }
                        val img = NativeApp.remotePlayImportFrame(slot, textures[slot])
                        if (img == 0L) {
                            NativeApp.recReleaseFrame(slot, seq)
                            hardware = false
                            NativeApp.recSetHardware(false)
                            Log.w(TAG, "Hardware frame import failed, falling back to RGBA readback")
                            continue
                        }
                        images[slot] = img
                        generations[slot] = gen
                    }
                    surfaceRenderer.drawOes(textures[slot], ptsUs * 1000L)
                    NativeApp.recReleaseFrame(slot, seq)
                } else {
                    rgbaBuf.rewind()
                    GLES20.glBindTexture(GLES20.GL_TEXTURE_2D, readbackTex)
                    if (readbackW != srcW || readbackH != srcH) {
                        GLES20.glTexParameteri(GLES20.GL_TEXTURE_2D, GLES20.GL_TEXTURE_MIN_FILTER, GLES20.GL_LINEAR)
                        GLES20.glTexParameteri(GLES20.GL_TEXTURE_2D, GLES20.GL_TEXTURE_MAG_FILTER, GLES20.GL_LINEAR)
                        GLES20.glTexParameteri(GLES20.GL_TEXTURE_2D, GLES20.GL_TEXTURE_WRAP_S, GLES20.GL_CLAMP_TO_EDGE)
                        GLES20.glTexParameteri(GLES20.GL_TEXTURE_2D, GLES20.GL_TEXTURE_WRAP_T, GLES20.GL_CLAMP_TO_EDGE)
                        GLES20.glTexImage2D(
                            GLES20.GL_TEXTURE_2D, 0, GLES20.GL_RGBA, srcW, srcH, 0,
                            GLES20.GL_RGBA, GLES20.GL_UNSIGNED_BYTE, rgbaBuf
                        )
                        readbackW = srcW
                        readbackH = srcH
                    } else {
                        GLES20.glTexSubImage2D(
                            GLES20.GL_TEXTURE_2D, 0, 0, 0, srcW, srcH,
                            GLES20.GL_RGBA, GLES20.GL_UNSIGNED_BYTE, rgbaBuf
                        )
                    }
                    GLES20.glBindTexture(GLES20.GL_TEXTURE_2D, 0)
                    surfaceRenderer.draw2D(readbackTex, ptsUs * 1000L)
                }

                drainCodec(encoder, isVideo = true, outInfo)
            }
        } catch (t: Throwable) {
            Log.e(TAG, "Video encoder loop error", t)
        } finally {
            videoCodecRef = null
            runCatching {
                encoder?.let {
                    it.signalEndOfInputStream()
                    drainCodec(it, isVideo = true, outInfo, timeoutUs = 10_000)
                    it.stop()
                    it.release()
                }
            }
            if (egl != null) {
                runCatching {
                    for (slot in 0..3) {
                        if (images[slot] != 0L) NativeApp.remotePlayDestroyImage(images[slot])
                    }
                    GLES20.glDeleteTextures(4, textures, 0)
                    if (readbackTex != 0) GLES20.glDeleteTextures(1, intArrayOf(readbackTex), 0)
                }
                runCatching { egl.release() }
            }
        }
    }

    private fun runAudioLoop() {
        val framesPerChunk = 1024
        val pcmBuf = ByteBuffer.allocateDirect(framesPerChunk * AUDIO_CHANNELS * 2)
        val outPtsUs = LongArray(1)
        val outInfo = MediaCodec.BufferInfo()
        var codec: MediaCodec? = null

        try {
            val fmt = MediaFormat.createAudioFormat(MediaFormat.MIMETYPE_AUDIO_AAC, SAMPLE_RATE, AUDIO_CHANNELS).apply {
                setInteger(MediaFormat.KEY_AAC_PROFILE, MediaCodecInfo.CodecProfileLevel.AACObjectLC)
                setInteger(MediaFormat.KEY_BIT_RATE, AUDIO_BITRATE)
                setInteger(MediaFormat.KEY_MAX_INPUT_SIZE, framesPerChunk * AUDIO_CHANNELS * 2)
            }
            codec = MediaCodec.createEncoderByType(MediaFormat.MIMETYPE_AUDIO_AAC)
            codec.configure(fmt, null, null, MediaCodec.CONFIGURE_FLAG_ENCODE)
            codec.start()

            while (running.get()) {
                pcmBuf.clear()
                val frames = NativeApp.recPollAudio(pcmBuf, framesPerChunk, 50, outPtsUs)
                if (frames == -1) break
                if (frames > 0) {
                    val bytes = frames * AUDIO_CHANNELS * 2
                    val inIdx = codec.dequeueInputBuffer(10_000)
                    if (inIdx >= 0) {
                        val inBuf = codec.getInputBuffer(inIdx)
                        if (inBuf != null) {
                            inBuf.clear()
                            pcmBuf.limit(bytes)
                            inBuf.put(pcmBuf)
                            codec.queueInputBuffer(inIdx, 0, bytes, outPtsUs[0], 0)
                        }
                    }
                }
                drainCodec(codec, isVideo = false, outInfo)
            }
        } catch (t: Throwable) {
            Log.e(TAG, "Audio encoder loop error", t)
        } finally {
            runCatching {
                codec?.let {
                    val inIdx = it.dequeueInputBuffer(5_000)
                    if (inIdx >= 0) {
                        it.queueInputBuffer(inIdx, 0, 0, 0L, MediaCodec.BUFFER_FLAG_END_OF_STREAM)
                    }
                    drainCodec(it, isVideo = false, outInfo, timeoutUs = 10_000)
                    it.stop()
                    it.release()
                }
            }
        }
    }

    private fun drainCodec(
        codec: MediaCodec,
        isVideo: Boolean,
        info: MediaCodec.BufferInfo,
        timeoutUs: Long = 0L,
    ) {
        while (true) {
            val idx = codec.dequeueOutputBuffer(info, timeoutUs)
            if (idx == MediaCodec.INFO_TRY_AGAIN_LATER) break
            if (idx == MediaCodec.INFO_OUTPUT_FORMAT_CHANGED) {
                val fmt = codec.outputFormat
                if (isVideo) videoFormat = fmt else audioFormat = fmt
                continue
            }
            if (idx < 0) continue

            try {
                if (info.size > 0 && (info.flags and MediaCodec.BUFFER_FLAG_CODEC_CONFIG) == 0) {
                    val buf = codec.getOutputBuffer(idx)
                    if (buf != null) {
                        buf.position(info.offset)
                        buf.limit(info.offset + info.size)
                        val copy = ByteArray(info.size)
                        buf.get(copy)
                        onEncodedPacket(EncodedPacket(isVideo, copy, info.flags, info.presentationTimeUs))
                    }
                }
            } finally {
                codec.releaseOutputBuffer(idx, false)
            }
            if ((info.flags and MediaCodec.BUFFER_FLAG_END_OF_STREAM) != 0) break
        }
    }

    private fun onEncodedPacket(pkt: EncodedPacket) {
        // 1. Append to rolling replay buffer if active.
        if (replayWanted) {
            synchronized(ringLock) {
                replayRing.addLast(pkt)
                ringBytes += pkt.data.size
                trimReplayRingLocked(pkt.ptsUs)
            }
        }

        // 2. Write to live recording muxer if active.
        if (liveWanted) {
            synchronized(muxLock) {
                if (!liveWanted) return
                val temp = liveTempFile ?: return
                if (!liveStarted) {
                    val vFmt = videoFormat
                    val aFmt = audioFormat
                    if (vFmt != null && aFmt != null) {
                        try {
                            val muxer = MediaMuxer(temp.absolutePath, MediaMuxer.OutputFormat.MUXER_OUTPUT_MPEG_4)
                            liveVideoTrack = muxer.addTrack(vFmt)
                            liveAudioTrack = muxer.addTrack(aFmt)
                            muxer.start()
                            liveMuxer = muxer
                            liveStarted = true
                            while (livePreQueue.isNotEmpty()) {
                                writeLivePacketLocked(livePreQueue.removeFirst())
                            }
                        } catch (t: Throwable) {
                            Log.e(TAG, "Failed to start live MediaMuxer", t)
                            liveWanted = false
                            isRecording.value = false
                            return
                        }
                    } else {
                        if (livePreQueue.size < 256) livePreQueue.addLast(pkt)
                        return
                    }
                }
                writeLivePacketLocked(pkt)
            }
        }
    }

    private fun writeLivePacketLocked(pkt: EncodedPacket) {
        val muxer = liveMuxer ?: return
        if (liveWaitingKeyframe) {
            if (!pkt.isVideo || (pkt.flags and MediaCodec.BUFFER_FLAG_KEY_FRAME) == 0) return
            liveWaitingKeyframe = false
            liveBasePtsUs = pkt.ptsUs
        }
        val relPts = (pkt.ptsUs - liveBasePtsUs).coerceAtLeast(0L)
        val pts = if (pkt.isVideo) {
            val p = if (relPts <= liveLastVideoPtsUs) liveLastVideoPtsUs + 1L else relPts
            liveLastVideoPtsUs = p
            p
        } else {
            val p = if (relPts <= liveLastAudioPtsUs) liveLastAudioPtsUs + 1L else relPts
            liveLastAudioPtsUs = p
            p
        }
        val info = MediaCodec.BufferInfo().apply {
            set(0, pkt.data.size, pts, pkt.flags)
        }
        val track = if (pkt.isVideo) liveVideoTrack else liveAudioTrack
        runCatching { muxer.writeSampleData(track, ByteBuffer.wrap(pkt.data), info) }
    }

    private fun trimReplayRingLocked(latestPtsUs: Long) {
        val keepUs = (clipSeconds() + 2) * 1_000_000L
        val cutoff = latestPtsUs - keepUs
        if (cutoff <= 0L && ringBytes <= MAX_RING_BYTES) return

        // Always trim up to a video keyframe so the earliest remaining frame is an IDR.
        while (replayRing.size > 2) {
            val first = replayRing.first()
            val overTime = first.ptsUs < cutoff
            val overMem = ringBytes > MAX_RING_BYTES
            if (!overTime && !overMem) break

            // Don't drop a keyframe unless there is another keyframe after it that is still <= cutoff (or overMem).
            if (first.isVideo && (first.flags and MediaCodec.BUFFER_FLAG_KEY_FRAME) != 0) {
                val hasLaterKey = replayRing.drop(1).any {
                    it.isVideo && (it.flags and MediaCodec.BUFFER_FLAG_KEY_FRAME) != 0 &&
                        (overMem || it.ptsUs <= cutoff)
                }
                if (!hasLaterKey) break
            }
            val removed = replayRing.removeFirst()
            ringBytes -= removed.data.size
        }
    }

    private fun requestSyncFrame() {
        runCatching {
            videoCodecRef?.setParameters(Bundle().apply {
                putInt(MediaCodec.PARAMETER_KEY_REQUEST_SYNC_FRAME, 0)
            })
        }
    }

    private fun resetLiveMuxerLocked() {
        liveMuxer = null
        liveTempFile = null
        liveVideoTrack = -1
        liveAudioTrack = -1
        liveStarted = false
        liveWaitingKeyframe = false
        liveBasePtsUs = -1L
        liveLastVideoPtsUs = -1L
        liveLastAudioPtsUs = -1L
        livePreQueue.clear()
    }

    private fun publishVideo(context: Context, mp4: File, prefix: String): String? {
        val stamp = SimpleDateFormat("yyyyMMdd_HHmmss", Locale.US).format(Date())
        val name = "${prefix}_${stamp}.mp4"
        return runCatching {
            if (Build.VERSION.SDK_INT >= Build.VERSION_CODES.Q) {
                val values = ContentValues().apply {
                    put(MediaStore.Video.Media.DISPLAY_NAME, name)
                    put(MediaStore.Video.Media.MIME_TYPE, "video/mp4")
                    put(MediaStore.Video.Media.RELATIVE_PATH, "${Environment.DIRECTORY_MOVIES}/$ALBUM")
                    put(MediaStore.Video.Media.IS_PENDING, 1)
                }
                val resolver = context.contentResolver
                val uri = resolver.insert(MediaStore.Video.Media.EXTERNAL_CONTENT_URI, values) ?: return null
                resolver.openOutputStream(uri)?.use { out -> mp4.inputStream().use { it.copyTo(out) } }
                values.clear()
                values.put(MediaStore.Video.Media.IS_PENDING, 0)
                resolver.update(uri, values, null, null)
                name
            } else {
                @Suppress("DEPRECATION")
                val album = File(
                    Environment.getExternalStoragePublicDirectory(Environment.DIRECTORY_MOVIES),
                    ALBUM,
                )
                album.mkdirs()
                val dest = File(album, name)
                mp4.inputStream().use { input -> dest.outputStream().use { input.copyTo(it) } }
                @Suppress("DEPRECATION")
                android.media.MediaScannerConnection.scanFile(
                    context, arrayOf(dest.absolutePath), arrayOf("video/mp4"), null,
                )
                name
            }
        }.getOrNull()
    }

    private fun showToast(context: Context, msg: String) {
        android.os.Handler(android.os.Looper.getMainLooper()).post {
            android.widget.Toast.makeText(context, msg, android.widget.Toast.LENGTH_SHORT).show()
        }
    }

    /** Minimal EGL14 + GLES2 quad renderer onto MediaCodec's InputSurface. */
    private class GlInputSurface(
        private val surface: Surface,
        private val width: Int,
        private val height: Int,
    ) {
        private var display: EGLDisplay = EGL14.EGL_NO_DISPLAY
        private var context: EGLContext = EGL14.EGL_NO_CONTEXT
        private var eglSurface: EGLSurface = EGL14.EGL_NO_SURFACE

        private var progOes = 0
        private var prog2d = 0
        private val vbo: FloatBuffer = ByteBuffer.allocateDirect(16 * 4)
            .order(ByteOrder.nativeOrder())
            .asFloatBuffer()
            .apply {
                // Interleaved x, y, u, v (flipping v so buffer row 0 lands at top of surface)
                put(floatArrayOf(
                    -1f, -1f, 0f, 1f,
                     1f, -1f, 1f, 1f,
                    -1f,  1f, 0f, 0f,
                     1f,  1f, 1f, 0f,
                ))
                position(0)
            }

        init {
            display = EGL14.eglGetDisplay(EGL14.EGL_DEFAULT_DISPLAY)
            val version = IntArray(2)
            EGL14.eglInitialize(display, version, 0, version, 1)

            val attribList = intArrayOf(
                EGL14.EGL_RED_SIZE, 8,
                EGL14.EGL_GREEN_SIZE, 8,
                EGL14.EGL_BLUE_SIZE, 8,
                EGL14.EGL_ALPHA_SIZE, 8,
                EGL14.EGL_RENDERABLE_TYPE, EGL14.EGL_OPENGL_ES2_BIT,
                EGL_RECORDABLE_ANDROID, 1,
                EGL14.EGL_NONE
            )
            val configs = arrayOfNulls<EGLConfig>(1)
            val numConfigs = IntArray(1)
            EGL14.eglChooseConfig(display, attribList, 0, configs, 0, 1, numConfigs, 0)

            val ctxAttribs = intArrayOf(EGL14.EGL_CONTEXT_CLIENT_VERSION, 2, EGL14.EGL_NONE)
            context = EGL14.eglCreateContext(display, configs[0], EGL14.EGL_NO_CONTEXT, ctxAttribs, 0)

            val surfAttribs = intArrayOf(EGL14.EGL_NONE)
            eglSurface = EGL14.eglCreateWindowSurface(display, configs[0], surface, surfAttribs, 0)
        }

        fun makeCurrent() {
            EGL14.eglMakeCurrent(display, eglSurface, eglSurface, context)
            if (progOes == 0) progOes = buildProgram(FS_OES)
            if (prog2d == 0) prog2d = buildProgram(FS_2D)
            GLES20.glViewport(0, 0, width, height)
        }

        fun drawOes(texId: Int, ptsNs: Long) {
            draw(progOes, GLES11Ext.GL_TEXTURE_EXTERNAL_OES, texId, ptsNs)
        }

        fun draw2D(texId: Int, ptsNs: Long) {
            draw(prog2d, GLES20.GL_TEXTURE_2D, texId, ptsNs)
        }

        private fun draw(program: Int, target: Int, texId: Int, ptsNs: Long) {
            GLES20.glUseProgram(program)
            val aPos = GLES20.glGetAttribLocation(program, "aPos")
            val aTex = GLES20.glGetAttribLocation(program, "aTex")
            vbo.position(0)
            GLES20.glEnableVertexAttribArray(aPos)
            GLES20.glVertexAttribPointer(aPos, 2, GLES20.GL_FLOAT, false, 16, vbo)
            vbo.position(2)
            GLES20.glEnableVertexAttribArray(aTex)
            GLES20.glVertexAttribPointer(aTex, 2, GLES20.GL_FLOAT, false, 16, vbo)

            GLES20.glActiveTexture(GLES20.GL_TEXTURE0)
            GLES20.glBindTexture(target, texId)
            GLES20.glDrawArrays(GLES20.GL_TRIANGLE_STRIP, 0, 4)
            GLES20.glBindTexture(target, 0)

            EGLExt.eglPresentationTimeANDROID(display, eglSurface, ptsNs)
            EGL14.eglSwapBuffers(display, eglSurface)
        }

        fun release() {
            if (display != EGL14.EGL_NO_DISPLAY) {
                EGL14.eglMakeCurrent(display, EGL14.EGL_NO_SURFACE, EGL14.EGL_NO_SURFACE, EGL14.EGL_NO_CONTEXT)
                if (progOes != 0) GLES20.glDeleteProgram(progOes)
                if (prog2d != 0) GLES20.glDeleteProgram(prog2d)
                if (eglSurface != EGL14.EGL_NO_SURFACE) EGL14.eglDestroySurface(display, eglSurface)
                if (context != EGL14.EGL_NO_CONTEXT) EGL14.eglDestroyContext(display, context)
                EGL14.eglReleaseThread()
                EGL14.eglTerminate(display)
            }
            surface.release()
            display = EGL14.EGL_NO_DISPLAY
            context = EGL14.EGL_NO_CONTEXT
            eglSurface = EGL14.EGL_NO_SURFACE
        }

        private fun buildProgram(fsSource: String): Int {
            val vs = compileShader(GLES20.GL_VERTEX_SHADER, VS)
            val fs = compileShader(GLES20.GL_FRAGMENT_SHADER, fsSource)
            val prog = GLES20.glCreateProgram()
            GLES20.glAttachShader(prog, vs)
            GLES20.glAttachShader(prog, fs)
            GLES20.glLinkProgram(prog)
            GLES20.glDeleteShader(vs)
            GLES20.glDeleteShader(fs)
            return prog
        }

        private fun compileShader(type: Int, src: String): Int {
            val shader = GLES20.glCreateShader(type)
            GLES20.glShaderSource(shader, src)
            GLES20.glCompileShader(shader)
            return shader
        }

        private companion object {
            const val EGL_RECORDABLE_ANDROID = 0x3142
            const val VS = """
                attribute vec2 aPos;
                attribute vec2 aTex;
                varying vec2 vTex;
                void main() {
                    gl_Position = vec4(aPos, 0.0, 1.0);
                    vTex = aTex;
                }
            """
            const val FS_OES = """
                #extension GL_OES_EGL_image_external : require
                precision mediump float;
                varying vec2 vTex;
                uniform samplerExternalOES sTex;
                void main() {
                    gl_FragColor = texture2D(sTex, vTex);
                }
            """
            const val FS_2D = """
                precision mediump float;
                varying vec2 vTex;
                uniform sampler2D sTex;
                void main() {
                    gl_FragColor = texture2D(sTex, vTex);
                }
            """
        }
    }
}
