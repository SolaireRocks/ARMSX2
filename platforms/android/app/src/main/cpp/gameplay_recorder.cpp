// SPDX-FileCopyrightText: 2026 ARMSX2 Contributors
// SPDX-License-Identifier: GPL-3.0+

// Gameplay recorder & instant-replay core bridge: pulls GPU-captured frames (GSRemotePlay) and
// raw SPU2 mixed 48 kHz stereo audio (before output volume, mute, or time-stretching), both
// stamped on the emulated SPU2 audio clock so recordings and clips always play at 1x normal speed
// and normal game volume regardless of fast-forward or mute state.

#include <jni.h>
#include <android/log.h>

#include "common/Pcsx2Defs.h"
#include "pcsx2/GS/GSRemotePlay.h"
#include "pcsx2/VMManager.h"

#include <algorithm>
#include <atomic>
#include <chrono>
#include <cstring>
#include <mutex>
#include <thread>

#define REC_LOG(...) __android_log_print(ANDROID_LOG_INFO, "GameplayRec", __VA_ARGS__)

namespace
{
	std::atomic<bool> s_running{false};
	u64 s_gpu_delay_us = 8000;

	std::mutex s_audio_poll_mutex;
	u64 s_rec_audio_base = 0;
	u64 s_audio_read = 0;

	u64 SteadyNs()
	{
		return static_cast<u64>(std::chrono::duration_cast<std::chrono::nanoseconds>(
			std::chrono::steady_clock::now().time_since_epoch()).count());
	}

	// Takes the oldest finished frame so recorded video preserves chronological frame order.
	// Returns 2 for a hardware AHardwareBuffer slot (held until recReleaseFrame), 1 for an RGBA
	// readback written to dst, 0 when none is finished yet, -2 when dst cap is too small.
	int TakeOldestFrame(u8* dst, size_t cap, jlong* info, u64& pending_since)
	{
		std::lock_guard lock(GSRemotePlay::g_mutex);

		pending_since = 0;
		GSRemotePlay::Ring* const ring = GSRemotePlay::g_ring;
		if (!ring || (!ring->markers && !ring->is_done))
			return 0;

		GSRemotePlay::Slot* oldest = nullptr;
		u32 oldest_index = 0;
		for (u32 i = 0; i < ring->slots.size(); i++)
		{
			GSRemotePlay::Slot& slot = ring->slots[i];
			if (slot.state.load(std::memory_order_acquire) != GSRemotePlay::SlotRecorded)
				continue;

			const bool done = ring->markers ? ring->markers[i] == slot.seq : ring->is_done(ring->context, i);
			if (!done)
			{
				if (!pending_since || slot.recorded_ns < pending_since)
					pending_since = slot.recorded_ns;
				continue;
			}

			if (!oldest || static_cast<s32>(slot.seq - oldest->seq) < 0)
			{
				oldest = &slot;
				oldest_index = i;
			}
		}

		if (!oldest)
			return 0;

		std::atomic_thread_fence(std::memory_order_acquire);

		const u64 now = SteadyNs();
		if (now > oldest->recorded_ns)
		{
			const u64 took_us = std::min<u64>((now - oldest->recorded_ns) / 1000, 100'000);
			s_gpu_delay_us = (s_gpu_delay_us * 7 + took_us) / 8;
		}

		const u64 audio_frames = oldest->emulated_audio_frames >= s_rec_audio_base
			? (oldest->emulated_audio_frames - s_rec_audio_base)
			: 0;
		const u64 pts_us = (audio_frames * 1'000'000ULL) / GSRemotePlay::AUDIO_SAMPLE_RATE;

		info[0] = static_cast<jlong>(oldest->width);
		info[1] = static_cast<jlong>(oldest->height);
		info[4] = static_cast<jlong>(oldest->seq);
		info[5] = static_cast<jlong>(pts_us);

		if (oldest->hardware)
		{
			info[2] = static_cast<jlong>(oldest_index);
			info[3] = static_cast<jlong>(oldest->generation);
			oldest->state.store(GSRemotePlay::SlotHeld, std::memory_order_release);
			return 2;
		}

		info[2] = -1;
		info[3] = 0;

		const size_t size = static_cast<size_t>(oldest->width) * oldest->height * 4;
		int result = -2;
		if (cap >= size && oldest->data)
		{
			if (ring->prepare_read)
				ring->prepare_read(ring->context, oldest_index);
			std::memcpy(dst, oldest->data, size);
			result = 1;
		}

		oldest->state.store(GSRemotePlay::SlotFree, std::memory_order_release);
		return result;
	}
} // namespace

extern "C" JNIEXPORT jboolean JNICALL
Java_kr_co_iefriends_pcsx2_NativeApp_recStart(JNIEnv*, jclass, jint maxWidth, jint maxHeight, jboolean useHardware)
{
	if (!VMManager::HasValidVM())
	{
		REC_LOG("recStart: no game running");
		return JNI_FALSE;
	}
	if (!GSRemotePlay::g_renderer_captures.load(std::memory_order_acquire))
	{
		REC_LOG("recStart: renderer cannot capture frames");
		return JNI_FALSE;
	}
	if (!s_running.load(std::memory_order_acquire) && GSRemotePlay::g_max_size.load(std::memory_order_acquire) != 0)
	{
		REC_LOG("recStart: capture already in use by Remote Play");
		return JNI_FALSE;
	}

	{
		std::lock_guard lock(s_audio_poll_mutex);
		s_rec_audio_base = GSRemotePlay::g_rec_audio_written.load(std::memory_order_acquire);
		s_audio_read = s_rec_audio_base;
	}

	GSRemotePlay::g_rec_audio_on.store(true, std::memory_order_release);
	GSRemotePlay::g_hardware.store(useHardware == JNI_TRUE, std::memory_order_release);
	GSRemotePlay::g_max_size.store(
		(static_cast<u32>(std::clamp(maxWidth, 16, 4096)) << 16) |
		static_cast<u32>(std::clamp(maxHeight, 16, 4096)),
		std::memory_order_release);
	s_running.store(true, std::memory_order_release);
	REC_LOG("recStart: started up to %dx%d (hw=%d)", maxWidth, maxHeight, useHardware == JNI_TRUE ? 1 : 0);
	return JNI_TRUE;
}

extern "C" JNIEXPORT void JNICALL
Java_kr_co_iefriends_pcsx2_NativeApp_recStop(JNIEnv*, jclass)
{
	const bool was_running = s_running.exchange(false, std::memory_order_acq_rel);
	if (!was_running)
		return;

	GSRemotePlay::g_max_size.store(0, std::memory_order_release);
	GSRemotePlay::g_rec_audio_on.store(false, std::memory_order_release);

	GSRemotePlay::NotifyRecorded();
	{
		std::lock_guard lock(GSRemotePlay::g_rec_audio_mutex);
		GSRemotePlay::g_rec_audio_cv.notify_all();
	}
	REC_LOG("recStop: stopped");
}

extern "C" JNIEXPORT jint JNICALL
Java_kr_co_iefriends_pcsx2_NativeApp_recPollVideo(JNIEnv* env, jclass, jobject buffer, jlongArray info, jint timeoutMs)
{
	if (!s_running.load(std::memory_order_acquire) || !buffer || !info || env->GetArrayLength(info) < 6)
		return -1;

	u8* const dst = static_cast<u8*>(env->GetDirectBufferAddress(buffer));
	const jlong cap = env->GetDirectBufferCapacity(buffer);
	if (!dst || cap <= 0)
		return -1;

	jlong out[6] = {};
	int result = 0;
	const auto deadline = std::chrono::steady_clock::now() + std::chrono::milliseconds(std::max(timeoutMs, 0));

	while (true)
	{
		u32 recorded;
		{
			std::lock_guard lock(GSRemotePlay::g_recorded_mutex);
			recorded = GSRemotePlay::g_recorded;
		}

		u64 pending_since = 0;
		result = TakeOldestFrame(dst, static_cast<size_t>(cap), out, pending_since);
		if (result != 0)
			break;

		if (!s_running.load(std::memory_order_acquire))
		{
			result = -1;
			break;
		}

		const auto now = std::chrono::steady_clock::now();
		if (now >= deadline)
			break;

		if (pending_since)
		{
			const u64 waited_us = (SteadyNs() - pending_since) / 1000;
			const u64 sleep_us = waited_us + 1500 < s_gpu_delay_us ? s_gpu_delay_us - waited_us - 1000 : 1000;
			const u64 left_us = static_cast<u64>(std::chrono::duration_cast<std::chrono::microseconds>(deadline - now).count());
			std::this_thread::sleep_for(std::chrono::microseconds(std::min<u64>({sleep_us, left_us, 20'000})));
		}
		else
		{
			std::unique_lock lock(GSRemotePlay::g_recorded_mutex);
			GSRemotePlay::g_recorded_cv.wait_until(lock, deadline, [recorded] {
				return GSRemotePlay::g_recorded != recorded || !s_running.load(std::memory_order_acquire);
			});
		}
	}

	env->SetLongArrayRegion(info, 0, 6, out);
	return result;
}

extern "C" JNIEXPORT void JNICALL
Java_kr_co_iefriends_pcsx2_NativeApp_recReleaseFrame(JNIEnv*, jclass, jint slot, jint seq)
{
	std::lock_guard lock(GSRemotePlay::g_mutex);
	GSRemotePlay::Ring* const ring = GSRemotePlay::g_ring;
	if (!ring || slot < 0 || static_cast<u32>(slot) >= ring->slots.size() ||
		ring->slots[slot].seq != static_cast<u32>(seq))
	{
		return;
	}

	u32 held = GSRemotePlay::SlotHeld;
	ring->slots[slot].state.compare_exchange_strong(held, GSRemotePlay::SlotFree, std::memory_order_acq_rel);
}

extern "C" JNIEXPORT void JNICALL
Java_kr_co_iefriends_pcsx2_NativeApp_recSetHardware(JNIEnv*, jclass, jboolean enabled)
{
	GSRemotePlay::g_hardware.store(enabled == JNI_TRUE, std::memory_order_release);
}

extern "C" JNIEXPORT jint JNICALL
Java_kr_co_iefriends_pcsx2_NativeApp_recPollAudio(JNIEnv* env, jclass, jobject buffer, jint capFrames, jint timeoutMs, jlongArray outPtsUs)
{
	if (!s_running.load(std::memory_order_acquire) || !buffer || capFrames <= 0)
		return -1;

	s16* const dst = static_cast<s16*>(env->GetDirectBufferAddress(buffer));
	const jlong cap = env->GetDirectBufferCapacity(buffer);
	if (!dst || cap < 4)
		return -1;

	const u32 want = static_cast<u32>(std::min<jlong>(capFrames, cap / 4));
	const auto deadline = std::chrono::steady_clock::now() + std::chrono::milliseconds(std::max(timeoutMs, 0));

	std::lock_guard poll(s_audio_poll_mutex);
	u64 available = 0;
	while (true)
	{
		const u64 written = GSRemotePlay::g_rec_audio_written.load(std::memory_order_acquire);
		available = written >= s_audio_read ? (written - s_audio_read) : 0;

		if (available > GSRemotePlay::REC_AUDIO_RING_FRAMES / 2)
		{
			s_audio_read = written - want;
			available = want;
		}

		if (available >= want)
			break;
		if (!s_running.load(std::memory_order_acquire))
			return -1;
		if (std::chrono::steady_clock::now() >= deadline)
			break;

		std::unique_lock lock(GSRemotePlay::g_rec_audio_mutex);
		const u64 target = s_audio_read + want;
		GSRemotePlay::g_rec_audio_target.store(target, std::memory_order_relaxed);
		GSRemotePlay::g_rec_audio_waiting.store(true, std::memory_order_seq_cst);
		if (GSRemotePlay::g_rec_audio_written.load(std::memory_order_seq_cst) < target &&
			s_running.load(std::memory_order_acquire))
		{
			GSRemotePlay::g_rec_audio_cv.wait_until(lock, deadline);
		}
		GSRemotePlay::g_rec_audio_waiting.store(false, std::memory_order_relaxed);
	}

	const u32 frames = static_cast<u32>(std::min<u64>(available, want));
	if (outPtsUs && env->GetArrayLength(outPtsUs) >= 1)
	{
		const u64 rel_frames = s_audio_read >= s_rec_audio_base ? (s_audio_read - s_rec_audio_base) : 0;
		const jlong pts_us = static_cast<jlong>((rel_frames * 1'000'000ULL) / GSRemotePlay::AUDIO_SAMPLE_RATE);
		env->SetLongArrayRegion(outPtsUs, 0, 1, &pts_us);
	}

	for (u32 i = 0; i < frames; i++)
	{
		const u32 at = static_cast<u32>((s_audio_read + i) & (GSRemotePlay::REC_AUDIO_RING_FRAMES - 1)) * 2;
		dst[i * 2] = GSRemotePlay::g_rec_audio_ring[at];
		dst[i * 2 + 1] = GSRemotePlay::g_rec_audio_ring[at + 1];
	}
	s_audio_read += frames;
	return static_cast<jint>(frames);
}

extern "C" JNIEXPORT jboolean JNICALL
Java_kr_co_iefriends_pcsx2_NativeApp_recIsPaused(JNIEnv*, jclass)
{
	return VMManager::GetState() == VMState::Paused ? JNI_TRUE : JNI_FALSE;
}
