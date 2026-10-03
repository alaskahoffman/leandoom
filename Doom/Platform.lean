namespace Doom.Platform

-- IO's world token is erased in Lean 4.33's C ABI.
@[extern "doom_window_open"] opaque openWindow : UInt32 → UInt32 → IO Unit
@[extern "doom_window_title"] opaque setTitle : @& String → IO Unit
@[extern "doom_window_close"] opaque closeWindow : IO Unit
@[extern "doom_window_poll"] opaque poll : IO UInt32
@[extern "doom_window_present"] opaque present : @& ByteArray → IO Unit
@[extern "doom_window_seconds"] opaque seconds : IO Float

@[extern "doom_audio_open"] opaque openAudio : IO Unit
@[extern "doom_audio_queue"] opaque queueAudio : @& ByteArray → IO Unit
@[extern "doom_audio_clear"] opaque clearAudio : IO Unit
@[extern "doom_audio_queued"] opaque queuedAudio : IO UInt32

end Doom.Platform
