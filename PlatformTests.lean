import Doom.Platform
import Doom.Render

open Doom

private def mustFail (action : IO Unit) (label : String) : IO Unit := do
  let failed ← try action; pure false catch _ => pure true
  unless failed do throw (IO.userError s!"expected failure: {label}")

def main : IO Unit := do
  mustFail (Platform.openWindow 0 200) "invalid dimensions"
  mustFail (Platform.present emptyFrame) "present before initialization"
  mustFail (Platform.setTitle "closed") "title before initialization"
  mustFail Platform.openAudio "audio before platform initialization"
  mustFail (Platform.queueAudio ByteArray.empty) "queue before audio initialization"
  Platform.openWindow 320 200
  try
    mustFail (Platform.openWindow 320 200) "duplicate initialization"
    mustFail (Platform.present ByteArray.empty) "short framebuffer"
    mustFail (Platform.present (emptyFrame.push 0)) "oversized framebuffer"
    Platform.openAudio
    mustFail Platform.openAudio "duplicate audio initialization"
    mustFail (Platform.queueAudio (ByteArray.mk #[0])) "partial stereo frame"
    mustFail (Platform.queueAudio (ByteArray.mk (Array.replicate (44101*4) 0))) "oversized audio block"
    Platform.queueAudio (ByteArray.mk (Array.replicate 5040 0))
    let queued ← Platform.queuedAudio
    unless queued ≤ 5040 do throw (IO.userError "invalid queued sample count")
    Platform.clearAudio
    unless (← Platform.queuedAudio) == 0 do throw (IO.userError "audio queue did not clear")
    Platform.setTitle "Lean DOOM interaction test"
    let before ← Platform.seconds
    let _ ← Platform.poll
    Platform.present emptyFrame
    let after ← Platform.seconds
    unless after ≥ before do throw (IO.userError "clock moved backwards")
  finally
    Platform.closeWindow
  mustFail (Platform.present emptyFrame) "present after shutdown"
  mustFail (Platform.queueAudio ByteArray.empty) "audio after shutdown"
  Platform.openWindow 320 200
  Platform.openAudio
  Platform.closeWindow
  IO.println "SDL lifecycle, framebuffer, polling, clock and audio queue checks passed"
