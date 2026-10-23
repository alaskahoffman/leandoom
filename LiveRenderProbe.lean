import Doom.App
import Doom.Interaction
open Doom

/-- IO only supplies inputs and presents outputs. All game computation and
retained state live in the shared Engine/HITree model. -/
private partial def serve (ctx : Engine.Context) (tree : Interaction.Tree)
    (input output : IO.FS.Stream)
    (writeHeap : Nat → Array DosHeap.Event → IO Unit) : IO Unit := do
  match tree with
  | .unreachable => throw (IO.userError "invalid interaction effect response")
  | .pure (.fault message) => throw (IO.userError message)
  | .pure (.exited _) =>
    -- Retain the old pipe protocol: EOF closes cleanly; another valid command
    -- after exit receives the existing error. This is transport, not a game tic.
    let line ← input.getLine
    if line.isEmpty then return
    let _ ← checked (Engine.parseCommand line)
    throw (IO.userError "E1M1 exit reached; restart comparison")
  | .impure .input k =>
    let line ← input.getLine
    if line.isEmpty then return
    let cmd ← checked (Engine.parseCommand line)
    serve ctx (k (.command cmd)) input output writeHeap
  | .impure (.present frame) k =>
    writeHeap frame.tic frame.heapEvents
    output.putStr (frame.record.compress ++ "\n")
    output.write frame.rgb
    output.flush
    serve ctx (k .acknowledged) input output writeHeap
  | .impure (.again state events) _ =>
    writeHeap state.game.ticks events
    serve ctx (Interaction.program ctx state) input output writeHeap

/-- Persistent comparison worker. One exact ticcmd in, one state and RGB frame
out. Uses the same HITree whose finite replay interpretation is proved in
Doom.Proofs.Interaction; the OS pipe/IO implementation is not formally verified. -/
def main (args : List String) : IO UInt32 := do
  try
    let (wadPath, dosPresentation) ← match args with
      | [wad] => pure (wad, false)
      | [wad, "--dos-presentation"] => pure (wad, true)
      | _ => throw (IO.userError "live-render-probe WAD [--dos-presentation]")
    let lumps := (← checked (Wad.parse (← IO.FS.readBinFile wadPath))).lumps
    let tracePath ← IO.getEnv "LEANDOOM_HEAP_TRACE"
    let trace ← tracePath.mapM (fun path => IO.FS.Handle.mk path .write)
    let writeHeap := fun (tic : Nat) (events : Array DosHeap.Event) => do
      if let some trace := trace then
        for e in events do
          trace.putStrLn s!"{tic} {e.op} {e.size} {e.tag.toInt} {e.owner} {e.address}"
        trace.flush
    let (ctx, state, startupEvents) ← checked (Engine.start lumps dosPresentation trace.isSome)
    writeHeap 0 startupEvents
    serve ctx (Interaction.program ctx state) (← IO.getStdin) (← IO.getStdout) writeHeap
    return 0
  catch e =>
    (← IO.getStderr).putStrLn s!"live renderer: {e}"
    return 1
