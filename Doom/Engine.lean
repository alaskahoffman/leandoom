import Doom.CombatView
import Doom.Trace
import Doom.Wipe
import Doom.DosStartup
import Doom.DosVideo

namespace Doom.Engine

/-- Immutable inputs to the one-render-per-tic comparison profile. -/
structure Context where
  assets : Assets
  dosPresentation : Bool

/-- All state retained by the comparison worker, including state which rendering
changes. Keeping just Simulation would lose the heap, HUD and VGA history. -/
structure State where
  game : Simulation
  phase : Fuzz.Phase := 0
  previous : Option IndexedFrame := none
  videoPages : DosVideo.Pages := {}

/-- Diagnostic snapshot plus the exact RGB presentation. Heap events are
output-only diagnostics; they do not supply any state to the engine. -/
structure Presentation where
  record : Lean.Json
  rgb : ByteArray
  tic : Nat
  heapEvents : Array DosHeap.Event

/-- State after drawing but before post-presentation effects. -/
structure Drawn where
  presentation : Presentation
  pending : State

/-- Setup is pure once the WAD bytes have been read. -/
def start (lumps : Array Lump) (dosPresentation tracing : Bool)
    : Except String (Context × State × Array DosHeap.Event) := do
  let map ← Map.load lumps "E1M1"
  let assets ← Assets.load lumps map true true
  let game ← Simulation.spawn map true (LevelSpecials.switchEpisode lumps)
  let mut state : State := { game }
  let mut events := #[]
  if dosPresentation then
    let heap ← DosHeap.startup assets.art game {} tracing
    events := heap.events
    state := { state with previous := some { dosHeap := some { heap with events := #[] } } }
  return (⟨assets, dosPresentation⟩, state, events)

/-- Preserve the live worker's vanilla-demo input validation. The DOS adapter
additionally excludes special pause/save commands (buttons >= 128). -/
def parseCommand (line : String) : Except String Ticcmd := do
  let parts := line.trimAscii.toString.splitOn " "
  let [f,s,a,b] ← parts.mapM (fun v => match v.toInt? with
    | some n => Except.ok n
    | none => Except.error "invalid command integer")
    | throw "expected four command fields"
  if f < -127 || f > 127 || s < -128 || s > 127 || a < -32768 || a > 32512 || a % 256 != 0 || b < 0 || b > 255 then
    throw "command outside vanilla demo encoding"
  return ⟨Int8.ofInt f, Int8.ofInt s, Int16.ofInt a, UInt8.ofInt b⟩

/-- Execute the real update and renderer, with no IO and no reference-engine
inputs. The frame is exposed before opening-wipe effects, as in DOS D_Display. -/
def advance (ctx : Context) (state : State) (cmd : Ticcmd) : Except String Drawn := do
  if state.game.exitRequested then throw "E1M1 exit reached; restart comparison"
  let game := { state.game with dosHeap := state.previous.bind (·.dosHeap) }
  let game ← game.tickCommand cmd
  if ctx.dosPresentation && game.dosHeap.isNone then
    throw "DOS heap lifecycle lost; in-game level reload is not yet modeled"
  let previous := state.previous.map fun p => { p with dosHeap := game.dosHeap }
  let game := { game with dosHeap := none }
  let record ← Trace.record game game.ticks (some cmd)
  let drawing := if ctx.dosPresentation then
      previous.map fun p => { p with indices := state.videoPages.restore p.indices }
    else previous
  let frame ← game.drawIndexedFrame ctx.assets none state.phase drawing
  let videoPages := if ctx.dosPresentation then state.videoPages.present frame.indices
    else state.videoPages
  let heapEvents := (frame.dosHeap.map (·.events)).getD #[]
  let frame := { frame with dosHeap := frame.dosHeap.map fun h => { h with events := #[] } }
  return {
    presentation := { record, rgb := frame.rgb, tic := game.ticks, heapEvents }
    pending := { game, phase := frame.phase, previous := some frame, videoPages } }

/-- These effects happen AFTER presenting the first frame, BEFORE requesting
another input. An error here must not erase the frame already presented. -/
def afterPresent (ctx : Context) (state : State)
    : Except String (State × Array DosHeap.Event) := do
  let mut state := state
  let mut events := #[]
  if ctx.dosPresentation && state.game.ticks == 1 then
    if let some frame := state.previous then
      state := { state with videoPages := DosVideo.afterMelt frame.indices }
    state := { state with game := { state.game with
      rng := (Wipe.initialDelays frameWidth state.game.rng).2 } }
    if let some heap := state.previous.bind (·.dosHeap) then
      let (_,heap) ← DosHeap.openingWipe.run heap
      events := heap.events
      state := { state with previous := state.previous.map fun p =>
        { p with dosHeap := some { heap with events := #[] } } }
  return (state, events)

end Doom.Engine
