import Doom.SpawnData
import Doom.Random
import Doom.Things

namespace Doom.MapSpawn

structure State where
  frame : Nat
  tics : Int32
  lastlook : Nat
  deriving Inhabited

/-- P_SpawnMobj consumes lastlook even for stationary objects. P_SpawnMapThing
then randomizes positive state durations; P_SpawnPlayer skips that second draw.
The supported profile is single-player, Hurt Me Plenty, ordinary map things. -/
def thing (t : Thing) (rng : DoomRandom) : Except String (Option State × DoomRandom) := do
  if t.kind != 1 && (t.kind ≤ 4 || t.kind == 11 || !t.active) then return (none,rng)
  let some (frame,duration) := info t.kind | throw s!"spawn: unknown map thing {t.kind}"
  let (look,rng) := rng.nextPlay
  let (tics,rng) := if t.kind != 1 && duration > 0 then
      let (roll,next) := rng.nextPlay
      (Int32.ofNat (1+roll%duration.toInt.toNat),next)
    else (duration,rng)
  return (some { frame, tics, lastlook := look%4 },rng)

end Doom.MapSpawn
