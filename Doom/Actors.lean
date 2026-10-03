import Doom.Things
import Doom.Random
import Doom.DeathData
import Doom.Imp

namespace Doom

inductive ActorMode where
  | idle | chase | attack | pain | dying
  deriving Inhabited, BEq, Repr

structure EnemySpec where
  health : Nat
  speed : Nat
  movePeriod : Nat
  attackTick : Nat
  attackLength : Nat
  melee : Bool
  pellets : Nat
  painChance : Nat
  corpse : Nat
  drop : Nat
  deriving Inhabited

/-- Initial combat roster; original stats, with a deliberately smaller AI below. -/
def enemySpec : Nat → Option EnemySpec
  | 3004 => some ⟨20, 8, 4, 10, 26, false, 1, 200, 18, 2007⟩
  | 9 => some ⟨30, 8, 3, 10, 30, false, 3, 170, 19, 2001⟩
  | 3002 => some ⟨150, 10, 2, 16, 24, true, 1, 180, 21, 0⟩
  | 3001 => some ⟨60, 8, 3, 16, 22, false, 0, 200, 20, 0⟩
  | 2035 => some ⟨20, 0, 1, 0, 0, false, 0, 0, 0, 0⟩
  | _ => none

structure Actor where
  thing : Nat
  kind : Nat
  health : Nat
  death : Option Death.Body := none
  imp : Option Imp.State := none
  /-- Barrel target is assigned by a surviving hit, before a later explosion. -/
  damageTarget : Option Nat := none
  mode : ActorMode := .idle
  age : Nat := 0
  cooldown : Nat := 35
  deriving Inhabited

/-- Pose/timing metadata from id Software's published info.c. -/
def actorPoses (kind : Nat) (mode : ActorMode) : Array ThingPose := match kind, mode with
  | 3001, .pain => #[⟨"TROOH", false, 2⟩, ⟨"TROOH", false, 2⟩]
  | 3004, .chase => #[⟨"POSSA", false, 4⟩, ⟨"POSSA", false, 4⟩, ⟨"POSSB", false, 4⟩, ⟨"POSSB", false, 4⟩, ⟨"POSSC", false, 4⟩, ⟨"POSSC", false, 4⟩, ⟨"POSSD", false, 4⟩, ⟨"POSSD", false, 4⟩]
  | 3004, .attack => #[⟨"POSSE", false, 10⟩, ⟨"POSSF", false, 8⟩, ⟨"POSSE", false, 8⟩]
  | 3004, .pain => #[⟨"POSSG", false, 3⟩, ⟨"POSSG", false, 3⟩]
  | 3004, .dying => #[⟨"POSSH", false, 5⟩, ⟨"POSSI", false, 5⟩, ⟨"POSSJ", false, 5⟩, ⟨"POSSK", false, 5⟩, ⟨"POSSL", false, 0⟩]
  | 9, .chase => #[⟨"SPOSA", false, 3⟩, ⟨"SPOSA", false, 3⟩, ⟨"SPOSB", false, 3⟩, ⟨"SPOSB", false, 3⟩, ⟨"SPOSC", false, 3⟩, ⟨"SPOSC", false, 3⟩, ⟨"SPOSD", false, 3⟩, ⟨"SPOSD", false, 3⟩]
  | 9, .attack => #[⟨"SPOSE", false, 10⟩, ⟨"SPOSF", true, 10⟩, ⟨"SPOSE", false, 10⟩]
  | 9, .pain => #[⟨"SPOSG", false, 3⟩, ⟨"SPOSG", false, 3⟩]
  | 9, .dying => #[⟨"SPOSH", false, 5⟩, ⟨"SPOSI", false, 5⟩, ⟨"SPOSJ", false, 5⟩, ⟨"SPOSK", false, 5⟩, ⟨"SPOSL", false, 0⟩]
  | 3002, .chase => #[⟨"SARGA", false, 2⟩, ⟨"SARGA", false, 2⟩, ⟨"SARGB", false, 2⟩, ⟨"SARGB", false, 2⟩, ⟨"SARGC", false, 2⟩, ⟨"SARGC", false, 2⟩, ⟨"SARGD", false, 2⟩, ⟨"SARGD", false, 2⟩]
  | 3002, .attack => #[⟨"SARGE", false, 8⟩, ⟨"SARGF", false, 8⟩, ⟨"SARGG", false, 8⟩]
  | 3002, .pain => #[⟨"SARGH", false, 2⟩, ⟨"SARGH", false, 2⟩]
  | 3002, .dying => #[⟨"SARGI", false, 8⟩, ⟨"SARGJ", false, 8⟩, ⟨"SARGK", false, 4⟩, ⟨"SARGL", false, 4⟩, ⟨"SARGM", false, 4⟩, ⟨"SARGN", false, 0⟩]
  | _, _ => thingPoses kind

def deathPoses (kind : Nat) : Array ThingPose := Id.run do
  let some info := Death.info kind | return #[]
  let some first := Death.frames.find? (·.id == info.normal) | return #[]
  return (Death.frames.filter (·.sprite == first.sprite)).map fun frame =>
    ⟨frame.sprite ++ String.singleton (Char.ofNat (65 + frame.frame % 32768)), frame.frame ≥ 32768, frame.tics.toInt.toNat⟩

def Actor.pose (a : Actor) : ThingPose := Id.run do
  if let some body := a.death then
    if let some frame := Death.frames.find? (·.id == body.state) then
      return ⟨frame.sprite ++ String.singleton (Char.ofNat (65 + frame.frame % 32768)), frame.frame ≥ 32768, frame.tics.toInt.toNat⟩
  if let some imp := a.imp then
    if let some frame := ImpData.frames.find? (·.id == imp.frame) then
      return ⟨frame.sprite ++ String.singleton (Char.ofNat (65 + frame.frame % 32768)), frame.frame ≥ 32768, frame.tics.toInt.toNat⟩
  let poses := actorPoses a.kind a.mode
  let duration := poses.foldl (fun n p => n + p.ticks) 0
  let mut age := if a.mode == .idle || a.mode == .chase then a.age % (max 1 duration) else a.age
  for pose in poses do
    if pose.ticks == 0 || age < pose.ticks then return pose
    age := age - pose.ticks
  return poses.back!

end Doom
