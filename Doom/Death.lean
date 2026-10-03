/-
P_KillMobj and death-state actions, Chocolate Doom 3.1.1,
commit 410d96855b5df5410ff591a90efeafa889119224.
Derived from id Software (1993-1996), Simon Howard (2005-2014).
SPDX-License-Identifier: GPL-2.0-or-later. See COPYING.md.
-/
import Doom.Fixed
import Doom.Random

namespace Doom.Death

structure Frame where
  id : Nat
  label : String
  sprite : String
  frame : Nat
  tics : Int32
  next : Nat
  action : String
  deriving Inhabited

structure Info where
  spawnHealth : Int32
  normal : Nat
  extreme : Nat
  sound : String
  flags : UInt32
  deriving Inhabited

structure Body where
  kind : Nat := 0
  player : Option (Fin 4) := none
  health : Int32 := 0
  flags : UInt32 := 0
  height : Fixed := Fixed.ofInt 56
  info : Info := default
  state : Nat := 0
  tics : Int32 := 0
  removed : Bool := false
  deriving Inhabited

structure Stats where
  kills : Int32 := 0
  frags : Vector Int32 4 := #v[0,0,0,0]
  dead : Bool := false
  deriving Inhabited

inductive Event where
  | dropWeapon (player : Nat)
  | stopAutomap
  | state (id : Nat)
  | sound (name : String) (global : Bool := false)
  | drop (editor : Nat)
  | remove
  | explode
  deriving Repr

structure World where
  players : Vector Stats 4 := Vector.replicate 4 {}
  /-- None is environmental; some none is a nonplayer source. -/
  source : Option (Option (Fin 4)) := none
  netgame : Bool := false
  console : Fin 4 := 0
  automap : Bool := false
  commercial : Bool := false
  chex : Bool := false
  rng : DoomRandom := {}
  events : Array Event := #[]
  deriving Inhabited

private def action (body : Body) (world : World) (name : String) : Except String (Body × World) := do
  let mut world := world
  match name with
  | "NULL" => return (body,world)
  | "A_Explode" => return (body,{ world with events := world.events.push .explode })
  | "A_Fall" => return ({ body with flags := body.flags &&& ~~~(2 : UInt32) },world)
  | "A_XScream" => return (body,{ world with events := world.events.push (.sound "slop") })
  | "A_PlayerScream" =>
    return (body,{ world with events := world.events.push (.sound (if world.commercial && body.health < -50 then "pdiehi" else "pldeth")) })
  | "A_Scream" =>
    let mut sound := body.info.sound
    if sound == "None" then return (body,world)
    if #["podth1","podth2","podth3"].contains sound then
      let (roll,rng) := world.rng.nextPlay
      world := { world with rng }; sound := s!"podth{roll%3+1}"
    else if #["bgdth1","bgdth2"].contains sound then
      let (roll,rng) := world.rng.nextPlay
      world := { world with rng }; sound := s!"bgdth{roll%2+1}"
    return (body,{ world with events := world.events.push (.sound sound (body.kind == 7 || body.kind == 16)) })
  | _ => throw s!"death: unsupported state action {name}"

/-- P_SetMobjState for the supplied death table, including entry actions and
zero-tic chains. The million-iteration historical cycle guard is retained. -/
def setState (frames : Array Frame) (body : Body) (world : World) (id : Nat)
    : Except String (Body × World) := do
  let mut body := body
  let mut world := world
  let mut id := id
  for counter in [:1000002] do
    if id == 0 then
      return ({ body with state := 0, removed := true },{ world with events := world.events.push .remove })
    let some frame := frames.find? (·.id == id) | throw s!"death: missing state {id}"
    body := { body with state := id, tics := frame.tics }
    world := { world with events := world.events.push (.state id) }
    (body,world) ← action body world frame.action
    id := frame.next
    if counter > 1000000 then throw "death: infinite state cycle"
    if body.tics != 0 then return (body,world)
  throw "death: infinite state cycle"

/-- Original P_KillMobj. Damage has already made health nonpositive; the caller
owns that gate. State entry effects precede the timing draw, then item spawning.
Drop/weapon/automap effects are explicit requests. -/
def kill (frames : Array Frame) (body : Body) (world : World) : Except String (Body × World) := do
  let mut body := { body with flags := body.flags &&& ~~~(4 ||| 0x4000 ||| 0x1000000 : UInt32) }
  if body.kind != 3006 then body := { body with flags := body.flags &&& ~~~(0x200 : UInt32) }
  body := { body with flags := body.flags ||| 0x100000 ||| 0x400, height := ⟨body.height.raw >>> 2⟩ }
  let mut world := world
  if let some (some source) := world.source then
    let mut player := world.players[source]
    if body.flags &&& (0x400000 : UInt32) != 0 then player := { player with kills := player.kills+1 }
    if let some victim := body.player then player := { player with frags := player.frags.set victim (player.frags[victim]+1) }
    world := { world with players := world.players.set source player }
  else if !world.netgame && body.flags &&& (0x400000 : UInt32) != 0 then
    let player := world.players[0]
    world := { world with players := world.players.set 0 { player with kills := player.kills+1 } }
  if let some victim := body.player then
    let mut player := world.players[victim]
    if world.source.isNone then player := { player with frags := player.frags.set victim (player.frags[victim]+1) }
    player := { player with dead := true }
    body := { body with flags := body.flags &&& ~~~(2 : UInt32) }
    world := { world with players := world.players.set victim player, events := world.events.push (.dropWeapon victim.val) }
    if victim == world.console && world.automap then
      world := { world with automap := false, events := world.events.push .stopAutomap }
  let state := if body.health < -body.info.spawnHealth && body.info.extreme != 0 then body.info.extreme else body.info.normal
  (body,world) ← setState frames body world state
  let (roll,rng) := world.rng.nextPlay
  body := { body with tics := max 1 (body.tics - Int32.ofNat (roll &&& 3)) }
  world := { world with rng }
  if world.chex then return (body,world)
  let item := match body.kind with | 84 | 3004 => 2007 | 9 => 2001 | 65 => 2002 | _ => 0
  if item != 0 then world := { world with events := world.events.push (.drop item) }
  return (body,world)

/-- Original finite-state countdown branch of P_MobjThinker. Movement, nightmare
respawn and general thinker interleaving are separate stages. -/
def tick (frames : Array Frame) (body : Body) (world : World) : Except String (Body × World) := do
  if body.removed || body.tics == -1 then return (body,world)
  let body := { body with tics := body.tics-1 }
  if body.tics != 0 then return (body,world)
  let some frame := frames.find? (·.id == body.state) | throw "death: missing current state"
  setState frames body world frame.next

end Doom.Death
