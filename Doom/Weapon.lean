/- Fist/pistol/shotgun psprite actions from Chocolate Doom 3.1.1 p_pspr.c.
Copyright 1993-1996 id Software; 2005-2014 Simon Howard. GPL-2.0-or-later.
Adapted to explicit Lean state on 2026-10-03. See COPYING.md.
The adapter still starts at ready; full player spawn/thinker ordering is separate. -/
import Doom.Fire
import Doom.Pickup
import Doom.Angles
namespace Doom.Weapon
open WeaponData
structure Sprite where
  frame : Nat := PISTOL
  tics : Int32 := 1
  x : Fixed := ⟨0⟩
  y : Fixed := Fixed.ofInt 32
  deriving Inhabited
structure State where
  weapon : Sprite := {}
  flash : Sprite := { frame := 0, tics := 0, y := ⟨0⟩ }
  refire : Int32 := 0
  attackDown : Bool := true
  extraLight : Int32 := 0
  deriving Inhabited
inductive Event where
  | pistol (accurate : Bool) | shotgun | punch | noise
  deriving Repr, BEq
structure Context where
  state : State := {}
  player : Pickup.State := {}
  attack : Bool := false
  dead : Bool := false
  bob : Fixed := ⟨0⟩
  time : Int32 := 0
  events : Array Event := #[]
  deriving Inhabited

def supported (w : Nat) : Bool := w ≤ 2
def ready (w : Nat) : Nat := if w == 0 then PUNCH else if w == 2 then SGUN else PISTOL
def down (w : Nat) : Nat := ready w + 1
def up (w : Nat) : Nat := ready w + 2
def attackState (w : Nat) : Nat := ready w + 3

/-- Original owned-weapon gate; selection is allowed even with no ammunition.
Unsupported pending pickups remain available for future weapon implementations. -/
def Context.select (c : Context) (choice : Option Nat) : Context :=
  match choice with
  | some w => if h : w < 9 then
      if supported w && c.player.weapons[w] && c.player.readyWeapon.val != w then
        { c with player := { c.player with pendingWeapon := ⟨w,by omega⟩ } }
      else c
    else c
  | none => c

private def Context.pending (c : Context) : Bool := supported c.player.pendingWeapon.val

mutual
private partial def enter (c : Context) (id : Nat) : Context := Id.run do
  let mut c := { c with state := { c.state with weapon := { c.state.weapon with frame := id } } }
  if id == 0 then return c
  let f := frames[id]!
  c := { c with state := { c.state with weapon := { c.state.weapon with tics := f.tics } } }
  let w := c.player.readyWeapon.val
  match f.action with
  | "A_WeaponReady" =>
    if c.pending || c.player.health == 0 then return enter c (down w)
    if c.attack then return fire { c with state := { c.state with attackDown := true } }
    let angle : Angle := ⟨((c.time*128).toUInt32 &&& 8191) <<< 19⟩
    let half : Angle := ⟨((c.time*128).toUInt32 &&& 4095) <<< 19⟩
    c := { c with state := { c.state with attackDown := false, weapon := { c.state.weapon with
      x := Fixed.ofInt 1 + c.bob*angle.fineCosine,
      y := Fixed.ofInt 32 + c.bob*half.fineSine } } }
  | "A_Lower" =>
    let y := c.state.weapon.y + Fixed.ofInt 6
    c := { c with state := { c.state with weapon := { c.state.weapon with y } } }
    if y.raw < 128*65536 then return c
    if c.dead then return { c with state := { c.state with weapon := { c.state.weapon with y := Fixed.ofInt 128 } } }
    if c.player.health == 0 then return enter c 0
    let w := c.player.pendingWeapon.val
    if h : w < 9 then
      c := { c with player := { c.player with readyWeapon := ⟨w,h⟩, pendingWeapon := 9 }, state := { c.state with weapon := { c.state.weapon with y := Fixed.ofInt 128 } } }
      return enter c (up w)
  | "A_Raise" =>
    let y := c.state.weapon.y - Fixed.ofInt 6
    c := { c with state := { c.state with weapon := { c.state.weapon with y } } }
    if y.raw > 32*65536 then return c
    return enter { c with state := { c.state with weapon := { c.state.weapon with y := Fixed.ofInt 32 } } } (ready w)
  | "A_ReFire" =>
    if c.attack && !c.pending && c.player.health != 0 then
      return fire { c with state := { c.state with refire := c.state.refire+1 } }
    c := (checkAmmo { c with state := { c.state with refire := 0 } }).2
  | "A_FirePistol" | "A_FireShotgun" =>
    let shotgun := f.action == "A_FireShotgun"
    let gun : Fire.Gun := if shotgun then .shotgun else .pistol
    let ammo := gun.ammoIndex.val
    let discharge := Fire.discharge gun c.player.ammo[ammo]!
    let flash := if shotgun then SGUNFLASH1 else PISTOLFLASH
    c := { c with player := { c.player with ammo := c.player.ammo.set! ammo discharge.ammoAfter }, state := { c.state with flash := { c.state.flash with frame := flash, tics := frames[flash]!.tics }, extraLight := 1 }, events := c.events.push (if shotgun then .shotgun else .pistol (c.state.refire == 0)) }
  | "A_Punch" => c := { c with events := c.events.push .punch }
  | _ => pure ()
  if c.state.weapon.tics == 0 then return enter c frames[c.state.weapon.frame]!.next
  return c

private partial def checkAmmo (c : Context) : Bool × Context :=
  let w := c.player.readyWeapon.val
  if w == 0 || c.player.ammo[if w == 2 then 1 else 0]! > 0 then (true,c)
  else
    let pending : Fin 10 := if c.player.weapons[2] && c.player.ammo[1] > 0 then 2
      else if c.player.ammo[0] > 0 then 1 else 0
    (false,enter { c with player := { c.player with pendingWeapon := pending } } (down w))

private partial def fire (c : Context) : Context :=
  let (allowed,c) := checkAmmo c
  if !allowed then c else
    let c := enter c (attackState c.player.readyWeapon.val)
    { c with events := c.events.push .noise }
end

/-- Original weapon-first, flash-second countdown. A newly created muzzle flash
loses its first tic in the same P_MovePsprites call. -/
def tick (c : Context) : Context := Id.run do
  let mut c := { c with events := #[] }
  if c.state.weapon.frame != 0 && c.state.weapon.tics != -1 then
    c := { c with state := { c.state with weapon := { c.state.weapon with tics := c.state.weapon.tics-1 } } }
    if c.state.weapon.tics == 0 then c := enter c frames[c.state.weapon.frame]!.next
  if c.state.flash.frame != 0 && c.state.flash.tics != -1 then
    let mut flash := { c.state.flash with tics := c.state.flash.tics-1 }
    let mut light := c.state.extraLight
    if flash.tics == 0 then
      let next := frames[flash.frame]!.next
      if next == LIGHTDONE then flash := { flash with frame := 0 }; light := 0
      else flash := { flash with frame := next, tics := frames[next]!.tics }; light := 2
    c := { c with state := { c.state with flash, extraLight := light } }
  return { c with state := { c.state with flash := { c.state.flash with x := c.state.weapon.x, y := c.state.weapon.y } } }

def drop (c : Context) : Context := enter c (down c.player.readyWeapon.val)

def label (s : Sprite) : Option String := do
  if s.frame == 0 then none else
    let f ← frames[s.frame]?
    return f.sprite ++ String.singleton (Char.ofNat (65+f.frame%32768)) ++ "0"

end Doom.Weapon
