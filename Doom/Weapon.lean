/- Fist/pistol/shotgun psprite actions from Chocolate Doom 3.1.1 p_pspr.c.
Copyright 1993-1996 id Software; 2005-2014 Simon Howard. GPL-2.0-or-later.
Adapted to explicit Lean state on 2026-10-03. See COPYING.md.
Player spawning enters the original raising state via setup. -/
import Doom.Fire
import Doom.Pickup
import Doom.Angles
import Doom.PlayerAnim
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
  body : PlayerAnim.State := {}
  deriving Inhabited

def supported (w : Nat) : Bool := w ≤ 2
def ready (w : Nat) : Nat := if w == 0 then PUNCH else if w == 2 then SGUN else PISTOL
def down (w : Nat) : Nat := ready w + 1
def up (w : Nat) : Nat := ready w + 2
def attackState (w : Nat) : Nat := ready w + 3

/-- Ammo gate shared by the live firing path and the DOS correspondence proof. -/
def ammoAvailable (w : Nat) (ammo : Int32) : Bool := w == 0 || ammo > 0

/-- E1M1 fallback priority when the readied weapon cannot fire. -/
def fallbackWeapon (shotgunOwned : Bool) (shells bullets : Int32) : Fin 10 :=
  if shotgunOwned && shells > 0 then 2 else if bullets > 0 then 1 else 0

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

/-- Ready-action priority for the supported fist, pistol and shotgun. -/
inductive ReadyDecision where
  | lower | fire | idle
  deriving DecidableEq, Repr

def readyDecision (pending : Nat) (health : Int32) (attack : Bool) : ReadyDecision :=
  if supported pending || health == 0 then .lower
  else if attack then .fire else .idle

/-- A_Lower's first movement and the dead-player clamp. Arithmetic is signed
16.16 with 32-bit wraparound, including the addition before the comparison. -/
def lowerHeight (y : Fixed) (dead : Bool) : Fixed :=
  let advanced := y + Fixed.ofInt 6
  if dead && !(advanced.raw < 128*65536) then Fixed.ofInt 128 else advanced

/-- A_Raise performs wrapping subtraction before its signed ready-height test.
The Boolean reports whether the ready-state action must run immediately. -/
def raiseStep (y : Fixed) : Fixed × Bool :=
  let advanced := y - Fixed.ofInt 6
  if advanced.raw > 32*65536 then (advanced,false) else (Fixed.ofInt 32,true)

/-- The no-attack ready action clears the latch and applies vanilla weapon bob. -/
def readyIdle (s : State) (bob : Fixed) (time : Int32) : State :=
  let angle : Angle := ⟨((time*128).toUInt32 &&& 8191) <<< 19⟩
  let half : Angle := ⟨((time*128).toUInt32 &&& 4095) <<< 19⟩
  { s with attackDown := false, weapon := { s.weapon with
    x := Fixed.ofInt 1 + bob*angle.fineCosine,
    y := Fixed.ofInt 32 + bob*half.fineSine } }

/-- The actual pistol/shotgun action. Geometry, RNG and sound remain ordered
runtime events; this function installs the pose, ammo debit and muzzle flash. -/
def fireAction (gun : Fire.Gun) (c : Context) : Context :=
  let ammo := gun.ammoIndex.val
  let discharge := Fire.discharge gun c.player.ammo[ammo]!
  let flash := if gun == .shotgun then SGUNFLASH1 else PISTOLFLASH
  { c with
    body := (PlayerAnim.enter 155).1,
    player := { c.player with ammo := c.player.ammo.set! ammo discharge.ammoAfter },
    state := { c.state with flash := { c.state.flash with frame := flash, tics := frames[flash]!.tics }, extraLight := 1 },
    events := c.events.push (if gun == .shotgun then .shotgun else .pistol (c.state.refire == 0)) }

/-- One execution of the original state-entry body. Recursive transfers are
parameters, allowing terminal actions to be reduced by the kernel. The runtime
supplies the same recursive callbacks below; there is no fuel limit. -/
def enterWith (enter : Context → Nat → Context) (fire : Context → Context)
    (checkAmmo : Context → Bool × Context) (c : Context) (id : Nat) : Context := Id.run do
  let mut c := { c with state := { c.state with weapon := { c.state.weapon with frame := id } } }
  if id == 0 then return c
  let f := frames[id]!
  c := { c with state := { c.state with weapon := { c.state.weapon with tics := f.tics } } }
  let w := c.player.readyWeapon.val
  match f.action with
  | "A_WeaponReady" =>
    if c.body.frame == 154 || c.body.frame == 155 then
      c := { c with body := (PlayerAnim.enter 149).1 }
    match readyDecision c.player.pendingWeapon.val c.player.health c.attack with
    | .lower => return enter c (down w)
    | .fire => return fire { c with state := { c.state with attackDown := true } }
    | .idle => c := { c with state := readyIdle c.state c.bob c.time }
  | "A_Lower" =>
    let advanced := c.state.weapon.y + Fixed.ofInt 6
    let y := lowerHeight c.state.weapon.y c.dead
    c := { c with state := { c.state with weapon := { c.state.weapon with y } } }
    if advanced.raw < 128*65536 then return c
    if c.dead then return c
    if c.player.health == 0 then return enter c 0
    let w := c.player.pendingWeapon.val
    if h : w < 9 then
      c := { c with player := { c.player with readyWeapon := ⟨w,h⟩, pendingWeapon := 9 }, state := { c.state with weapon := { c.state.weapon with y := Fixed.ofInt 128 } } }
      return enter c (up w)
  | "A_Raise" =>
    let (y,readyNow) := raiseStep c.state.weapon.y
    c := { c with state := { c.state with weapon := { c.state.weapon with y } } }
    if !readyNow then return c
    return enter c (ready w)
  | "A_ReFire" =>
    if c.attack && !c.pending && c.player.health != 0 then
      return fire { c with state := { c.state with refire := c.state.refire+1 } }
    c := (checkAmmo { c with state := { c.state with refire := 0 } }).2
  | "A_FirePistol" | "A_FireShotgun" =>
    c := fireAction (if f.action == "A_FireShotgun" then .shotgun else .pistol) c
  | "A_Punch" => c := { c with events := c.events.push .punch }
  | _ => pure ()
  if c.state.weapon.tics == 0 then return enter c frames[c.state.weapon.frame]!.next
  return c

mutual
private partial def resumeEnter (c : Context) (id : Nat) : Context :=
  enterWith resumeEnter fire checkAmmo c id

private partial def checkAmmo (c : Context) : Bool × Context :=
  let w := c.player.readyWeapon.val
  if ammoAvailable w c.player.ammo[if w == 2 then 1 else 0]! then (true,c)
  else
    let pending := fallbackWeapon c.player.weapons[2] c.player.ammo[1] c.player.ammo[0]
    (false,resumeEnter { c with player := { c.player with pendingWeapon := pending } } (down w))

private partial def fire (c : Context) : Context :=
  let (allowed,c) := checkAmmo c
  if !allowed then c else
    let c := resumeEnter { c with body := (PlayerAnim.enter 154).1 } (attackState c.player.readyWeapon.val)
    { c with events := c.events.push .noise }
end

/-- Expose the first state-entry step in the live path. Recursive transfers
remain the original interpreter and are separate correspondence obligations. -/
def enter (c : Context) (id : Nat) : Context := enterWith resumeEnter fire checkAmmo c id

/-- P_SetupPsprites/P_BringUpWeapon: entering the up state immediately invokes
A_Raise, so the first observable pistol offset is 122, not 128 or ready-height. -/
def setup (c : Context) : Context :=
  let state : State := { c.state with
    weapon := { frame := 0, tics := 0, y := Fixed.ofInt 128 }
    flash := { frame := 0, tics := 0, y := ⟨0⟩ } }
  enter { c with player := { c.player with pendingWeapon := 9 }, state } (up c.player.readyWeapon.val)

/-- The flash phase runs after the weapon phase, including on the tic a shot
creates a flash. Kept separate so its correspondence can be proved directly. -/
def tickFlash (s : State) : State := Id.run do
  let mut s := s
  if s.flash.frame != 0 && s.flash.tics != -1 then
    let mut flash := { s.flash with tics := s.flash.tics-1 }
    let mut light := s.extraLight
    if flash.tics == 0 then
      let next := frames[flash.frame]!.next
      if next == LIGHTDONE then flash := { flash with frame := 0 }; light := 0
      else flash := { flash with frame := next, tics := frames[next]!.tics }; light := 2
    s := { s with flash, extraLight := light }
  return { s with flash := { s.flash with x := s.weapon.x, y := s.weapon.y } }

/-- Original weapon-first, flash-second countdown. A newly created muzzle flash
loses its first tic in the same P_MovePsprites call. -/
def tick (c : Context) : Context := Id.run do
  let mut c := { c with events := #[] }
  if c.state.weapon.frame != 0 && c.state.weapon.tics != -1 then
    c := { c with state := { c.state with weapon := { c.state.weapon with tics := c.state.weapon.tics-1 } } }
    if c.state.weapon.tics == 0 then c := enter c frames[c.state.weapon.frame]!.next
  return { c with state := tickFlash c.state }

def drop (c : Context) : Context := enter c (down c.player.readyWeapon.val)

def label (s : Sprite) : Option String := do
  if s.frame == 0 then none else
    let f ← frames[s.frame]?
    return f.sprite ++ String.singleton (Char.ofNat (65+f.frame%32768)) ++ "0"

end Doom.Weapon
