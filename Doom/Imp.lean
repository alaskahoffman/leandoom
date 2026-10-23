/- Original imp/zombieman branches of p_enemy.c, Chocolate Doom 3.1.1.
Derived from id Software / Simon Howard. SPDX-License-Identifier: GPL-2.0-or-later. -/
import Doom.ImpData
import Doom.Slide
import Doom.Angles
import Doom.ActorClock

namespace Doom.Imp
open Collision ImpData

structure State where
  id : Nat
  kind : Nat := 3001
  frame : Nat := TROO_STND
  tics : Int32 := 10
  angle : Angle := ⟨0⟩
  target : Option Nat := none
  movedir : Nat := 0
  movecount : Int32 := 0
  reaction : Int32 := 8
  threshold : Int32 := 0
  lastlook : Nat := 0
  ambush : Bool := false
  justHit : Bool := false
  justAttacked : Bool := false
  deriving Inhabited

def State.spawnFrame (a : State) : Nat := if a.kind == 3004 then POSS_STND else TROO_STND
def State.chaseFrame (a : State) : Nat := if a.kind == 3004 then POSS_RUN1 else TROO_RUN1
def State.attackFrame (a : State) : Nat := if a.kind == 3004 then POSS_ATK1 else TROO_ATK1
def State.painFrame (a : State) : Nat := if a.kind == 3004 then POSS_PAIN else TROO_PAIN

inductive Event where
  | sound (name : String)
  | melee (target : Nat) (damage : Nat)
  | missile (target : Nat)
  | hitscan (target : Nat)
  deriving Repr

structure Hooks (α : Type) where
  thing : α → Nat → Except String SolidThing
  sight : α → Nat → Nat → Except String Bool
  shadow : α → Nat → Bool
  soundTarget : α → Nat → Option Nat
  move : α → State → Except String (α × State × Bool)

structure World (α : Type) where
  host : α
  actor : State
  rng : DoomRandom
  events : Array Event := #[]

abbrev M (α : Type) := StateT (World α) (Except String)

private def roll : M α Nat := do
  let w ← get
  let (n,rng) := w.rng.nextPlay
  set { w with rng }
  return n

private def emit (e : Event) : M α Unit := modify fun w => { w with events := w.events.push e }
private def change (f : State → State) : M α Unit := modify fun w => { w with actor := f w.actor }

private def object (h : Hooks α) (id : Nat) : M α SolidThing := do
  h.thing (← get).host id

private def visible (h : Hooks α) (id : Nat) : M α Bool := do
  let w ← get
  h.sight w.host w.actor.id id

private def distance (h : Hooks α) (id : Nat) : M α Fixed := do
  let a ← object h (← get).actor.id
  let b ← object h id
  approximateDistance (b.x-a.x) (b.y-a.y)

def meleeRange (h : Hooks α) : M α Bool := do
  let some id := (← get).actor.target | return false
  let target ← object h id
  if (← distance h id).raw ≥ (Fixed.ofInt 44 + target.radius).raw then return false
  visible h id

def missileRange (h : Hooks α) : M α Bool := do
  let some id := (← get).actor.target | return false
  if !(← visible h id) then return false
  if (← get).actor.justHit then
    change fun a => { a with justHit := false }
    return true
  if (← get).actor.reaction != 0 then return false
  let offset := if (← get).actor.kind == 3004 then 192 else 64
  let dist := min (200 : Int32) (((← distance h id) - Fixed.ofInt offset).raw >>> 16)
  return Int32.ofNat (← roll) ≥ dist

private def walk (h : Hooks α) : M α Bool := do
  let w ← get
  let (host,actor,ok) ← h.move w.host w.actor
  set { w with host, actor }
  return ok

private def tryWalk (h : Hooks α) : M α Bool := do
  if !(← walk h) then return false
  let count ← roll
  change fun a => { a with movecount := Int32.ofNat (count &&& 15) }
  return true

def newChaseDir (h : Hooks α) : M α Unit := do
  let a := (← get).actor
  let some target := a.target | throw "imp: chase without target"
  let own ← object h a.id; let dest ← object h target
  let dx := dest.x-own.x; let dy := dest.y-own.y
  let old := a.movedir
  let turn := #[4,5,6,7,0,1,2,3,8][old]!
  let mut xdir := if dx.raw > 655360 then 0 else if dx.raw < -655360 then 4 else 8
  let mut ydir := if dy.raw < -655360 then 6 else if dy.raw > 655360 then 2 else 8
  if xdir != 8 && ydir != 8 then
    let dir := #[3,1,5,7][(if dy.raw < 0 then 2 else 0)+(if dx.raw > 0 then 1 else 0)]!
    change fun a => { a with movedir := dir }
    if dir != turn then
      if (← tryWalk h) then return
  let random ← roll
  let ax ← checkedPathAbs dx; let ay ← checkedPathAbs dy
  if random > 200 || ay.raw > ax.raw then
    let t := xdir; xdir := ydir; ydir := t
  if xdir == turn then xdir := 8
  if ydir == turn then ydir := 8
  for dir in #[xdir,ydir,old] do
    if dir != 8 then
      change fun a => { a with movedir := dir }
      if (← tryWalk h) then return
  let forward := (← roll) &&& 1 != 0
  for i in [:8] do
    let dir := if forward then i else 7-i
    if dir != turn then
      change fun a => { a with movedir := dir }
      if (← tryWalk h) then return
  if turn != 8 then
    change fun a => { a with movedir := turn }
    if (← tryWalk h) then return
  change fun a => { a with movedir := 8 }

private def lookPlayer (h : Hooks α) (allaround : Bool) : M α Bool := do
  -- Original four-slot scan, with only player 0 active in this runtime profile.
  let stop := ((← get).actor.lastlook+3)%4
  let mut count := 0
  for _ in [:12] do
    let a := (← get).actor
    if a.lastlook == 0 then
      if count == 2 || a.lastlook == stop then return false
      count := count+1
      let player ← object h 0
      if player.health > 0 then
        if (← visible h 0) then
          let own ← object h a.id
          let angle := (Angle.fromVector (player.x-own.x) (player.y-own.y)).raw-a.angle.raw
          let allowed ← if !allaround && angle > 0x40000000 && angle < 0xc0000000 then
              do pure (decide ((← distance h 0).raw ≤ 4194304))
            else pure true
          if allowed then
            change fun a => { a with target := some 0 }
            return true
    change fun a => { a with lastlook := (a.lastlook+1)%4 }
  throw "imp: invalid player scan"

private def face (h : Hooks α) : M α Unit := do
  let a := (← get).actor
  let some target := a.target | return
  let own ← object h a.id; let dest ← object h target
  let mut angle := Angle.fromVector (dest.x-own.x) (dest.y-own.y)
  if h.shadow (← get).host target then
    let first ← roll; let second ← roll
    angle := ⟨angle.raw + (Int32.ofInt (Int.ofNat first-Int.ofNat second) <<< 21).toUInt32⟩
  change fun a => { a with angle, ambush := false }

/-- State entry actions execute immediately, including Look→Chase→Attack.
Normal single-player skill: multiplayer/fast/nightmare branches are excluded. -/
def enter (h : Hooks α) : Nat → Nat → M α Unit
  | 0,_ => throw "imp: recursive state action limit"
  | fuel+1,id => do
    let some frame := frames.find? (·.id == id) | throw "imp: missing live state"
    change fun a => { a with frame := id, tics := frame.tics }
    match frame.action with
    | "NULL" => pure ()
    | "A_Pain" => emit (.sound "popain")
    | "A_FaceTarget" => face h
    | "A_PosAttack" =>
      let some target := (← get).actor.target | return
      face h
      emit (.hitscan target)
    | "A_TroopAttack" =>
      let some target := (← get).actor.target | return
      face h
      if (← meleeRange h) then
        emit (.sound "claw")
        emit (.melee target (3*((← roll)%8+1)))
      else emit (.missile target)
    | "A_Look" =>
      change fun a => { a with threshold := 0 }
      let w ← get
      let mut found := false
      if let some target := h.soundTarget w.host w.actor.id then
        if (← object h target).shootable then
          change fun a => { a with target := some target }
          found ← if w.actor.ambush then visible h target else pure true
      if !found then found ← lookPlayer h false
      if found then
        let sound ← if (← get).actor.kind == 3004 then do pure s!"posit{(← roll)%3+1}"
          else do pure s!"bgsit{(← roll)%2+1}"
        emit (.sound sound)
        enter h fuel (← get).actor.chaseFrame
    | "A_Chase" =>
      let a := (← get).actor
      let targetDead ← match a.target with
        | none => pure true
        | some id => do pure (decide ((← object h id).health ≤ 0))
      change fun a => { a with
        reaction := if a.reaction != 0 then a.reaction-1 else 0,
        threshold := if a.threshold == 0 || targetDead then 0 else a.threshold-1 }
      let a := (← get).actor
      if a.movedir < 8 then
        let angle := a.angle.raw &&& 0xe0000000
        let delta := (angle - (UInt32.ofNat a.movedir <<< 29)).toInt32
        change fun a => { a with angle := ⟨if delta > 0 then angle-0x20000000 else if delta < 0 then angle+0x20000000 else angle⟩ }
      let valid ← match a.target with
        | none => pure false
        | some id => do pure (← object h id).shootable
      if !valid then
        if !(← lookPlayer h true) then enter h fuel (← get).actor.spawnFrame
        return
      if a.justAttacked then
        change fun a => { a with justAttacked := false }
        newChaseDir h
        return
      if (← get).actor.kind != 3004 && (← meleeRange h) then
        enter h fuel (← get).actor.attackFrame
        return
      if (← get).actor.movecount == 0 then
        if (← missileRange h) then
          enter h fuel (← get).actor.attackFrame
          change fun a => { a with justAttacked := true }
          return
      change fun a => { a with movecount := a.movecount-1 }
      if (← get).actor.movecount < 0 then newChaseDir h
      else if !(← walk h) then newChaseDir h
      if (← roll) < 3 then emit (.sound (if (← get).actor.kind == 3004 then "posact" else "bgact"))
    | other => throw s!"imp: unsupported action {other}"

def tick (h : Hooks α) : M α Unit := do
  match ActorClock.step (← get).actor.tics with
  | .hold n => change fun a => { a with tics := n }
  | .enterNext =>
    change fun a => { a with tics := 0 }
    let some frame := frames.find? (·.id == (← get).actor.frame) | throw "imp: missing state"
    enter h 64 frame.next

end Doom.Imp
