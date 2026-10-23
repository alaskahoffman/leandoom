/-
Single-player status rules from Chocolate Doom 3.1.1 st_stuff.c / st_lib.c,
commit 410d96855b5df5410ff591a90efeafa889119224.
Derived from id Software (1993-1996), Simon Howard (2005-2014).
SPDX-License-Identifier: GPL-2.0-or-later. See COPYING.md.
-/
import Doom.Pickup

namespace Doom.Status

/-- STlib multi-icon state belongs to presentation history, not game tics. -/
structure Widgets where
  arms : Array (Option String) := Array.replicate 6 none
  face : Option String := none
  keys : Array (Option String) := Array.replicate 3 none
  deriving Inhabited

def faceName (index : Nat) : String :=
  let pain := index / 8
  if index == 40 then "STFGOD0" else if index == 41 then "STFDEAD0" else
    match index % 8 with
    | 0 | 1 | 2 => s!"STFST{pain}{index % 8}"
    | 3 => s!"STFTR{pain}0"
    | 4 => s!"STFTL{pain}0"
    | 5 => s!"STFOUCH{pain}"
    | 6 => s!"STFEVL{pain}"
    | _ => s!"STFKILL{pain}"

def patchNames : Array String :=
  #["STBAR", "STARMS", "STTPRCNT"] ++
  (Array.range 10).map (s!"STTNUM{·}") ++
  (Array.range 10).map (s!"STYSNUM{·}") ++
  (Array.range 6).map (s!"STGNUM{·+2}") ++
  (Array.range 6).map (s!"STKEYS{·}") ++
  (Array.range 42).map faceName

/-- Pure ST_doPaletteStuff selection, DOOM profile (not Chex Quest). -/
def palette (p : Pickup.State) : Nat := Id.run do
  let mut count := p.damageCount
  if p.powers[1] != 0 then count := max count ((12 : Int32) - (p.powers[1] >>> 6))
  if count != 0 then return (min (7 : Int32) ((count + 7) >>> 3) + 1).toInt.toNat
  if p.bonus != 0 then return (min (3 : Int32) ((p.bonus + 7) >>> 3) + 9).toInt.toNat
  if p.powers[3] > 128 || p.powers[3] &&& 8 != 0 then return 13
  return 0

def readyAmmo (p : Pickup.State) : Int32 :=
  let kind := (#v[4,0,1,0,3,2,2,4,1] : Vector Nat 9).get p.readyWeapon
  if h : kind < 4 then p.ammo[kind] else 1994

def key (p : Pickup.State) (i : Fin 3) : Option Nat :=
  if p.cards[i.val+3] then some (i.val+3) else if p.cards[i.val] then some i.val else none

structure Face where
  index : Nat := 0
  count : Int := 0
  priority : Nat := 0
  lastAttack : Int := -1
  oldHealth : Int := -1
  oldWeapons : Vector Bool 9 := #v[true,true,false,false,false,false,false,false,false]
  deriving Inhabited, BEq, Repr

structure FaceInput where
  player : Pickup.State := {}
  attack : Bool := false
  god : Bool := false
  angle : UInt32 := 0
  attackerAngle : Option UInt32 := none
  random : Nat := 0

/-- ST_calcPainOffset, for player health 0..200. -/
def painOffset (health : Int) : Nat := (8 * ((100 - min 100 health) * 5 / 101)).toNat

/-- One ST_Ticker face step. Rendering never calls this function. The historical
health-minus-oldhealth "ouch" comparison and unnormalized angle difference are
intentional. Inputs use live player's nonnegative health and a byte RNG value. -/
def Face.tick (s : Face) (input : FaceInput) : Face := Id.run do
  let p := input.player
  let health := p.health.toInt
  let pain := painOffset health
  let mut s := s
  if s.priority < 10 && health == 0 then
    s := { s with priority := 9, index := 41, count := 1 }
  if s.priority < 9 && p.bonus != 0 then
    if s.oldWeapons != p.weapons then
      s := { s with priority := 8, count := 70, index := pain+6, oldWeapons := p.weapons }
  if s.priority < 8 && p.damageCount != 0 then
    if let some angle := input.attackerAngle then
      s := { s with priority := 7, count := 35 }
      if health - s.oldHealth > 20 then s := { s with index := pain+5 }
      else
        let diff := if angle > input.angle then angle-input.angle else input.angle-angle
        let right := if angle > input.angle then diff > 0x80000000 else diff ≤ 0x80000000
        s := { s with index := pain + (if diff < 0x20000000 then 7 else if right then 3 else 4) }
  if s.priority < 7 && p.damageCount != 0 then
    s := { s with priority := (if health - s.oldHealth > 20 then 7 else 6), count := 35, index := pain + (if health - s.oldHealth > 20 then 5 else 7) }
  if s.priority < 6 then
    if input.attack then
      if s.lastAttack == -1 then s := { s with lastAttack := 70 }
      else
        s := { s with lastAttack := s.lastAttack-1 }
        if s.lastAttack == 0 then
          s := { s with priority := 5, index := pain+7, count := 1, lastAttack := 1 }
    else s := { s with lastAttack := -1 }
  if s.priority < 5 && (input.god || p.powers[0] != 0) then
    s := { s with priority := 4, index := 40, count := 1 }
  if s.count == 0 then
    s := { s with index := pain + input.random % 3, count := 17, priority := 0 }
  return { s with count := s.count-1, oldHealth := health }

/-- ST_Start resets these fields; the function-static priority/attack timer and
the global face count survive a level restart in the original implementation. -/
def Face.start (s : Face) (p : Pickup.State) : Face :=
  { s with index := 0, oldHealth := -1, oldWeapons := p.weapons }

structure Digit where
  x : Int
  digit : Nat -- 10 denotes STTMINUS
  deriving BEq, Repr, Inhabited

/-- STlib_drawNum patch placements. The caller restores width*digitWidth pixels
from the backing bar first, including when 1994 suppresses the number. -/
def digits (value : Int) (width digitWidth : Nat) (right : Int) : Array Digit := Id.run do
  let negative := value < 0
  let value := if negative && width == 2 then max (-9) value
    else if negative && width == 3 then max (-99) value else value
  let mut n := value.natAbs
  if n == 1994 then return #[]
  let mut x := right
  let mut result := #[]
  if n == 0 then result := result.push ⟨x-Int.ofNat digitWidth,0⟩
  for _ in [:width] do
    if n == 0 then break
    x := x - Int.ofNat digitWidth
    result := result.push ⟨x,n%10⟩
    n := n/10
  if negative then result := result.push ⟨x-8,10⟩
  return result

end Doom.Status
