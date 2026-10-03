/-
Single-player P_Give* and P_TouchSpecialThing, Chocolate Doom 3.1.1 p_inter.c,
commit 410d96855b5df5410ff591a90efeafa889119224.
Derived from id Software (1993-1996), Simon Howard (2005-2014).
SPDX-License-Identifier: GPL-2.0-or-later. See COPYING.md.
-/
import Doom.Fixed
import Init.Data.Vector.Basic

namespace Doom.Pickup

/-- Original enum order: clip, shell, cell, missile; 4 is am_noammo. -/
abbrev Ammo := Fin 5
abbrev Weapon := Fin 9
abbrev Card := Fin 6
abbrev Power := Fin 6
/-- Stable adapter ordinals, not the numeric values of DOOM's full sprite enum. -/
abbrev Sprite := Fin 36

def spriteNames : Vector String 36 := #v[
  "ARM1", "ARM2", "BON1", "BON2", "SOUL", "MEGA", "BKEY", "YKEY", "RKEY",
  "BSKU", "YSKU", "RSKU", "STIM", "MEDI", "PINV", "PSTR", "PINS", "SUIT",
  "PMAP", "PVIS", "CLIP", "AMMO", "ROCK", "BROK", "CELL", "CELP", "SHEL",
  "SBOX", "BPAK", "BFUG", "MGUN", "CSAW", "LAUN", "PLAS", "SHOT", "SGN2"]

structure Profile where
  skill : Fin 5 := 2
  commercial : Bool := true
  deriving Inhabited

/-- Pickup-visible player and mobj state. Cards and skulls remain separate;
pendingWeapon 9 means wp_nochange. Signed fields retain the C arithmetic profile.
Messages identify original string constants; localization/audio live elsewhere. -/
structure State where
  health : Int32 := 100
  bodyHealth : Int32 := 100
  armor : Int32 := 0
  armorType : Int32 := 0
  ammo : Vector Int32 4 := #v[50, 0, 0, 0]
  maxAmmo : Vector Int32 4 := #v[200, 50, 300, 50]
  weapons : Vector Bool 9 := #v[true, true, false, false, false, false, false, false, false]
  readyWeapon : Weapon := 1
  pendingWeapon : Fin 10 := 9
  cards : Vector Bool 6 := Vector.replicate 6 false
  powers : Vector Int32 6 := Vector.replicate 6 0
  backpack : Bool := false
  shadow : Bool := false
  bonus : Int32 := 0
  damageCount : Int32 := 0
  fixedColormap : Int32 := 0
  items : Int32 := 0
  message : String := "-"
  deriving Inhabited, BEq, Repr

def State.giveAmmo (s : State) (profile : Profile) (ammo : Ammo) (clips : Int32)
    : Bool × State := Id.run do
  if h : ammo.val < 4 then
    let i : Fin 4 := ⟨ammo.val, h⟩
    let old := s.ammo.get i
    if old == s.maxAmmo.get i then return (false, s)
    let clip : Int32 := (#v[10, 4, 20, 1] : Vector Int32 4).get i
    let count := if clips != 0 then clips * clip else clip / 2
    let count := if profile.skill == 0 || profile.skill == 4 then count <<< 1 else count
    let mut s := { s with ammo := s.ammo.set i.val (min (old + count) (s.maxAmmo.get i)) }
    if old != 0 then return (true, s)
    let ready := s.readyWeapon.val
    let pending := match ammo.val with
      | 0 => if ready == 0 then (if s.weapons[3] then 3 else 1) else s.pendingWeapon
      | 1 => if (ready == 0 || ready == 1) && s.weapons[2] then 2 else s.pendingWeapon
      | 2 => if (ready == 0 || ready == 1) && s.weapons[5] then 5 else s.pendingWeapon
      | 3 => if ready == 0 && s.weapons[4] then 4 else s.pendingWeapon
      | _ => s.pendingWeapon
    s := { s with pendingWeapon := pending }
    return (true, s)
  else return (false, s)

def State.giveWeapon (s : State) (profile : Profile) (weapon : Weapon) (dropped : Bool)
    : Bool × State := Id.run do
  let ammo := (#v[(4 : Ammo), 0, 1, 0, 3, 2, 2, 4, 1]).get weapon
  let (gaveAmmo, s) := s.giveAmmo profile ammo (if dropped then 1 else 2)
  if s.weapons.get weapon then return (gaveAmmo, s)
  return (true, { s with
    weapons := s.weapons.set weapon.val true,
    pendingWeapon := ⟨weapon.val, by omega⟩ })

def State.giveBody (s : State) (amount : Int32) : Bool × State :=
  if s.health ≥ 100 then (false, s) else
    let health := min 100 (s.health + amount)
    (true, { s with health, bodyHealth := health })

def State.giveArmor (s : State) (armorType : Int32) : Bool × State :=
  let hits := armorType * 100
  if s.armor ≥ hits then (false, s)
  else (true, { s with armor := hits, armorType })

def State.giveCard (s : State) (card : Card) : State :=
  if s.cards.get card then s
  else { s with cards := s.cards.set card.val true, bonus := 6 }

def State.givePower (s : State) (power : Power) : Bool × State :=
  match power.val with
  | 0 => (true, { s with powers := s.powers.set 0 1050 })
  | 1 => (true, { (s.giveBody 100).2 with powers := s.powers.set 1 1 })
  | 2 => (true, { s with powers := s.powers.set 2 2100, shadow := true })
  | 3 => (true, { s with powers := s.powers.set 3 2100 })
  | 5 => (true, { s with powers := s.powers.set 5 4200 })
  | _ => if s.powers.get power != 0 then (false, s)
         else (true, { s with powers := s.powers.set power.val 1 })

structure Item where
  sprite : Sprite
  z : Fixed := ⟨0⟩
  dropped : Bool := false
  countItem : Bool := false
  deriving Inhabited

inductive Sound where
  | item | weapon | power
  deriving BEq, Repr

/-- Map editor numbers and MF_COUNTITEM from the pinned info.c mobj table.
All these actors spawn with radius 20 and height 16 map units. -/
def itemOfEditor? (kind : Nat) (dropped : Bool := false) : Option Item := do
  let kinds : Vector Nat 36 := #v[2018,2019,2014,2015,2013,83,5,6,13,40,39,38,
    2011,2012,2022,2023,2024,2025,2026,2045,2007,2048,2010,2046,2047,17,
    2008,2049,8,2006,2002,2005,2003,2004,2001,82]
  let index ← kinds.toArray.findIdx? (· == kind)
  if h : index < 36 then
    some {
      sprite := ⟨index, h⟩, dropped,
      countItem := #[2,3,4,5,14,15,16,18,19].contains index }
  else none

structure Result where
  state : State
  removed : Bool := false
  sound : Option Sound := none
  deriving BEq, Repr

private def messages : Vector String 36 := #v[
  "GOTARMOR", "GOTMEGA", "GOTHTHBONUS", "GOTARMBONUS", "GOTSUPER", "GOTMSPHERE",
  "GOTBLUECARD", "GOTYELWCARD", "GOTREDCARD", "GOTBLUESKUL", "GOTYELWSKUL", "GOTREDSKULL",
  "GOTSTIM", "GOTMEDIKIT", "GOTINVUL", "GOTBERSERK", "GOTINVIS", "GOTSUIT",
  "GOTMAP", "GOTVISOR", "GOTCLIP", "GOTCLIPBOX", "GOTROCKET", "GOTROCKBOX",
  "GOTCELL", "GOTCELLBOX", "GOTSHELLS", "GOTSHELLBOX", "GOTBACKPACK", "GOTBFG9000",
  "GOTCHAINGUN", "GOTCHAINSAW", "GOTLAUNCHER", "GOTPLASMA", "GOTSHOTGUN", "GOTSHOTGUN2"]

/-- Single-player, unmodified DOOM 1.9 pickup effects once horizontal contact is
established. Height uses the toucher at its current position, not destination
floor height. No removal/sound on rejection. The caller must apply removal
immediately during PIT_CheckThing, even if a later check rejects the move. -/
def State.touch (initial : State) (profile : Profile) (item : Item)
    (toucherZ toucherHeight : Fixed) : Result := Id.run do
  let delta := item.z - toucherZ
  if delta.raw > toucherHeight.raw || delta.raw < -524288 || initial.bodyHealth ≤ 0 then
    return { state := initial }
  let mut s := initial
  let mut sound := Sound.item
  let mut message := messages.get item.sprite
  let mut granted := true
  match hs : item.sprite.val with
  | 0 => (granted, s) := s.giveArmor 1
  | 1 => (granted, s) := s.giveArmor 2
  | 2 =>
    let health := min 200 (s.health + 1)
    s := { s with health, bodyHealth := health }
  | 3 => s := { s with armor := min 200 (s.armor + 1), armorType := if s.armorType == 0 then 1 else s.armorType }
  | 4 =>
    let health := min 200 (s.health + 100)
    s := { s with health, bodyHealth := health }; sound := .power
  | 5 =>
    if !profile.commercial then return { state := initial }
    s := { s with health := 200, bodyHealth := 200 }
    s := (s.giveArmor 2).2; sound := .power
  | 6 | 7 | 8 | 9 | 10 | 11 =>
    let card : Card := ⟨item.sprite.val - 6, by omega⟩
    if s.cards.get card then message := s.message
    s := s.giveCard card
  | 12 => (granted, s) := s.giveBody 10
  | 13 =>
    (granted, s) := s.giveBody 25
    -- This check deliberately happens AFTER healing (the historical message bug).
    if s.health < 25 then message := "GOTMEDINEED"
  | 14 => (granted, s) := s.givePower 0; sound := .power
  | 15 =>
    (granted, s) := s.givePower 1
    if s.readyWeapon != 0 then s := { s with pendingWeapon := 0 }
    sound := .power
  | 16 => (granted, s) := s.givePower 2; sound := .power
  | 17 => (granted, s) := s.givePower 3; sound := .power
  | 18 => (granted, s) := s.givePower 4; sound := .power
  | 19 => (granted, s) := s.givePower 5; sound := .power
  | 20 => (granted, s) := s.giveAmmo profile 0 (if item.dropped then 0 else 1)
  | 21 => (granted, s) := s.giveAmmo profile 0 5
  | 22 => (granted, s) := s.giveAmmo profile 3 1
  | 23 => (granted, s) := s.giveAmmo profile 3 5
  | 24 => (granted, s) := s.giveAmmo profile 2 1
  | 25 => (granted, s) := s.giveAmmo profile 2 5
  | 26 => (granted, s) := s.giveAmmo profile 1 1
  | 27 => (granted, s) := s.giveAmmo profile 1 5
  | 28 =>
    if !s.backpack then s := { s with backpack := true, maxAmmo := s.maxAmmo.map (· * 2) }
    for i in [:4] do
      if h : i < 4 then s := (s.giveAmmo profile ⟨i, by omega⟩ 1).2
  | 29 => (granted, s) := s.giveWeapon profile 6 false; sound := .weapon
  | 30 => (granted, s) := s.giveWeapon profile 3 item.dropped; sound := .weapon
  | 31 => (granted, s) := s.giveWeapon profile 7 false; sound := .weapon
  | 32 => (granted, s) := s.giveWeapon profile 4 false; sound := .weapon
  | 33 => (granted, s) := s.giveWeapon profile 5 false; sound := .weapon
  | 34 => (granted, s) := s.giveWeapon profile 2 item.dropped; sound := .weapon
  | 35 => (granted, s) := s.giveWeapon profile 8 item.dropped; sound := .weapon
  | _ => return { state := initial }
  if !granted then return { state := s }
  s := { s with message, bonus := s.bonus + 6, items := s.items + (if item.countItem then 1 else 0) }
  return { state := s, removed := true, sound := some sound }

/-- Unmodified English messages from the pinned d_englsh.h. -/
def messageText : String → String
  | "GOTARMOR" => "Picked up the armor."
  | "GOTMEGA" => "Picked up the MegaArmor!"
  | "GOTHTHBONUS" => "Picked up a health bonus."
  | "GOTARMBONUS" => "Picked up an armor bonus."
  | "GOTSTIM" => "Picked up a stimpack."
  | "GOTMEDINEED" => "Picked up a medikit that you REALLY need!"
  | "GOTMEDIKIT" => "Picked up a medikit."
  | "GOTSUPER" => "Supercharge!"
  | "GOTBLUECARD" => "Picked up a blue keycard."
  | "GOTYELWCARD" => "Picked up a yellow keycard."
  | "GOTREDCARD" => "Picked up a red keycard."
  | "GOTBLUESKUL" => "Picked up a blue skull key."
  | "GOTYELWSKUL" => "Picked up a yellow skull key."
  | "GOTREDSKULL" => "Picked up a red skull key."
  | "GOTINVUL" => "Invulnerability!"
  | "GOTBERSERK" => "Berserk!"
  | "GOTINVIS" => "Partial Invisibility"
  | "GOTSUIT" => "Radiation Shielding Suit"
  | "GOTMAP" => "Computer Area Map"
  | "GOTVISOR" => "Light Amplification Visor"
  | "GOTMSPHERE" => "MegaSphere!"
  | "GOTCLIP" => "Picked up a clip."
  | "GOTCLIPBOX" => "Picked up a box of bullets."
  | "GOTROCKET" => "Picked up a rocket."
  | "GOTROCKBOX" => "Picked up a box of rockets."
  | "GOTCELL" => "Picked up an energy cell."
  | "GOTCELLBOX" => "Picked up an energy cell pack."
  | "GOTSHELLS" => "Picked up 4 shotgun shells."
  | "GOTSHELLBOX" => "Picked up a box of shotgun shells."
  | "GOTBACKPACK" => "Picked up a backpack full of ammo!"
  | "GOTBFG9000" => "You got the BFG9000!  Oh, yes."
  | "GOTCHAINGUN" => "You got the chaingun!"
  | "GOTCHAINSAW" => "A chainsaw!  Find some meat!"
  | "GOTLAUNCHER" => "You got the rocket launcher!"
  | "GOTPLASMA" => "You got the plasma gun!"
  | "GOTSHOTGUN" => "You got the shotgun!"
  | "GOTSHOTGUN2" => "You got the super shotgun!"
  | text => text

end Doom.Pickup
