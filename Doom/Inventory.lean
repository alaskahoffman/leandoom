import Doom.Things
import Doom.PlayerCounters

namespace Doom

structure Inventory where
  health : Nat := 100
  armor : Nat := 0
  armorType : Nat := 0
  blue : Bool := false
  red : Bool := false
  yellow : Bool := false
  bullets : Nat := 50
  shells : Nat := 0
  rockets : Nat := 0
  cells : Nat := 0
  backpack : Bool := false
  weapons : Array Nat := #[0, 1] -- Fist, pistol, followed by vanilla weapon indices.
  invulnerability : Nat := 0
  invisibility : Nat := 0
  suit : Nat := 0
  visor : Nat := 0
  berserk : Bool := false
  computerMap : Bool := false
  pickupState : Pickup.State := {}
  deriving Inhabited, BEq

/-- Bridge the remaining prototype combat/UI fields to the signed pickup state.
Separate cards, pending weapon and counters survive successive movement calls. -/
def Inventory.toPickup (i : Inventory) : Pickup.State := Id.run do
  let n (v : Nat) : Int32 := Int32.ofInt v
  let mut cards := i.pickupState.cards
  for (owned, card, skull) in #[(i.blue, 0, 3), (i.yellow, 1, 4), (i.red, 2, 5)] do
    if owned && !cards[card]! && !cards[skull]! then cards := cards.set! card true
  return { i.pickupState with
    health := n i.health, bodyHealth := n i.health, armor := n i.armor, armorType := n i.armorType,
    ammo := #v[n i.bullets, n i.shells, n i.cells, n i.rockets],
    maxAmmo := (#v[200,50,300,50] : Vector Int32 4).map (· * (if i.backpack then 2 else 1)),
    weapons := Vector.ofFn (fun w => i.weapons.contains w.val), cards,
    powers := #v[n i.invulnerability, if i.berserk then (if i.pickupState.powers[1] == 0 then 1 else i.pickupState.powers[1]) else 0, n i.invisibility,
      n i.suit, if i.computerMap then 1 else 0, n i.visor],
    backpack := i.backpack }

def Inventory.fromPickup (s : Pickup.State) : Inventory := {
  health := s.health.toInt.toNat, armor := s.armor.toInt.toNat, armorType := s.armorType.toInt.toNat,
  bullets := s.ammo[0].toInt.toNat, shells := s.ammo[1].toInt.toNat,
  cells := s.ammo[2].toInt.toNat, rockets := s.ammo[3].toInt.toNat,
  blue := s.cards[0] || s.cards[3], yellow := s.cards[1] || s.cards[4], red := s.cards[2] || s.cards[5],
  backpack := s.backpack, weapons := (Array.range 9).filter (fun w => s.weapons[w]!),
  invulnerability := s.powers[0].toInt.toNat, berserk := s.powers[1] != 0,
  invisibility := s.powers[2].toInt.toNat, suit := s.powers[3].toInt.toNat,
  computerMap := s.powers[4] != 0, visor := s.powers[5].toInt.toNat, pickupState := s }

/-- Live-player stage only; dead-player damage fading belongs to DeathThink. -/
def Inventory.tick (i : Inventory) : Inventory :=
  if i.health == 0 then i else fromPickup i.toPickup.tickCounters

/-- Convenience grant for isolated inventory checks. Runtime contact goes through
Collision.checkPositionWithEffects, including original ordering and unlinking. -/
def Inventory.pickup (i : Inventory) (kind : Nat) (dropped : Bool := false) : Option (Inventory × String) := do
  let item ← Pickup.itemOfEditor? kind dropped
  let result := i.toPickup.touch {} item (Fixed.ofInt 0) (Fixed.ofInt 56)
  if result.removed then some (fromPickup result.state, result.state.message) else none

/-- Armor absorbs a third (green) or half (blue) of incoming damage. -/
def Inventory.damage (i : Inventory) (amount : Nat) : Inventory :=
  if i.invulnerability > 0 || i.health == 0 then i else
    let absorbed := min i.armor (if i.armorType == 1 then amount / 3 else if i.armorType == 2 then amount / 2 else 0)
    let armor := i.armor - absorbed
    let count := min (100 : Int32) (i.pickupState.damageCount + Int32.ofInt (amount-absorbed))
    { i with
      health := i.health - (amount - absorbed), armor
      armorType := (if armor == 0 then 0 else i.armorType)
      pickupState := { i.pickupState with damageCount := count } }

end Doom
