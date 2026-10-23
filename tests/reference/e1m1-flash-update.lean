import Doom.Proofs.E1M1FlashUpdate
open Doom Doom.Proofs

def flash (id : Nat) (t : Int32) : Weapon.State :=
  { flash := { frame := id, tics := t }, extraLight := 7,
    weapon := { x := ⟨-123⟩, y := ⟨456⟩ } }
example : (Weapon.tickFlash (flash 30 1)).flash.frame=31 ∧
    (Weapon.tickFlash (flash 30 1)).flash.tics=3 ∧
    (Weapon.tickFlash (flash 30 1)).extraLight=2 := by decide
example : (Weapon.tickFlash (flash 17 1)).flash.frame=0 ∧
    (Weapon.tickFlash (flash 17 1)).flash.tics=0 ∧
    (Weapon.tickFlash (flash 17 1)).extraLight=0 := by decide
example : (Weapon.tickFlash (flash 31 1)).flash.frame=0 := by decide
example : (Weapon.tickFlash (flash 17 (-2147483648))).flash.tics=2147483647 := by decide
example : (Weapon.tickFlash (flash 17 0)).flash.tics=(-1) := by decide
example : (Weapon.tickFlash (flash 17 (-1))).extraLight=7 := by decide
example : (Weapon.tickFlash (flash 0 1)).flash.tics=1 := by decide
example : ¬ E1M1FlashUpdate.NoTransition (flash 30 1) := by unfold E1M1FlashUpdate.NoTransition; decide
example : ¬ WeaponFlash.Supported (flash 1 0) := by unfold WeaponFlash.Supported; decide
example : (Weapon.tickFlash (flash 0 1)).flash.x.raw=(-123) ∧
    (Weapon.tickFlash (flash 0 1)).flash.y.raw=456 := by decide
