import Doom.Proofs.E1M1WeaponFlash
set_option maxRecDepth 32768
set_option maxHeartbeats 2000000
open Doom Doom.Proofs Doom.Verification X86 X86Memory X86Control BlockSummary
namespace WeaponFlashChecks
def record (m : Memory) (id timer next action : Word) : Memory :=
  let a := 0x15a28+28*id
  store32 (store32 (store32 m (a+8) timer) (a+16) next) (a+12) action
def tables := record (record (record (record (fun _ => 0)
  1 0 0 0x2db40) 17 7 1 0x2db50) 30 4 31 0x2db50) 31 3 1 0x2db60

def live (id : Nat) : Weapon.State :=
  { flash := { frame := id, tics := 1 }, extraLight := 7,
    weapon := { x := ⟨-20⟩, y := ⟨40⟩ } }
def initial (id : Nat) (p sp : Word) : X86Memory.State :=
  ⟨write (write (write (write (fun _ => 0) 1 (p+260)) 4 sp) 6 1) 7 p,
    store32 (store32 (store32 (store32 (store32 tables
      (p+260) (WeaponFlash.pointer id)) (p+264) 1) (p+232) 7) (p+252) (-20)) (p+256) 40⟩


def context : Weapon.Context := { state := { live 30 with weapon := { (live 30).weapon with frame := 10, tics := 2 } } }
def weaponInitial (p sp : Word) : X86Memory.State :=
  let s := initial 30 p sp
  ⟨write (write s.regs 1 (p+244)) 6 0,
    store32 (store32 s.memory (p+244) (WeaponFlash.pointer 10)) (p+248) 2⟩

example : E1M1WeaponFlash.Inputs (weaponInitial 0x600101 5) 0x600101 context.state := by
  constructor
  · constructor <;> decide
  · decide
  · decide
example : E1M1WeaponFlash.Safe 0x600101 5 := by
  unfold E1M1WeaponFlash.Safe Apart; decide
example : E1M1FlashExpiry.Tables (weaponInitial 0x600101 5).memory := by
  constructor <;> decide
-- Reject a scratch word overlapping the weapon timer.
example : ¬ E1M1WeaponFlash.Safe 0x600100 (0x600100+252) := by
  intro h
  exact h 5 0 0 (by decide)
example : ¬ E1M1WeaponFlash.Quiet {context.state with weapon := {context.state.weapon with tics := 1}} := by
  unfold E1M1WeaponFlash.Quiet; decide
example : (E1M1WeaponFlash.countdown context.state).weapon.tics=1 := by decide
example : (E1M1WeaponFlash.countdown context.state).flash.tics=1 := by decide

-- Kernel-check a concrete application of the composed theorem, with an unaligned
-- player, wrapping scratch stack, weapon countdown and an expiring shotgun flash.
example : ∃ n t, n ≤ 125 ∧
    X86CodeMemory.Prefix FloorCaller.cm E1M1PspriteLight.program [] n
      ⟨weaponInitial 0x600101 5,none,0x2dc6f⟩ t ∧
    E1M1FlashUpdate.observe t.core.memory 0x600101=WeaponFlash.observe (Weapon.tick context).state := by
  apply E1M1WeaponFlash.live_correspondence
  · constructor
    · constructor <;> decide
    · decide
    · decide
  · unfold E1M1WeaponFlash.Quiet; decide
  · unfold WeaponFlash.Supported; decide
  · unfold E1M1WeaponFlash.Safe Apart; decide
  · intro _
    constructor
    · constructor <;> decide
    · unfold E1M1FlashExpiry.Separated Apart; decide

-- The seam uses the post-weapon flash values. A flash created with seven tics
-- is immediately decremented to six, not delayed until the next tic.
example : (Weapon.tickFlash {context.state with flash := {context.state.flash with frame := 17, tics := 7}}).flash.tics=6 := by decide

end WeaponFlashChecks
