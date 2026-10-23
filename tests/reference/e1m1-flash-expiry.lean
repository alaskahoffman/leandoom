import Doom.Proofs.E1M1FlashExpiry
set_option maxRecDepth 32768
set_option maxHeartbeats 2000000
open Doom Doom.Proofs Doom.Verification X86 X86Memory X86Control BlockSummary
namespace FlashExpiryChecks

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

example : E1M1FlashUpdate.Inputs (initial 17 0x600100 0x603000) 0x600100 (live 17) := by
  constructor <;> decide
example : E1M1FlashExpiry.Tables (initial 17 0x600100 0x603000).memory := by
  constructor <;> decide
example : E1M1FlashExpiry.Separated 0x600100 0x603000 := by
  unfold E1M1FlashExpiry.Separated Apart; decide
-- Unaligned player and a scratch frame wrapping across address zero.
example : E1M1FlashExpiry.Separated 0x600101 5 := by
  unfold E1M1FlashExpiry.Separated Apart; decide
-- The callback return word would alias the extra-light field.
example : ¬ E1M1FlashExpiry.Separated 0x600100 (0x600100+248) := by
  intro h
  exact h 0 8 (by decide) 0 0 (by decide)
-- The player overlaps an original table word.
example : ¬ E1M1FlashExpiry.Separated (0x15a4c-232) 0x603000 := by
  intro h
  exact h 0 9 (by decide) 0 0 (by decide)

def observation (t : X86Control.State) :=
  (t.pc,t.core.regs 6,t.core.regs 4,
    load32 t.core.memory 0x600204,load32 t.core.memory 0x600208,load32 t.core.memory 0x6001e8)
example : (E1M1PspriteLight.slot 2 (initial 17 0x600100 0x603000)).map observation=
  some (0x2dc95,1,0x603000,0,0,0) := by decide
example : (E1M1PspriteLight.slot 2 (initial 30 0x600100 0x603000)).map observation=
  some (0x2dc95,1,0x603000,0x15d8c,3,2) := by decide
example : (E1M1PspriteLight.slot 2 (initial 31 0x600100 0x603000)).map observation=
  some (0x2dc95,1,0x603000,0,0,0) := by decide
example : (E1M1PspriteLight.slot 1 (initial 30 0x600100 0x603000)).isNone=true := by decide
-- Explicit non-vacuous use of the universal result with a wrapping scratch stack.
example : ∃ n t, n ≤ 106 ∧
    X86CodeMemory.Prefix FloorCaller.cm E1M1PspriteLight.program [] n
      ⟨initial 30 0x600101 5,none,0x2dc6f⟩ t ∧
    E1M1FlashUpdate.observe t.core.memory 0x600101=WeaponFlash.observe (Weapon.tickFlash (live 30)) := by
  apply E1M1FlashExpiry.expired_correspondence
  · constructor <;> decide
  · unfold WeaponFlash.Supported; decide
  · decide
  · decide
  · constructor <;> decide
  · unfold E1M1FlashExpiry.Separated Apart; decide

end FlashExpiryChecks
