import Doom.Proofs.OriginalWeaponDischarge
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000
open Doom Doom.Proofs Doom.Verification X86 X86Memory X86Control
open OriginalWeaponDischarge
namespace DischargeFixture
-- Deliberately unaligned player, and a CALL whose stack word wraps at 2^32.
def p : Word := 0x600043
def context (gun : Fire.Gun) (ammo : Int32) : Weapon.Context :=
  { state := {weapon := {frame := WeaponActions.windup gun, tics := 1}},
    player := {ammo := #v[ammo,ammo,77,88]} }
def machine (gun : Fire.Gun) (ammo : Int32) : X86Memory.State :=
  { regs := fun r => if r=1 then p else if r=4 then 1 else 0,
    memory := fun a =>
      let table : Memory := fun b =>
        if b=0x12dc0 then 1 else if b=0x12dbc then 17 else if b=0x12dd4 then 30 else 0
      let m := store32 table (p+112) (weaponNumber gun)
      let m := store32 m (p+156) ammo.toBitVec
      store32 m (p+160) ammo.toBitVec a }
example : Inputs .pistol (machine .pistol 0) (context .pistol 0) := by
  constructor <;> first | decide +kernel | (unfold BlockSummary.Apart; decide +kernel)
example : Inputs .shotgun (machine .shotgun (-2147483648)) (context .shotgun (-2147483648)) := by
  constructor <;> first | decide +kernel | (unfold BlockSummary.Apart; decide +kernel)
example : load32 (flashCall .pistol (machine .pistol 0)).core.memory (p+156) = 0xffffffff := by decide +kernel
example : load32 (flashCall .shotgun (machine .shotgun (-2147483648))).core.memory (p+160) = 0x7fffffff := by decide +kernel
example : (flashCall .shotgun (machine .shotgun 8)).core.regs 3 = 30 := by decide +kernel
example : load32 (flashCall .shotgun (machine .shotgun 8)).core.memory 0xfffffffd = 0x2d966 := by decide +kernel
-- Decoder accepts memory DEC and rejects register DEC and truncated operands.
example : X86Routine.decode [0xff,0x8c,0x81,0x9c,0,0,0] =
    some (.decrementMemory ⟨some 1,some 0,2,156⟩,[]) := by decide
example : X86Routine.decode [0xff,0xc8] = none := by decide
example : X86Routine.decode [0xff,0x8c,0x81,0x9c,0,0] = none := by decide
-- Forgotten DEC flags cannot silently be reused for a branch.
example : X86Routine.execute (.control (.jumpZero true 4))
    ⟨(machine .pistol 1),none,0x10⟩ = none := by decide
end DischargeFixture
