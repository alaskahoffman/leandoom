import Doom.Proofs.OriginalPlayerArmor
open Doom Doom.Verification X86 X86Memory X86Control Doom.Proofs PlayerArmor

def machine (p : Word) (d a k : Int32) : X86Memory.State :=
  ⟨fun r => if r = 5 then p else if r = 7 then d.toBitVec else 0x10203040,
    store32 (store32 (fun _ => 0xa5) (p+36) a.toBitVec) (p+40) k.toBitVec⟩

def agrees (p : Word) (d a k : Int32) : Bool :=
  let s := machine p d a k
  let out := PlayerDamage.absorbArmor {armor := a,armorType := k} d
  match X86Routine.run program [0x2a616] 24 ⟨s,none,0x2a5d5⟩ with
  | none => false
  | some t => t.core.regs 7 == out.2.toBitVec &&
      load32 t.core.memory (p+36) == out.1.armor.toBitVec &&
      load32 t.core.memory (p+40) == out.1.armorType.toBitVec &&
      t.core.regs 4 == s.regs 4 && t.core.regs 5 == p && t.pc == 0x2a616

def divide (high low divisor : Word) : Option (Word × Word × Bool) :=
  let s : X86Control.State := ⟨⟨fun r => if r = 0 then low else if r = 2 then high else divisor,fun _ => 0⟩,
    some (logical32 0),123⟩
  (X86Routine.execute (.signedDivide 3) s).map fun t => (t.core.regs 0,t.core.regs 2,t.flags.isNone)

#eval [agrees 0x1001 20 100 1, agrees 0x1002 20 6 1, agrees 0x1003 20 5 1,
  agrees 0xffffffd8 20 10 2, agrees 0xffffffd9 5 100 0,
  agrees 0xffffffd7 (-2147483648) (-2147483648) 1,
  agrees 0x1000 2147483647 (-1) 2, agrees 2 (-3) 200 (-1),
  agrees 0xffffffdc (-1) 200 1, agrees 0x1000 0 0 1,
  divide 0 10 3 == some (3,1,true), divide 0xffffffff 0xfffffff6 3 == some (0xfffffffd,0xffffffff,true),
  divide 0 10 0xfffffffd == some (0xfffffffd,1,true),
  (divide 0 10 0).isNone, (divide 0x80000000 0 0xffffffff).isNone,
  (divide 0 0x80000000 1).isNone, (divide 0xffffffff 0x80000000 0xffffffff).isNone,
  divide 0xffffffff 0x80000000 1 == some (0x80000000,0,true),
  X86Routine.decode [0xf7,0x3b] == none, X86Routine.decode [0xf7,0xfb] == some (.signedDivide 3,[]),
  X86Routine.decode [0xf7,0xeb] == some (.control (.block (.arithmetic (.imul 3))),[])]
