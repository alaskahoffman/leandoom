import Doom.Proofs.OriginalFloorDamage
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option linter.unusedSimpArgs false
namespace Doom.Proofs.RandomReturn
open Verification X86 X86Memory X86Control BlockSummary
open FloorDamage (nextIndex randomMemory increment_index mask_byte randomByte random_value)

def rngListed : X86Routine.Program
  | 0x24160 => some (.control (.block (.load 0 ⟨none,none,0,0x12720⟩)),5)
  | 0x24165 => some (.addImmediate 0 1,1)
  | 0x24166 => some (.control (.andEax 255),5)
  | 0x2416b => some (.control (.storeEax 0x12720),5)
  | 0x24170 => some (.control (.loadByte 0 ⟨some 0,none,0,0x1261c⟩),6)
  | 0x24176 => some (.control (.andEax 255),5)
  | 0x2417b => some (.ret,1)
  | _ => none

def randomEnd (resume : Fin 4294967296) (s : X86Memory.State) (i : UInt8) (b : BitVec 8) : X86Control.State :=
  ⟨⟨write (write s.regs 0 (b.zeroExtend 32)) 4 (s.regs 4+(4#32)),randomMemory s i⟩,
    some (logical32 (b.zeroExtend 32)),resume.val⟩

/-- Real P_Random instructions and RET in the shared byte-addressed memory.
Table/return reads are from memory after the index write, so aliasing is never
silently discarded by the instruction proof. -/
theorem random_execution (resume : Fin 4294967296)
    (outside : resume.val < 0x24160 ∨ 0x2417c ≤ resume.val) (s : X86Memory.State) (f : Option Flags) (i : UInt8) (b : BitVec 8)
    (index : load32 s.memory (0x12720#32) = BitVec.ofNat 32 i.toNat)
    (table : randomMemory s i ((0x1261c#32)+nextIndex i) = b)
    (ret : load32 (randomMemory s i) (s.regs 4) = (BitVec.ofNat 32 resume.val)) :
    X86Routine.run rngListed [resume.val] 7 ⟨s,f,0x24160⟩ = some (randomEnd resume s i b) := by
  let c1 := put s 0 (BitVec.ofNat 32 i.toNat)
  let c2 := put c1 0 (BitVec.ofNat 32 i.toNat+1)
  let c3 := put c2 0 (nextIndex i)
  let c4 : X86Memory.State := { c3 with memory := randomMemory s i }
  let c5 := putByte c4 0 b
  let c6 := put c5 0 (b.zeroExtend 32)
  have path : X86Routine.Prefix rngListed [resume.val] 7 ⟨s,f,0x24160⟩
      ⟨put c6 4 (s.regs 4+4),some (logical32 (b.zeroExtend 32)),resume.val⟩ := by
    apply X86Routine.Prefix.step (middle := ⟨c1,f,0x24165⟩) (by simp only [List.mem_singleton]; omega) (show rngListed 0x24160 = _ from rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Block.Address.eval,blockPreservesFlags,c1,index])
    apply X86Routine.Prefix.step (middle := ⟨c2,none,0x24166⟩) (by simp only [List.mem_singleton]; omega) (show rngListed 0x24165 = _ from rfl) (by
      simp [X86Routine.execute,c2,c1,put,write])
    apply X86Routine.Prefix.step (middle := ⟨c3,some (logical32 (nextIndex i)),0x2416b⟩) (by simp only [List.mem_singleton]; omega) (show rngListed 0x24166 = _ from rfl) (by
      simp [X86Routine.execute,X86Control.execute,c3,c2,c1,put,write,increment_index])
    apply X86Routine.Prefix.step (middle := ⟨c4,some (logical32 (nextIndex i)),0x24170⟩) (by simp only [List.mem_singleton]; omega) (show rngListed 0x2416b = _ from rfl) (by
      simp [X86Routine.execute,X86Control.execute,c4,c3,c2,c1,put,write,randomMemory])
    apply X86Routine.Prefix.step (middle := ⟨c5,some (logical32 (nextIndex i)),0x24176⟩) (by simp only [List.mem_singleton]; omega) (show rngListed 0x24170 = _ from rfl) (by
      simp [X86Routine.execute,X86Control.execute,X86Block.Address.eval,c5,c4,c3,c2,c1,put,write,BitVec.add_comm,table,eax])
    apply X86Routine.Prefix.step (middle := ⟨c6,some (logical32 (b.zeroExtend 32)),0x2417b⟩) (by simp only [List.mem_singleton]; omega) (show rngListed 0x24176 = _ from rfl) (by
      simp [X86Routine.execute,X86Control.execute,c6,c5,putByte,byteReg,put,write,mask_byte,eax])
    apply X86Routine.Prefix.step (middle := ⟨put c6 4 (s.regs 4+4),some (logical32 (b.zeroExtend 32)),resume.val⟩)
      (by simp only [List.mem_singleton]; omega) (show rngListed 0x2417b = _ from rfl) (by
        simp [X86Routine.execute,c6,c5,c4,c3,c2,c1,putByte,byteReg,put,write,ret,BitVec.toNat_ofNat,Nat.mod_eq_of_lt resume.isLt])
    exact X86Routine.Prefix.nil _
  rw [show 7 = 7+0 from rfl,path.run 0]
  simp [X86Routine.run,randomEnd,c6,c5,c4,c3,c2,c1,putByte,byteReg,put,write]
  funext r
  by_cases h0 : r=0 <;> by_cases h4 : r=4 <;> simp_all [write]


end Doom.Proofs.RandomReturn
