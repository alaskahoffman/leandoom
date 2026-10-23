import Doom.Proofs.OriginalDivMemory
import Doom.Proofs.E1M1LineSetup
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
namespace Doom.Proofs.E1M1LineIteration
open Verification X86 X86Memory X86Control BlockSummary

def joinedBytes (division metadata slope vertices delta horizontal vertical copy cache advance : List UInt8) : X86Routine.Program := fun pc =>
  if pc<0x2e29a then OriginalDivMemory.bytesProgram division pc
  else E1M1LineSetup.joinedBytes metadata slope vertices delta horizontal vertical copy cache advance pc
def program := joinedBytes Doom19.fixedDivBytes OriginalLineSetup.metadataBytes OriginalLineSetup.slopeBytes
  OriginalLineGeometry.verticesBytes OriginalLineGeometry.deltaBytes OriginalLineGeometry.horizontalBytes
  OriginalLineGeometry.verticalBytes OriginalLineLoad.copyBytes OriginalLineCache.cacheBytes OriginalLineLoad.advanceBytes

theorem division_agrees (pc : Nat) (h : OriginalDivMemory.program pc≠none) :
    program pc=OriginalDivMemory.program pc := by
  have within : 0x1d180≤pc ∧ pc<0x1d1c1 := by
    by_cases h' : 0x1d180≤pc ∧ pc<0x1d1c1
    · exact h'
    · simp [OriginalDivMemory.program,OriginalDivMemory.bytesProgram,h'] at h
  simp [program,joinedBytes,show pc<0x2e29a from by omega,OriginalDivMemory.program]

theorem setup_agrees (pc : Nat) (h : E1M1LineSetup.program pc≠none) :
    program pc=E1M1LineSetup.program pc := by
  have outside : ¬pc<0x2e29a := by
    intro lt
    have a : ¬((0x2e29a≤pc ∧ pc<0x2e2b2) ∨ (0x2e2ec≤pc ∧ pc<0x2e326)) := by omega
    have b : pc<0x2e358 := by omega
    have c : ¬(0x2e2b2≤pc ∧ pc<0x2e2d6) := by omega
    have d : ¬(0x2e2d6≤pc ∧ pc<0x2e2ec) := by omega
    have e : ¬(0x2e326≤pc ∧ pc<0x2e33d) := by omega
    have f : ¬(0x2e33d≤pc ∧ pc<0x2e358) := by omega
    simp only [E1M1LineSetup.program,E1M1LineSetup.joinedBytes,if_neg a,
      E1M1LineGeometry.joinedBytes,if_pos b,OriginalLineGeometry.bytesProgram,
      if_neg c,if_neg d,if_neg e,if_neg f,ne_eq,not_true_eq_false] at h
  simp [program,joinedBytes,outside,E1M1LineSetup.program]

def Axis (s : X86Memory.State) : Prop :=
  OriginalLineSetup.dx (E1M1LineSetup.prepared s).core=0 ∨ OriginalLineSetup.dy (E1M1LineSetup.prepared s).core=0
instance (s : X86Memory.State) : Decidable (Axis s) := inferInstanceAs (Decidable (_∨_))
def Safe (s : X86Memory.State) : Prop := ¬Axis s → OriginalDivMemory.Safe (E1M1LineSetup.selected s).core
def result (s : X86Memory.State) :=
  if Axis s then E1M1LineGeometry.result (E1M1LineSetup.selected s).core
  else E1M1LineGeometry.result (OriginalLineSetup.classified
    (OriginalDivMemory.result (E1M1LineSetup.selected s).core).core).core

theorem diagonal_return (s : X86Memory.State) (axis : ¬Axis s) :
    (E1M1LineSetup.selected s).pc=0x1d180 ∧
    (OriginalDivMemory.result (E1M1LineSetup.selected s).core).pc=0x2e312 := by
  have x : OriginalLineSetup.dx (E1M1LineSetup.prepared s).core≠0 := fun h => axis (Or.inl h)
  have y : OriginalLineSetup.dy (E1M1LineSetup.prepared s).core≠0 := fun h => axis (Or.inr h)
  have call := OriginalLineSetup.diagonal_call (E1M1LineSetup.prepared s).core x y
  refine ⟨call.1,?_⟩
  rw [(OriginalDivMemory.restored_registers (E1M1LineSetup.selected s).core).2.2.2.2]
  change (load32 (OriginalLineSetup.selected (E1M1LineSetup.prepared s).core).core.memory
    ((OriginalLineSetup.selected (E1M1LineSetup.prepared s).core).core.regs 4)).toNat=0x2e312
  rw [call.2.2.2.1,call.2.2.2.2]
  rfl

/-- One continuous original iteration, including diagonal FixedDiv's body,
stack writes, pops and RET. The arithmetic-success condition is explicit. -/
theorem iteration (s : X86Memory.State) (f : Option Flags) (safe : Safe s) :
    ∃ n≤104, X86Routine.Prefix program [] n ⟨s,f,0x2e29a⟩ (result s) ∧
      (result s).pc∈[0x2e29a,0x2e3c1] := by
  by_cases axis : Axis s
  · obtain ⟨n,hn,path,last⟩ := E1M1LineSetup.axis_iteration s f axis
    have path := path.transfer program [] setup_agrees (by simp)
    exact ⟨n,by omega,by simpa only [result,if_pos axis] using path,by simpa only [result,if_pos axis] using last⟩
  · obtain ⟨a,ha,pa⟩ := E1M1LineSetup.selection_path s f
    have pa := pa.transfer program [] setup_agrees (by simp)
    obtain ⟨b,hb,pb⟩ := OriginalDivMemory.execution_path (E1M1LineSetup.selected s).core
      (E1M1LineSetup.selected s).flags (safe axis)
    have pb := pb.transfer program [] division_agrees (by simp)
    have pcs := diagonal_return s axis
    have start : (⟨(E1M1LineSetup.selected s).core,(E1M1LineSetup.selected s).flags,0x1d180⟩ : X86Control.State)=E1M1LineSetup.selected s := by rw [←pcs.1]
    rw [start] at pb
    obtain ⟨c,hc,pc,last⟩ := E1M1LineSetup.returned_suffix
      (OriginalDivMemory.result (E1M1LineSetup.selected s).core).core
      (OriginalDivMemory.result (E1M1LineSetup.selected s).core).flags
    have pc := pc.transfer program [] setup_agrees (by simp)
    have seam : (⟨(OriginalDivMemory.result (E1M1LineSetup.selected s).core).core,
      (OriginalDivMemory.result (E1M1LineSetup.selected s).core).flags,0x2e312⟩ : X86Control.State)=
      OriginalDivMemory.result (E1M1LineSetup.selected s).core := by rw [←pcs.2]
    rw [seam] at pc
    exact ⟨a+b+c,by omega,by simpa only [result,if_neg axis] using
      OriginalGroupBounds.prefix_join (OriginalGroupBounds.prefix_join pa pb) pc,
      by simpa only [result,if_neg axis] using last⟩
end Doom.Proofs.E1M1LineIteration
