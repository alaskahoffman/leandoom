import Doom.Proofs.OriginalLineSetup
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace Doom.Proofs.E1M1LineSetup
open Verification X86 X86Memory X86Control BlockSummary OriginalLineSetup

def joinedBytes (metadata slope vertices delta horizontal vertical copy cache advance : List UInt8) : X86Routine.Program := fun pc =>
  if (0x2e29a≤pc ∧ pc<0x2e2b2) ∨ (0x2e2ec≤pc ∧ pc<0x2e326) then
    bytesProgram metadata slope pc
  else E1M1LineGeometry.joinedBytes vertices delta horizontal vertical copy cache advance pc
def program := joinedBytes metadataBytes slopeBytes OriginalLineGeometry.verticesBytes
  OriginalLineGeometry.deltaBytes OriginalLineGeometry.horizontalBytes OriginalLineGeometry.verticalBytes
  OriginalLineLoad.copyBytes OriginalLineCache.cacheBytes OriginalLineLoad.advanceBytes

theorem local_agrees (pc : Nat) (h : OriginalLineSetup.program pc≠none) :
    program pc=OriginalLineSetup.program pc := by
  have within : (0x2e29a≤pc ∧ pc<0x2e2b2) ∨ (0x2e2ec≤pc ∧ pc<0x2e326) := by
    by_cases a : 0x2e29a≤pc ∧ pc<0x2e2b2
    · exact Or.inl a
    · by_cases b : 0x2e2ec≤pc ∧ pc<0x2e326
      · exact Or.inr b
      · simp [OriginalLineSetup.program,bytesProgram,a,b] at h
  simp [program,joinedBytes,within,OriginalLineSetup.program]
theorem geometry_agrees (pc : Nat) (h : E1M1LineGeometry.program pc≠none) :
    program pc=E1M1LineGeometry.program pc := by
  have outside : ¬((0x2e29a≤pc ∧ pc<0x2e2b2) ∨ (0x2e2ec≤pc ∧ pc<0x2e326)) := by
    intro inside
    have a : ¬(0x2e2b2≤pc ∧ pc<0x2e2d6) := by omega
    have b : ¬(0x2e2d6≤pc ∧ pc<0x2e2ec) := by omega
    have c : ¬(0x2e326≤pc ∧ pc<0x2e33d) := by omega
    have d : ¬(0x2e33d≤pc ∧ pc<0x2e358) := by omega
    have lt : pc<0x2e358 := by omega
    simp only [E1M1LineGeometry.program,E1M1LineGeometry.joinedBytes,if_pos lt,
      OriginalLineGeometry.bytesProgram,if_neg a,if_neg b,if_neg c,if_neg d,ne_eq,not_true_eq_false] at h
  simp [program,joinedBytes,outside,E1M1LineGeometry.program]

def prepared (s : X86Memory.State) := OriginalLineGeometry.prepared (metadata s)
def selected (s : X86Memory.State) := OriginalLineSetup.selected (prepared s).core

/-- Metadata and geometry execute continuously, with no memory reset. -/
theorem preparation_path (s : X86Memory.State) (f : Option Flags) :
    ∃ n≤24, X86Routine.Prefix program [] n ⟨s,f,0x2e29a⟩ (prepared s) := by
  obtain ⟨a,ha,pa,_⟩ := X86Routine.run_path (metadata_execution s f)
  have pa := pa.transfer program [] local_agrees (by simp)
  obtain ⟨b,hb,pb,_⟩ := X86Routine.run_path (OriginalLineGeometry.prefix_execution (metadata s) f)
  have agree (pc : Nat) (h : OriginalLineGeometry.program pc≠none) :
      program pc=OriginalLineGeometry.program pc := by
    rw [geometry_agrees pc (by rw [E1M1LineGeometry.geometry_agrees pc h]; exact h),
      E1M1LineGeometry.geometry_agrees pc h]
  have pb := pb.transfer program [] agree (by simp)
  exact ⟨a+b,by omega,OriginalGroupBounds.prefix_join pa pb⟩

/-- On diagonals this prefix stops at the actual FixedDiv entry, with CALL's
stack store included. It does not assume or skip the callee. -/
theorem selection_path (s : X86Memory.State) (f : Option Flags) :
    ∃ n≤33, X86Routine.Prefix program [] n ⟨s,f,0x2e29a⟩ (selected s) := by
  obtain ⟨a,ha,pa⟩ := preparation_path s f
  obtain ⟨b,hb,pb,_⟩ := X86Routine.run_path (selection_execution (prepared s).core (prepared s).flags)
  have pb := pb.transfer program [] local_agrees (by simp)
  exact ⟨a+b,by omega,OriginalGroupBounds.prefix_join pa pb⟩

/-- The complete iteration for axis-aligned (including degenerate) lines.
A Prefix is used because the loop's entry is also its back-edge destination. -/
theorem axis_iteration (s : X86Memory.State) (f : Option Flags)
    (axis : dx (prepared s).core=0 ∨ dy (prepared s).core=0) :
    ∃ n≤75, X86Routine.Prefix program [] n ⟨s,f,0x2e29a⟩
      (E1M1LineGeometry.result (selected s).core) ∧
      (E1M1LineGeometry.result (selected s).core).pc∈[0x2e29a,0x2e3c1] := by
  obtain ⟨a,ha,pa⟩ := selection_path s f
  have pc : (selected s).pc=0x2e326 := (axis_classification (prepared s).core axis).1
  obtain ⟨b,hb,pb,last⟩ := X86Routine.run_path
    (E1M1LineGeometry.joined_execution (selected s).core (selected s).flags)
  have pb := pb.transfer program [] geometry_agrees (by simp)
  have same : (⟨(selected s).core,(selected s).flags,0x2e326⟩ : X86Control.State)=selected s := by
    rw [←pc]
  rw [same] at pb
  exact ⟨a+b,by omega,OriginalGroupBounds.prefix_join pa pb,last⟩

/-- Returned quotient classification is joined to bounds, cache writes and
loop advance. The separate FixedDiv call/return proof is still required. -/
theorem returned_suffix (s : X86Memory.State) (f : Option Flags) :
    ∃ n≤46, X86Routine.Prefix program [] n ⟨s,f,0x2e312⟩
      (E1M1LineGeometry.result (classified s).core) ∧
      (E1M1LineGeometry.result (classified s).core).pc∈[0x2e29a,0x2e3c1] := by
  obtain ⟨a,ha,pa,_⟩ := X86Routine.run_path (classification_execution s f)
  have pa := pa.transfer program [] local_agrees (by simp)
  obtain ⟨b,hb,pb,last⟩ := X86Routine.run_path
    (E1M1LineGeometry.joined_execution (classified s).core (classified s).flags)
  have pb := pb.transfer program [] geometry_agrees (by simp)
  exact ⟨a+b,by omega,OriginalGroupBounds.prefix_join pa pb,last⟩

end Doom.Proofs.E1M1LineSetup
