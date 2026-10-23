import Doom.Proofs.E1M1OpeningHeights
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1800000
namespace Doom.Proofs.E1M1AimOpening
open Verification X86 X86Memory X86Control BlockSummary
attribute [local irreducible] load32 store32

def program : X86Routine.Program := fun pc =>
  match OriginalAimOpening.program pc with
  | some op => some op
  | none => match OriginalAimGuard.program pc with
    | some op => some op
    | none => E1M1NoiseOpening.program pc

theorem contains_call (pc : Nat) (h : OriginalAimOpening.program pc≠none) :
    program pc=OriginalAimOpening.program pc := by
  unfold program
  cases eq : OriginalAimOpening.program pc <;> simp_all

theorem contains_helper (pc : Nat) (h : E1M1NoiseOpening.program pc≠none) :
    program pc=E1M1NoiseOpening.program pc := by
  have absent : OriginalAimOpening.program pc=none := by
    by_cases inside : 0x2b77f≤pc ∧ pc<0x2b797
    · have all : ∀ i : Fin 24, E1M1NoiseOpening.program (0x2b77f+i.val)=none := by decide
      have eq : 0x2b77f+(pc-0x2b77f)=pc := by omega
      exact False.elim (h (by simpa only [eq] using all ⟨pc-0x2b77f,by omega⟩))
    · simp [OriginalAimOpening.program,OriginalAimOpening.bytesProgram,inside]
  have guard : OriginalAimGuard.program pc=none := by
    by_cases a : 0x2b760≤pc ∧ pc<0x2b77f
    · have all : ∀ i : Fin 31, E1M1NoiseOpening.program (0x2b760+i.val)=none := by decide
      have eq : 0x2b760+(pc-0x2b760)=pc := by omega
      exact False.elim (h (by simpa only [eq] using all ⟨pc-0x2b760,by omega⟩))
    · by_cases b : 0x2b8d2≤pc ∧ pc<0x2b8db
      · have all : ∀ i : Fin 9, E1M1NoiseOpening.program (0x2b8d2+i.val)=none := by decide
        have eq : 0x2b8d2+(pc-0x2b8d2)=pc := by omega
        exact False.elim (h (by simpa only [eq] using all ⟨pc-0x2b8d2,by omega⟩))
      · simp [OriginalAimGuard.program,OriginalAimGuard.bytesProgram,a,b]
  simp [program,absent,guard]

theorem contains_guard (pc : Nat) (h : OriginalAimGuard.program pc≠none) :
    program pc=OriginalAimGuard.program pc := by
  have absent : OriginalAimOpening.program pc=none := by
    by_cases inside : 0x2b77f≤pc ∧ pc<0x2b797
    · have a : ¬(0x2b760≤pc ∧ pc<0x2b77f) := by omega
      have b : ¬(0x2b8d2≤pc ∧ pc<0x2b8db) := by omega
      exact False.elim (h (by simp [OriginalAimGuard.program,OriginalAimGuard.bytesProgram,a,b]))
    · simp [OriginalAimOpening.program,OriginalAimOpening.bytesProgram,inside]
  unfold program
  rw [absent]
  cases eq : OriginalAimGuard.program pc <;> simp_all

def opened (s : X86Memory.State) := E1M1NoiseOpening.result (OriginalAimOpening.called s)
def result (s : X86Memory.State) := OriginalAimOpening.gate (opened s).core
/-- Static protection of the helper's return word and its saved ECX/EDX from
opening-global stores, expressed at the actual caller entry. -/
def Safe (s : X86Memory.State) : Prop :=
  E1M1NoiseLedger.Protect [s.regs 4-4,s.regs 4-12,s.regs 4-16]
    E1M1NoiseLineProgress.openingGlobals

theorem helper_return (s : X86Memory.State) (safe : Safe s) :
    (opened s).pc=0x2b786 ∧ (opened s).core.regs 1=s.regs 1 ∧
    (opened s).core.regs 2=s.regs 2 ∧ (opened s).core.regs 4=s.regs 4 := by
  have h := E1M1NoiseOpeningFrame.restored (OriginalAimOpening.called s) (by
    simpa [E1M1NoiseOpeningFrame.Safe,Safe,OriginalAimOpening.called,OriginalAimOpening.argument,
      X86Routine.pushWord,put,write,BitVec.sub_sub] using safe)
  have sp := E1M1NoiseFootprint.opening_sp (OriginalAimOpening.called s)
  simpa [opened,OriginalAimOpening.called,OriginalAimOpening.argument,X86Routine.pushWord,put,write,load_store,BitVec.sub_add_cancel] using
    And.intro h.2.2 (And.intro h.1 (And.intro h.2.1 sp))

/-- The actual CALL, entire existing opening helper, real RET, and signed
bottom/top branch. No helper result or return address is assumed. -/
theorem execution (s : X86Memory.State) (f : Option Flags) (safe : Safe s) :
    ∃ n, n≤36 ∧ X86CodeMemory.Prefix FloorCaller.cm program [] n
      ⟨s,f,0x2b77f⟩ (result s) := by
  have p := (X86CodeMemory.lift_success (OriginalAimOpening.call_execution s f) FloorCaller.cm).transfer
    program [] contains_call (by simp)
  obtain ⟨n,hn,q⟩ := E1M1NoiseOpening.opening_execution (OriginalAimOpening.called s) f
  have q := q.transfer program [] contains_helper (by simp)
  have r := (X86CodeMemory.lift_success (OriginalAimOpening.gate_execution (opened s).core (opened s).flags)
    FloorCaller.cm).transfer program [] contains_call (by simp)
  rw [OriginalPathXStep.at_pc _ _ (helper_return s safe).1] at r
  exact ⟨2+n+3,by omega,E1M1PspriteStep.prefix_trans (E1M1PspriteStep.prefix_trans p q) r⟩

/-- The branch compares signed heights directly, rather than a wrapping
subtraction of them. -/
theorem decision (s : X86Memory.State) :
    (result s).pc=if (OriginalAimOpening.top (opened s).core).toInt ≤
      (OriginalAimOpening.bottom (opened s).core).toInt then 0x2b8d2 else 0x2b797 := rfl

def CallerSafe (s : X86Memory.State) : Prop :=
  E1M1NoiseLedger.Protect [s.regs 4-(28#32),s.regs 4-(36#32),s.regs 4-(40#32)]
    E1M1NoiseLineProgress.openingGlobals

/-- Continue directly from the reached aim callback through its prologue,
type and wall guards, actual opening helper, and closed-opening decision. -/
theorem from_callback (s : X86Memory.State) (f : Option Flags) (hit : Collision.Intercept) (pointer : Word)
    (record : OriginalLineFinish.RecordAt s.memory (s.regs 0) hit pointer)
    (isLine : hit.isLine=true)
    (tagSafe : E1M1AimWall.Safe (s.regs 4) (s.regs 0+4))
    (pointerSafe : E1M1AimWall.Safe (s.regs 4) (s.regs 0+8))
    (flagsSafe : E1M1AimWall.Safe (s.regs 4) (pointer+16))
    (two : s.memory (pointer+16) &&& (4#8)≠0) (helperSafe : CallerSafe s) :
    ∃ n, n≤48 ∧ X86CodeMemory.Prefix FloorCaller.cm program [] n ⟨s,f,0x2b760⟩
      (result (OriginalAimGuard.lineCore (OriginalAimGuard.prepared s))) := by
  have pc : (OriginalAimGuard.entry s).pc=0x2b772 := by
    rw [E1M1AimWall.entry_record s hit pointer record tagSafe,isLine]; rfl
  have ptr : OriginalAimGuard.line (OriginalAimGuard.prepared s)=pointer := by
    change load32 (OriginalAimGuard.saved s).memory (s.regs 0+8)=pointer
    rw [E1M1AimWall.saved_frame s _ pointerSafe]; exact record.2.2
  have bits : OriginalAimGuard.bits (OriginalAimGuard.prepared s)≠(0#8) := by
    unfold OriginalAimGuard.bits
    rw [ptr]
    change (OriginalAimGuard.saved s).memory (pointer+16) &&& (4#8)≠0
    rw [E1M1AimWall.saved_byte s _ flagsSafe]; exact two
  have gatePc : (OriginalAimGuard.lineGate (OriginalAimGuard.prepared s)).pc=0x2b77f := by
    simp [OriginalAimGuard.lineGate,bits]
  have p := (X86CodeMemory.lift_success (OriginalAimGuard.entry_execution s f) FloorCaller.cm).transfer
    program [] contains_guard (by simp)
  have q := (X86CodeMemory.lift_success (OriginalAimGuard.line_execution (OriginalAimGuard.prepared s)
    (OriginalAimGuard.entry s).flags) FloorCaller.cm).transfer program [] contains_guard (by simp)
  change X86CodeMemory.Prefix FloorCaller.cm program [] 3
    ⟨(OriginalAimGuard.entry s).core,(OriginalAimGuard.entry s).flags,0x2b772⟩ _ at q
  rw [OriginalPathXStep.at_pc _ _ pc] at q
  have safe : Safe (OriginalAimGuard.lineCore (OriginalAimGuard.prepared s)) := by
    simpa [Safe,CallerSafe,OriginalAimGuard.lineCore,OriginalAimGuard.prepared,OriginalAimGuard.saved,
      OriginalAimGuard.save6,OriginalAimGuard.save5,OriginalAimGuard.save4,OriginalAimGuard.save3,
      OriginalAimGuard.save2,OriginalAimGuard.save1,X86Routine.pushWord,put,write,BitVec.sub_sub] using helperSafe
  obtain ⟨n,hn,r⟩ := execution (OriginalAimGuard.lineCore (OriginalAimGuard.prepared s))
    (OriginalAimGuard.lineGate (OriginalAimGuard.prepared s)).flags safe
  change X86CodeMemory.Prefix FloorCaller.cm program [] n
    ⟨(OriginalAimGuard.lineGate (OriginalAimGuard.prepared s)).core,
      (OriginalAimGuard.lineGate (OriginalAimGuard.prepared s)).flags,0x2b77f⟩ _ at r
  rw [OriginalPathXStep.at_pc _ _ gatePc] at r
  exact ⟨9+3+n,by omega,E1M1PspriteStep.prefix_trans (E1M1PspriteStep.prefix_trans p q) r⟩

/-- Substitute the sector heights read by the real helper into the actual aim
branch. These are helper-entry representation contracts, not output premises. -/
theorem height_decision (s : X86Memory.State) (front back ff fc bf bc : Word)
    (safe : E1M1OpeningHeights.Safe (OriginalAimOpening.called s) front back)
    (side : load16 (OriginalAimOpening.called s).memory (s.regs 1+(24#32))≠0xffff)
    (frontPtr : load32 (OriginalAimOpening.called s).memory (s.regs 1+(46#32))=front)
    (backPtr : load32 (OriginalAimOpening.called s).memory (s.regs 1+(50#32))=back)
    (frontFloor : load32 (OriginalAimOpening.called s).memory front=ff)
    (frontCeiling : load32 (OriginalAimOpening.called s).memory (front+(4#32))=fc)
    (backFloor : load32 (OriginalAimOpening.called s).memory back=bf)
    (backCeiling : load32 (OriginalAimOpening.called s).memory (back+(4#32))=bc) :
    (result s).pc=if (if bc.toInt≤fc.toInt then bc else fc).toInt ≤
      (if ff.toInt≤bf.toInt then bf else ff).toInt then 0x2b8d2 else 0x2b797 := by
  have arg : (OriginalAimOpening.called s).regs 0=s.regs 1 := by
    simp [OriginalAimOpening.called,OriginalAimOpening.argument,X86Routine.pushWord,put,write]
  have h := E1M1OpeningHeights.heights (OriginalAimOpening.called s) front back ff fc bf bc safe
    (by simpa only [arg] using side) (by simpa only [arg] using frontPtr)
    (by simpa only [arg] using backPtr) frontFloor frontCeiling backFloor backCeiling
  change (if (load32 (opened s).core.memory (0x2c034#32)).toInt ≤
    (load32 (opened s).core.memory (0x2c030#32)).toInt then _ else _)=_
  unfold opened
  rw [h.1,h.2]
end Doom.Proofs.E1M1AimOpening
