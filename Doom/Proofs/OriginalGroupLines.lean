import Doom.Proofs.OriginalSideLoader
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1800000
set_option linter.unusedSimpArgs false
namespace Doom.Proofs.OriginalGroupLines
open Verification X86 X86Memory X86Control BlockSummary E1M1NoiseImage
def groupBytes : List UInt8 := [0x31,0xff,0x8b,0xd,0x20,0xc1,0x2,0x0,0x8b,0x1d,0x34,0xc1,0x2,0x0,0x89,0x75,0x52,0x85,0xdb,0x7e,0x39,0x3b,0x69,0x2e,0x74,0x5,0x3b,0x69,0x32,0x75,0x22,0x89,0xe]
def bytesProgram (group : List UInt8) : X86Routine.Program := fun pc =>
  if 0x2e661≤pc ∧ pc<0x2e682 then X86Routine.decodeAt group (pc-0x2e661) else none
def program := bytesProgram groupBytes
def listed : X86Routine.Program
  | 0x2e661 => some (.xorRegister 7 7,2)
  | 0x2e663 => some (.control (.block (.load 1 ⟨none,none,0,0x2c120⟩)),6)
  | 0x2e669 => some (.control (.block (.load 3 ⟨none,none,0,0x2c134⟩)),6)
  | 0x2e66f => some (.control (.block (.store ⟨some 5,none,0,82⟩ 6)),3)
  | 0x2e672 => some (.control (.testWord 3 3),2)
  | 0x2e674 => some (.jumpSigned 1 57,2)
  | 0x2e676 => some (.control (.cmpMemory 5 ⟨some 1,none,0,46⟩),3)
  | 0x2e679 => some (.control (.jumpZero true 5),2)
  | 0x2e67b => some (.control (.cmpMemory 5 ⟨some 1,none,0,50⟩),3)
  | 0x2e67e => some (.control (.jumpZero false 34),2)
  | 0x2e680 => some (.control (.block (.store ⟨some 6,none,0,0⟩ 1)),2)
  | _ => none
theorem decoded (pc : Nat) (h : listed pc≠none) : program pc=listed pc := by
  fun_cases listed pc <;> simp_all [listed] <;> decide

/-- Counts and linedef base are loaded before the sector-array pointer is written. -/
def prepared (s : X86Memory.State) : X86Memory.State :=
  let t := put s 7 0
  let t := put t 1 (load32 s.memory 0x2c120)
  let t := put t 3 (load32 s.memory 0x2c134)
  { t with memory := store32 s.memory (s.regs 5+82) (s.regs 6) }
def entry (s : X86Memory.State) : X86Control.State :=
  ⟨prepared s,some (logical32 (load32 s.memory 0x2c134)),
    if (load32 s.memory 0x2c134).toInt≤0 then 0x2e6af else 0x2e676⟩
def front (s : X86Memory.State) : Word := load32 s.memory (s.regs 1+46)
def back (s : X86Memory.State) : Word := load32 s.memory (s.regs 1+50)
def accepts (sector front back : Word) : Bool := sector==front || sector==back
def emitted (s : X86Memory.State) (f : Option Flags) : X86Control.State :=
  ⟨{s with memory := store32 s.memory (s.regs 6) (s.regs 1)},f,0x2e682⟩
def selected (s : X86Memory.State) : X86Control.State :=
  if s.regs 5=front s then emitted s (some (compare32 (s.regs 5) (front s)))
  else if s.regs 5=back s then emitted s (some (compare32 (s.regs 5) (back s)))
  else ⟨s,some (compare32 (s.regs 5) (back s)),0x2e6a2⟩
@[local simp] private theorem step_2e661 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2e676,0x2e6af] (n+1) ⟨s,f,0x2e661⟩ =
      (X86Routine.execute (.xorRegister 7 7) ⟨s,f,0x2e663⟩).bind (X86Routine.run listed [0x2e676,0x2e6af] n) := by rfl
@[local simp] private theorem step_2e663 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2e676,0x2e6af] (n+1) ⟨s,f,0x2e663⟩ =
      (X86Routine.execute (.control (.block (.load 1 ⟨none,none,0,0x2c120⟩))) ⟨s,f,0x2e669⟩).bind (X86Routine.run listed [0x2e676,0x2e6af] n) := by rfl
@[local simp] private theorem step_2e669 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2e676,0x2e6af] (n+1) ⟨s,f,0x2e669⟩ =
      (X86Routine.execute (.control (.block (.load 3 ⟨none,none,0,0x2c134⟩))) ⟨s,f,0x2e66f⟩).bind (X86Routine.run listed [0x2e676,0x2e6af] n) := by rfl
@[local simp] private theorem step_2e66f (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2e676,0x2e6af] (n+1) ⟨s,f,0x2e66f⟩ =
      (X86Routine.execute (.control (.block (.store ⟨some 5,none,0,82⟩ 6))) ⟨s,f,0x2e672⟩).bind (X86Routine.run listed [0x2e676,0x2e6af] n) := by rfl
@[local simp] private theorem step_2e672 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2e676,0x2e6af] (n+1) ⟨s,f,0x2e672⟩ =
      (X86Routine.execute (.control (.testWord 3 3)) ⟨s,f,0x2e674⟩).bind (X86Routine.run listed [0x2e676,0x2e6af] n) := by rfl
@[local simp] private theorem step_2e674 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2e676,0x2e6af] (n+1) ⟨s,f,0x2e674⟩ =
      (X86Routine.execute (.jumpSigned 1 57) ⟨s,f,0x2e676⟩).bind (X86Routine.run listed [0x2e676,0x2e6af] n) := by rfl
@[local simp] private theorem stop_2e676 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2e676,0x2e6af] n ⟨s,f,0x2e676⟩=some ⟨s,f,0x2e676⟩ := by cases n <;> rfl
@[local simp] private theorem stop_2e6af (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2e676,0x2e6af] n ⟨s,f,0x2e6af⟩=some ⟨s,f,0x2e6af⟩ := by cases n <;> rfl
theorem entry_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.run program [0x2e676,0x2e6af] 6 ⟨s,f,0x2e661⟩=some (entry s) := by
  have run : X86Routine.run listed [0x2e676,0x2e6af] 6 ⟨s,f,0x2e661⟩=some (entry s) := by
    by_cases h : (load32 s.memory (0x2c134#32)).toInt≤0
    all_goals simp_all [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,
      X86Block.Address.eval,X86.execute,blockPreservesFlags,prepared,entry,selected,emitted,front,back,
      cmp32_zero,PlayerHeight.logical_le,put,write,BitVec.add_assoc,h,-BitVec.toInt_add]
    all_goals
      have negative : ¬(load32 s.memory (0x2c134#32)).toInt≤0 := by omega
      simp [negative]
  rw [X86Routine.run_sound program listed decoded _ _ _ (by rw [run]; simp),run]
@[local simp] private theorem step_2e676 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2e682,0x2e6a2] (n+1) ⟨s,f,0x2e676⟩ =
      (X86Routine.execute (.control (.cmpMemory 5 ⟨some 1,none,0,46⟩)) ⟨s,f,0x2e679⟩).bind (X86Routine.run listed [0x2e682,0x2e6a2] n) := by rfl
@[local simp] private theorem step_2e679 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2e682,0x2e6a2] (n+1) ⟨s,f,0x2e679⟩ =
      (X86Routine.execute (.control (.jumpZero true 5)) ⟨s,f,0x2e67b⟩).bind (X86Routine.run listed [0x2e682,0x2e6a2] n) := by rfl
@[local simp] private theorem step_2e67b (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2e682,0x2e6a2] (n+1) ⟨s,f,0x2e67b⟩ =
      (X86Routine.execute (.control (.cmpMemory 5 ⟨some 1,none,0,50⟩)) ⟨s,f,0x2e67e⟩).bind (X86Routine.run listed [0x2e682,0x2e6a2] n) := by rfl
@[local simp] private theorem step_2e67e (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2e682,0x2e6a2] (n+1) ⟨s,f,0x2e67e⟩ =
      (X86Routine.execute (.control (.jumpZero false 34)) ⟨s,f,0x2e680⟩).bind (X86Routine.run listed [0x2e682,0x2e6a2] n) := by rfl
@[local simp] private theorem step_2e680 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2e682,0x2e6a2] (n+1) ⟨s,f,0x2e680⟩ =
      (X86Routine.execute (.control (.block (.store ⟨some 6,none,0,0⟩ 1))) ⟨s,f,0x2e682⟩).bind (X86Routine.run listed [0x2e682,0x2e6a2] n) := by rfl
@[local simp] private theorem stop_2e682 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2e682,0x2e6a2] n ⟨s,f,0x2e682⟩=some ⟨s,f,0x2e682⟩ := by cases n <;> rfl
@[local simp] private theorem stop_2e6a2 (s : X86Memory.State) (f : Option Flags) (n : Nat) :
    X86Routine.run listed [0x2e682,0x2e6a2] n ⟨s,f,0x2e6a2⟩=some ⟨s,f,0x2e6a2⟩ := by cases n <;> rfl
theorem selection_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.run program [0x2e682,0x2e6a2] 5 ⟨s,f,0x2e676⟩=some (selected s) := by
  have run : X86Routine.run listed [0x2e682,0x2e6a2] 5 ⟨s,f,0x2e676⟩=some (selected s) := by
    by_cases hf : s.regs 5=front s <;> by_cases hb : s.regs 5=back s
    all_goals simp [front,back] at hf hb
    all_goals simp_all [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,
      X86Block.Address.eval,X86.execute,blockPreservesFlags,prepared,entry,selected,emitted,front,back,
      cmp32_zero,PlayerHeight.logical_le,put,write,BitVec.add_assoc,hf,hb,-BitVec.toInt_add]
  rw [X86Routine.run_sound program listed decoded _ _ _ (by rw [run]; simp),run]

/-- The sector's array base is a real loader store, not an assumed MapRep field. -/
theorem entry_patch (s : X86Memory.State) :
    (entry s).core.memory=applyPatch (word (s.regs 5+82) (s.regs 6)) s.memory := by
  simp [entry,prepared,apply_word]
theorem entry_pointer (s : X86Memory.State) :
    load32 (entry s).core.memory (s.regs 5+82)=s.regs 6 := load_store _ _ _

def selectionPatch (s : X86Memory.State) : E1M1NoiseImage.Patch :=
  if accepts (s.regs 5) (front s) (back s) then word (s.regs 6) (s.regs 1) else []
theorem selection_patch (s : X86Memory.State) :
    (selected s).core.memory=applyPatch (selectionPatch s) s.memory := by
  by_cases hf : s.regs 5=front s <;> by_cases hb : s.regs 5=back s <;>
    simp_all [selected,emitted,selectionPatch,accepts,apply_word] <;> rfl
theorem selected_pointer (s : X86Memory.State)
    (member : accepts (s.regs 5) (front s) (back s)=true) :
    (selected s).pc=0x2e682 ∧ load32 (selected s).core.memory (s.regs 6)=s.regs 1 := by
  by_cases hf : s.regs 5=front s <;> by_cases hb : s.regs 5=back s <;>
    simp_all [accepts,selected,emitted,load_store]

-- The next theorem joins entry and selection without resetting flags, registers,
-- or memory. In particular selection observes the preceding pointer store.
def result (s : X86Memory.State) : X86Control.State :=
  if (entry s).pc=0x2e676 then selected (entry s).core else entry s
private theorem active (pc : Nat) (h : program pc≠none) : pc∉[0x2e682,0x2e6a2,0x2e6af] := by
  intro member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl|rfl|rfl <;> exact h (by decide)

theorem joined_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.run program [0x2e682,0x2e6a2,0x2e6af] 11 ⟨s,f,0x2e661⟩=some (result s) := by
  obtain ⟨n,hn,path,done⟩ := X86Routine.run_path (entry_execution s f)
  have path := path.transfer program [0x2e682,0x2e6a2,0x2e6af] (fun _ _ => rfl) active
  by_cases more : (entry s).pc=0x2e676
  · obtain ⟨k,hk,tail,last⟩ := X86Routine.run_path (selection_execution (entry s).core (entry s).flags)
    have tail := tail.transfer program [0x2e682,0x2e6a2,0x2e6af] (fun _ _ => rfl) active
    have eq : ⟨(entry s).core,(entry s).flags,0x2e676⟩=entry s := by rw [←more]
    rw [eq] at tail
    have stopped : X86Routine.run program [0x2e682,0x2e6a2,0x2e6af] 0 (selected (entry s).core)=some (selected (entry s).core) := by
      simp only [X86Routine.run]
      have member : (selected (entry s).core).pc∈[0x2e682,0x2e6a2,0x2e6af] := by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at last ⊢
        exact last.elim Or.inl (fun h => Or.inr (Or.inl h))
      simp [member]
    have finish := tail.finish stopped 5 (by omega)
    simpa [result,more] using path.finish finish 11 (by omega)
  · have pc : (entry s).pc=0x2e6af := by simpa [more] using done
    have finish : X86Routine.run program [0x2e682,0x2e6a2,0x2e6af] 0 (entry s)=some (entry s) := by simp [X86Routine.run,pc]
    simpa [result,more] using path.finish finish 11 (by omega)

open E1M1NoiseTopology
/-- Injectivity is restricted to the finite sector table, not all natural
numbers. Null denotes an absent back sector and cannot be a live sector. -/
structure SectorAddresses (a : Addresses) (n : Nat) : Prop where
  nonzero : ∀ i, i<n → a.sector i≠0
  distinct : ∀ i, i<n → ∀ j, j<n → a.sector i=a.sector j → i=j

def InRange (e : Line) (n : Nat) : Prop := e.front<n ∧ (e.backIndex≠65535 → e.back<n)
instance (e : Line) (n : Nat) : Decidable (InRange e n) := by unfold InRange; infer_instance
def backAddress (e : Line) (a : Addresses) : Word := if e.backIndex=65535 then 0 else a.sector e.back

theorem selection_rule (a : Addresses) (n : Nat) (layout : SectorAddresses a n)
    (e : Line) (valid : InRange e n) (i : Nat) (inside : i<n) :
    accepts (a.sector i) (a.sector e.front) (backAddress e a)=
      (e.front==i || (e.backIndex != 65535 && e.back==i)) := by
  have hf : a.sector i=a.sector e.front ↔ e.front=i :=
    ⟨fun h => (layout.distinct i inside e.front valid.1 h).symm,fun h => congrArg a.sector h.symm⟩
  have nonzero : a.sector i≠(0#32) := layout.nonzero i inside
  apply Bool.eq_iff_iff.mpr
  by_cases absent : e.backIndex=(65535#16)
  · simp [accepts,backAddress,absent,nonzero,hf]
  · have hb : a.sector i=a.sector e.back ↔ e.back=i :=
      ⟨fun h => (layout.distinct i inside e.back (valid.2 absent) h).symm,fun h => congrArg a.sector h.symm⟩
    simp [accepts,backAddress,absent,hf,hb]

/-- This proves equality of the ordered selection specifications. Execution of
all scan iterations and the intervening bounding-box calls is still separate. -/
theorem ordered_selection (t : Topology) (a : Addresses)
    (layout : SectorAddresses a t.sectors.length)
    (ranges : ∀ e∈t.lines, InRange e t.sectors.length) (grouped : t.Grouped)
    (i : Fin t.sectors.length) :
    (t.lines.filter fun e => accepts (a.sector i.val) (a.sector e.front) (backAddress e a)).map Line.index=t.sectors[i.val] := by
  rw [grouped i]
  congr 1
  apply List.filter_congr
  intro e he
  exact selection_rule a _ layout e (ranges e he) i.val i.isLt

/-- Per-line original execution is connected to the WAD grouping predicate.
The input representation describes pre-store memory, not the desired output. -/
theorem line_correspondence (s : X86Memory.State) (f : Option Flags)
    (a : Addresses) (n : Nat) (layout : SectorAddresses a n) (e : Line)
    (valid : InRange e n) (i : Nat) (inside : i<n)
    (sector : s.regs 5=a.sector i) (line : s.regs 1=a.line e.index)
    (frontRead : front s=a.sector e.front) (backRead : back s=backAddress e a) :
    ∃ out, X86Routine.run program [0x2e682,0x2e6a2] 5 ⟨s,f,0x2e676⟩=some out ∧
      out.core.memory=applyPatch
        (if e.front==i || (e.backIndex != 65535 && e.back==i) then word (s.regs 6) (a.line e.index) else []) s.memory := by
  refine ⟨selected s,selection_execution s f,?_⟩
  rw [selection_patch]
  simp only [selectionPatch,sector,frontRead,backRead,selection_rule a n layout e valid i inside,line]

end Doom.Proofs.OriginalGroupLines
