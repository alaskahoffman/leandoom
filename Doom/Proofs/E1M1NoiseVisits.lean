import Doom.Proofs.E1M1NoisePreservation
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 800000
namespace Doom.Proofs.E1M1NoiseVisits
open Verification X86 X86Memory X86Control BlockSummary

/-- The three relevant states of one sector during a fixed sound generation.
Unseen imposes no constraint on the old cost word. -/
inductive Mark where | unseen | blocked | clear deriving DecidableEq, Repr

def rank : Mark → Nat | .unseen => 2 | .blocked => 1 | .clear => 0
def blocks (b : Bool) : Word := if b then 1 else 0
def marked (b : Bool) : Mark := if b then .blocked else .clear
def admits : Mark → Bool → Bool
  | .unseen,_ => true
  | .blocked,b => !b
  | .clear,_ => false

def Rep (generation sector : Word) (m : Memory) : Mark → Prop
  | .unseen => load32 m (sector+(66#32))≠generation
  | .blocked => load32 m (sector+(66#32))=generation ∧ load32 m (sector+(18#32))=(2#32)
  | .clear => load32 m (sector+(66#32))=generation ∧ load32 m (sector+(18#32))=(1#32)

/-- Relation at the original gate, after the actual stack prologue. -/
structure GateInputs (s : X86Memory.State) (m : Mark) (b : Bool) : Prop where
  sector : s.regs 0=s.regs 3
  count : s.regs 1=blocks b
  mark : Rep (s.regs 2) (s.regs 3) s.memory m

/-- The exact signed original gate admits a fresh sector or a 2→1 improvement.
No alternate path-comparison algorithm is substituted for the instructions. -/
theorem gate_admits (s : X86Memory.State) (m : Mark) (b : Bool) (h : GateInputs s m b) :
    (NoiseAlert.gate s).pc=0x26f83 ↔ admits m b=true := by
  obtain ⟨sector,count,rep⟩ := h
  cases m with
  | unseen =>
    have old : s.regs 2≠load32 s.memory (s.regs 3+(66#32)) := Ne.symm rep
    cases b <;> simp [admits,NoiseAlert.gate,NoiseAlert.seen,sector,old]
  | blocked => cases b <;> simp_all [Rep,blocks,admits,NoiseAlert.gate,NoiseAlert.seen,NoiseAlert.previousCost,NoiseAlert.nextCost]
  | clear => cases b <;> simp_all [Rep,blocks,admits,NoiseAlert.gate,NoiseAlert.seen,NoiseAlert.previousCost,NoiseAlert.nextCost]

theorem admitted_decreases (m : Mark) (b : Bool) (h : admits m b=true) :
    rank (marked b)+1≤rank m := by
  cases m <;> cases b <;> simp_all [admits,marked,rank]

private theorem gate_memory (s : X86Memory.State) : (NoiseAlert.gate s).core.memory=s.memory := by
  unfold NoiseAlert.gate; split <;> rfl
private theorem gate_reg (s : X86Memory.State) (r : Reg) (h : r≠0) :
    (NoiseAlert.gate s).core.regs r=s.regs r := by
  unfold NoiseAlert.gate; split <;> simp [put,write,h]

/-- The real three-store update establishes the new mark. Keeping the global
generation equal to the gate's loaded EDX is explicit, because aliasing could
otherwise change it between reads. -/
theorem update_rep (s : X86Memory.State) (b : Bool)
    (count : s.regs 1=blocks b) (generation : load32 s.memory (0x13580#32)=s.regs 2) :
    Rep (s.regs 2) (s.regs 3) (NoiseAlert.updated (NoiseAlert.gate s).core).core.memory (marked b) := by
  have stamp := NoiseAlert.updated_stamp (NoiseAlert.gate s).core
  have cost := NoiseAlert.updated_cost (NoiseAlert.gate s).core
  simp only [gate_reg s 3 (by decide),gate_memory] at stamp cost
  simp only [NoiseAlert.nextCost,gate_reg s 1 (by decide),count] at cost
  cases b <;> simp_all [marked,blocks,Rep]

/-- A machine admission consumes at least one of this sector's two credits. -/
theorem machine_progress (s : X86Memory.State) (m : Mark) (b : Bool)
    (h : GateInputs s m b) (generation : load32 s.memory (0x13580#32)=s.regs 2)
    (enter : (NoiseAlert.gate s).pc=0x26f83) :
    Rep (s.regs 2) (s.regs 3) (NoiseAlert.updated (NoiseAlert.gate s).core).core.memory (marked b) ∧
    rank (marked b)+1≤rank m :=
  ⟨update_rep s b h.count generation,admitted_decreases m b ((gate_admits s m b h).mp enter)⟩

/-- Link the admission to the actual sector prefix's nonempty-loop endpoint.
The gate relation is supplied after the proved prologue, not assumed at RET. -/
theorem sector_more_progress (s : X86Memory.State) (m : Mark) (b : Bool)
    (h : GateInputs (NoiseAlert.prepared s) m b)
    (generation : load32 (NoiseAlert.prepared s).memory (0x13580#32)=(NoiseAlert.prepared s).regs 2)
    (more : (E1M1NoiseAlert.sectorResult s).pc=0x26fa6) :
    Rep ((NoiseAlert.prepared s).regs 2) ((NoiseAlert.prepared s).regs 3)
      (E1M1NoiseAlert.sectorResult s).core.memory (marked b) ∧ rank (marked b)+1≤rank m := by
  have enter : (NoiseAlert.gate (NoiseAlert.prepared s)).pc=0x26f83 := by
    simp only [E1M1NoiseAlert.sectorResult] at more
    split at more
    · assumption
    · have pc (t : X86Memory.State) : (NoiseAlert.gate t).pc=0x26f83 ∨ (NoiseAlert.gate t).pc=0x27011 := by
        simp only [NoiseAlert.gate]; split
        · exact Or.inl rfl
        · split
          · exact Or.inr rfl
          · exact Or.inl rfl
      have := pc (NoiseAlert.prepared s)
      omega
  simpa only [E1M1NoiseAlert.sectorResult,enter,ite_true] using machine_progress _ m b h generation enter

/-- The sound-block branch sends only zero or one to children, provided the
parent count is in that domain. A second blocking line never creates a child. -/
theorem child_count (s : X86Memory.State) (b : Bool) (count : s.regs 1=blocks b)
    (call : (NoiseTraversal.blockResult s).pc=0x26f60) :
    ∃ c : Bool, (NoiseTraversal.blockResult s).core.regs 2=blocks c ∧ (b=true → c=true) := by
  by_cases ordinary : NoiseTraversal.lineFlags s (64#8)=(0#8)
  · refine ⟨b,?_,fun h => h⟩
    simp [NoiseTraversal.blockResult,ordinary,NoiseTraversal.recursiveCall,X86Routine.pushWord,put,write,count]
  · cases b
    · refine ⟨true,?_,by simp⟩
      simp [NoiseTraversal.blockResult,ordinary,count,blocks,NoiseTraversal.recursiveCall,X86Routine.pushWord,put,write]
    · simp [NoiseTraversal.blockResult,ordinary,count,blocks] at call

/-- A finite ledger of distinct sectors. Its ordering is arbitrary and does not
assert a correspondence to the map until the memory relation is established. -/
def potential : List Mark → Nat
  | [] => 0
  | m::ms => rank m+potential ms

inductive Admission : List Mark → List Mark → Prop
  | here (m ms b) (allowed : admits m b=true) : Admission (m::ms) (marked b::ms)
  | there (m xs ys) (step : Admission xs ys) : Admission (m::xs) (m::ys)

theorem Admission.decreases {xs ys} (h : Admission xs ys) : potential ys+1≤potential xs := by
  induction h with
  | here m ms b allowed => have := admitted_decreases m b allowed; simp only [potential]; omega
  | there m xs ys _ ih => simp only [potential]; omega

theorem potential_bound (xs : List Mark) : potential xs≤2*xs.length := by
  induction xs with
  | nil => simp [potential]
  | cons m ms ih => have bound : rank m≤2 := by cases m <;> decide
                    simp only [potential,List.length_cons]; omega

/-- Count admitted updates only. Rejected calls consume no credit and may be
numerous; bounding their number additionally requires finite line lists. -/
inductive Admissions : List Mark → List Mark → Nat → Prop
  | nil (xs) : Admissions xs xs 0
  | cons {xs ys zs n} (step : Admission xs ys) (tail : Admissions ys zs n) : Admissions xs zs (n+1)

theorem Admissions.budget {xs ys n} (h : Admissions xs ys n) : n+potential ys≤potential xs := by
  induction h with
  | nil => omega
  | cons step tail ih => have := step.decreases; omega

theorem Admissions.at_most_twice {xs ys n} (h : Admissions xs ys n) : n≤2*xs.length := by
  have := h.budget
  have := potential_bound xs
  omega

/-- Embed one original machine admission at any ledger position. -/
theorem machine_admission (before after : List Mark) (s : X86Memory.State) (m : Mark) (b : Bool)
    (h : GateInputs s m b) (enter : (NoiseAlert.gate s).pc=0x26f83) :
    Admission (before++m::after) (before++marked b::after) := by
  have allowed := (gate_admits s m b h).mp enter
  induction before with
  | nil => exact Admission.here m after b allowed
  | cons x xs ih => exact Admission.there x _ _ ih

/-- The prologue must not overwrite the generation or this sector's mark while
saving its registers. These are initial-address conditions. -/
def PrologueSafe (s : X86Memory.State) : Prop :=
  ∀ a, a ∈ [(0x13580#32),s.regs 0+(66#32),s.regs 0+(18#32)] →
    ∀ b, b ∈ [s.regs 4-(4#32),s.regs 4-(8#32),s.regs 4-(12#32),s.regs 4-(16#32),s.regs 4-(20#32)] → Apart a b

private theorem prepared_read (s : X86Memory.State) (safe : PrologueSafe s) (a : Word)
    (ha : a ∈ [(0x13580#32),s.regs 0+(66#32),s.regs 0+(18#32)]) :
    load32 (NoiseAlert.prepared s).memory a=load32 s.memory a := by
  rw [E1M1NoiseFrame.prepared_memory]
  unfold E1M1NoiseFrame.savedMemory
  repeat rw [load_store_apart _ _ _ _ (safe a ha _ (by simp))]

/-- EDX is loaded after the pushes, so its agreement with the global generation
at this boundary is proved without any separate generation hypothesis. -/
theorem prepared_generation (s : X86Memory.State) :
    load32 (NoiseAlert.prepared s).memory (0x13580#32)=(NoiseAlert.prepared s).regs 2 := by
  simp [NoiseAlert.prepared,NoiseAlert.prepareTail,NoiseAlert.saveThree,NoiseAlert.saveTwo,
    X86Routine.pushWord,put,write]

theorem prepared_inputs (s : X86Memory.State) (m : Mark) (b : Bool)
    (rep : Rep (load32 s.memory (0x13580#32)) (s.regs 0) s.memory m)
    (count : s.regs 2=blocks b) (safe : PrologueSafe s) : GateInputs (NoiseAlert.prepared s) m b := by
  have a : (NoiseAlert.prepared s).regs 0=s.regs 0 := by
    simp [NoiseAlert.prepared,NoiseAlert.prepareTail,NoiseAlert.saveThree,NoiseAlert.saveTwo,X86Routine.pushWord,put,write]
  have base : (NoiseAlert.prepared s).regs 3=s.regs 0 := by
    simp [NoiseAlert.prepared,NoiseAlert.prepareTail,NoiseAlert.saveThree,NoiseAlert.saveTwo,X86Routine.pushWord,put,write]
  have c : (NoiseAlert.prepared s).regs 1=blocks b := by
    simpa [NoiseAlert.prepared,NoiseAlert.prepareTail,NoiseAlert.saveThree,NoiseAlert.saveTwo,X86Routine.pushWord,put,write] using count
  refine ⟨a.trans base.symm,c,?_⟩
  rw [←prepared_generation,prepared_read s safe _ (by simp),base]
  have stamp := prepared_read s safe (s.regs 0+(66#32)) (by simp)
  have cost := prepared_read s safe (s.regs 0+(18#32)) (by simp)
  cases m <;> simpa only [Rep,stamp,cost] using rep

/-- A nonempty original sector traversal consumes credit from its initial
sector mark. Only the initial count, memory relation and prologue separation
are supplied; the gate result and written mark are derived. -/
theorem sector_progress (s : X86Memory.State) (m : Mark) (b : Bool)
    (rep : Rep (load32 s.memory (0x13580#32)) (s.regs 0) s.memory m)
    (count : s.regs 2=blocks b) (safe : PrologueSafe s)
    (more : (E1M1NoiseAlert.sectorResult s).pc=0x26fa6) :
    Rep ((NoiseAlert.prepared s).regs 2) ((NoiseAlert.prepared s).regs 3)
      (E1M1NoiseAlert.sectorResult s).core.memory (marked b) ∧ rank (marked b)+1≤rank m :=
  sector_more_progress s m b (prepared_inputs s m b rep count safe) (prepared_generation s) more

/-- Carry a mark across code that writes elsewhere. This reuses byte-range
separation, including unaligned or wrapping addresses. -/
theorem Rep.frame {generation sector : Word} {before after : Memory} {m : Mark} {w : List Word}
    (rep : Rep generation sector before m) (frame : PlayerHeight.Frame before after w)
    (safe : ∀ a, a ∈ [sector+(66#32),sector+(18#32)] → ∀ b, b ∈ w → Apart a b) :
    Rep generation sector after m := by
  have stamp := frame (sector+(66#32)) (safe _ (by simp))
  have cost := frame (sector+(18#32)) (safe _ (by simp))
  cases m <;> simpa only [Rep,stamp,cost] using rep

theorem update_other_mark (s : X86Memory.State) (generation sector : Word) (m : Mark)
    (rep : Rep generation sector s.memory m)
    (safe : ∀ a, a ∈ [sector+(66#32),sector+(18#32)] → ∀ b,
      b ∈ [s.regs 3+(66#32),s.regs 3+(18#32),s.regs 3+(22#32)] → Apart a b) :
    Rep generation sector (NoiseAlert.updated s).core.memory m :=
  rep.frame (NoiseAlert.update_frame s) safe

theorem eval_preserves_mark (k : Nat) (phase : E1M1NoiseRecursive.Phase) (s t : X86Control.State)
    (generation sector : Word) (m : Mark) (rep : Rep generation sector s.core.memory m)
    (run : E1M1NoiseRecursive.eval k phase s=some t)
    (safe : ∀ a, a ∈ [sector+(66#32),sector+(18#32)] → ∀ b,
      b ∈ E1M1NoisePreservation.writes k phase s → Apart a b) :
    Rep generation sector t.core.memory m :=
  rep.frame (E1M1NoisePreservation.eval_frame k phase s t run) safe

theorem eval_preserves_generation (k : Nat) (phase : E1M1NoiseRecursive.Phase) (s t : X86Control.State)
    (run : E1M1NoiseRecursive.eval k phase s=some t)
    (safe : ∀ b, b ∈ E1M1NoisePreservation.writes k phase s → Apart (0x13580#32) b) :
    load32 t.core.memory (0x13580#32)=load32 s.core.memory (0x13580#32) :=
  E1M1NoisePreservation.eval_frame k phase s t run _ safe
end Doom.Proofs.E1M1NoiseVisits
