import Doom.Proofs.E1M1NoiseVisits
set_option maxRecDepth 32768
set_option maxHeartbeats 2000000
namespace Doom.Verification.NoiseVisitsFixture
open Doom Doom.Proofs X86 X86Memory X86Control BlockSummary E1M1NoiseVisits

def initial (m : Mark) (b wrap : Bool) : X86Memory.State :=
  ⟨fun r => if r=0 then 0x600101 else if r=2 then blocks b else if r=4 then (if wrap then 1 else 0x602e01)
    else BitVec.ofNat 32 (10+r.val),
    ([(0x13580,0xffffffff),(0x2b958,0x600d01),(0x600143,if m=.unseen then 0 else 0xffffffff),
      (0x600113,match m with | .unseen => 0x80000000 | .blocked => 2 | .clear => 1),
      (0x60014f,1)] : List (Word × Word)).foldl (fun mem p => store32 mem p.1 p.2) (fun _ => 0)⟩

theorem relation (m : Mark) (b wrap : Bool) :
    Rep (load32 (initial m b wrap).memory (0x13580#32)) ((initial m b wrap).regs 0) (initial m b wrap).memory m := by
  cases m <;> cases b <;> cases wrap <;> unfold Rep <;> decide +kernel

theorem separate (m : Mark) (b wrap : Bool) : PrologueSafe (initial m b wrap) := by
  cases m <;> cases b <;> cases wrap
  all_goals
    intro a ha c hc
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha hc
    rcases ha with rfl|rfl|rfl
    all_goals
      rcases hc with rfl|rfl|rfl|rfl|rfl
      all_goals unfold Apart; decide +kernel

theorem inputs (m : Mark) (b wrap : Bool) : GateInputs (NoiseAlert.prepared (initial m b wrap)) m b :=
  prepared_inputs _ m b (relation m b wrap) (by cases b <;> rfl) (separate m b wrap)

-- The old signed-negative cost on an unseen sector is deliberately irrelevant.
example (m : Mark) (b wrap : Bool) :
    (NoiseAlert.gate (NoiseAlert.prepared (initial m b wrap))).pc=0x26f83 ↔ admits m b=true :=
  gate_admits _ m b (inputs m b wrap)

example (m : Mark) (b wrap : Bool) : (E1M1NoiseAlert.sectorResult (initial m b wrap)).pc=
    if admits m b then 0x26fa6 else 0x27011 := by
  cases m <;> cases b <;> cases wrap <;> decide +kernel

example (wrap : Bool) :
    Rep ((NoiseAlert.prepared (initial .blocked false wrap)).regs 2)
      ((NoiseAlert.prepared (initial .blocked false wrap)).regs 3)
      (E1M1NoiseAlert.sectorResult (initial .blocked false wrap)).core.memory .clear ∧ rank .clear+1≤rank .blocked :=
  sector_progress _ .blocked false (relation _ _ _) (by rfl) (separate _ _ _) (by cases wrap <;> decide +kernel)

-- Three sectors can each use both credits. This witnesses sharpness of 2*N.
theorem six_admissions : Admissions [.unseen,.unseen,.unseen] [.clear,.clear,.clear] 6 := by
  apply Admissions.cons (Admission.here .unseen _ true (by decide))
  apply Admissions.cons (Admission.there .blocked _ _ (Admission.here .unseen _ true (by decide)))
  apply Admissions.cons (Admission.there .blocked _ _ (Admission.there .blocked _ _ (Admission.here .unseen _ true (by decide))))
  apply Admissions.cons (Admission.here .blocked _ false (by decide))
  apply Admissions.cons (Admission.there .clear _ _ (Admission.here .blocked _ false (by decide)))
  apply Admissions.cons (Admission.there .clear _ _ (Admission.there .clear _ _ (Admission.here .blocked _ false (by decide))))
  exact Admissions.nil _
example : 6≤2*([Mark.unseen,.unseen,.unseen] : List Mark).length := six_admissions.at_most_twice
example : ¬Admissions [.unseen] [.clear] 3 := by
  intro h
  have bound := h.at_most_twice
  simp at bound
example : admits .blocked true=false ∧ admits .clear false=false ∧ admits .clear true=false := by decide

-- Signed comparison is significant outside the admitted mark relation.
def negativeCost : X86Memory.State :=
  { NoiseAlert.prepared (initial .blocked false false) with
    memory := store32 (NoiseAlert.prepared (initial .blocked false false)).memory 0x600113 0x80000000 }
example : (NoiseAlert.gate negativeCost).pc=0x27011 := by decide +kernel
end Doom.Verification.NoiseVisitsFixture
