import Doom.Proofs.E1M1NoiseVisits
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1600000
set_option linter.unusedSimpArgs false
namespace Doom.Proofs.E1M1NoiseLedger
open Verification X86 X86Memory X86Control BlockSummary E1M1NoiseVisits
abbrev Ledger := List (Word × Mark)
def addresses (xs : Ledger) := xs.map Prod.fst
def credit (xs : Ledger) := potential (xs.map Prod.snd)
def Represents (generation : Word) (mem : Memory) (xs : Ledger) : Prop :=
  load32 mem (0x13580#32)=generation ∧ ∀ p, p ∈ xs → Rep generation p.1 mem p.2

def update (target : Word) (b : Bool) (xs : Ledger) : Ledger :=
  xs.map (fun p => if p.1=target then (p.1,marked b) else p)

theorem update_addresses (target : Word) (b : Bool) (xs : Ledger) :
    addresses (update target b xs)=addresses xs := by
  induction xs with
  | nil => rfl
  | cons p xs ih => by_cases h : p.1=target <;> simp_all [addresses,update]

theorem update_credit (target : Word) (b : Bool) (xs : Ledger)
    (allowed : ∀ p, p ∈ xs → p.1=target → admits p.2 b=true) :
    credit (update target b xs)≤credit xs ∧
      (target ∈ addresses xs → credit (update target b xs)+1≤credit xs) := by
  induction xs with
  | nil => simp [credit,update,addresses,potential]
  | cons p xs ih =>
    have tail := ih (fun q hq => allowed q (by simp [hq]))
    by_cases here : p.1=target
    · have dec := admitted_decreases p.2 b (allowed p (by simp) here)
      simp only [credit,update,List.map_cons,if_pos here,potential] at *
      constructor <;> intros <;> omega
    · have same : (if p.1=target then (p.1,marked b) else p)=p := if_neg here
      simp only [credit,update,List.map_cons,same,potential] at *
      constructor
      · omega
      · intro member
        have member : target ∈ addresses xs := by simpa [addresses, Ne.symm here] using member
        have := tail.2 member
        omega

def stackWrites (s : X86Memory.State) : List Word :=
  [s.regs 4-(4#32),s.regs 4-(8#32),s.regs 4-(12#32),s.regs 4-(16#32),s.regs 4-(20#32)]
def markWrites (s : X86Memory.State) : List Word :=
  [s.regs 0+(66#32),s.regs 0+(18#32),s.regs 0+(22#32)]
def markReads (a : Word) : List Word := [a+(66#32),a+(18#32)]
def Protect (reads writes : List Word) : Prop := ∀ a, a ∈ reads → ∀ b, b ∈ writes → Apart a b

/-- Local address and count conditions. No post-state ledger relation or
preservation of another sector is assumed. Duplicate layout entries are allowed
but conservatively counted separately in the final bound. -/
structure SectorSafe (layout : List Word) (s : X86Memory.State) : Prop where
  member : s.regs 0 ∈ layout
  count : s.regs 2=(0#32) ∨ s.regs 2=(1#32)
  stack : ∀ a, a ∈ layout → Protect (markReads a) (stackWrites s)
  counter : ∀ a, a ∈ E1M1NoiseFootprint.sectorWrites s → Apart (0x13580#32) a
  others : ∀ a, a ∈ layout → a≠s.regs 0 → Protect (markReads a) (markWrites s)

def LineSafe (layout : List Word) (s : X86Memory.State) : Prop :=
  (∀ b, b ∈ E1M1NoiseFootprint.lineWrites s → Apart (0x13580#32) b) ∧
  ∀ a, a ∈ layout → Protect (markReads a) (E1M1NoiseFootprint.lineWrites s)

theorem prepared_frame (s : X86Memory.State) :
    PlayerHeight.Frame s.memory (NoiseAlert.prepared s).memory (stackWrites s) := by
  intro a safe
  rw [E1M1NoiseFrame.prepared_memory]
  unfold E1M1NoiseFrame.savedMemory
  repeat rw [load_store_apart _ _ _ _ (safe _ (by simp [stackWrites]))]

private theorem prepared_regs (s : X86Memory.State) :
    (NoiseAlert.prepared s).regs 3=s.regs 0 ∧ (NoiseAlert.prepared s).regs 0=s.regs 0 := by
  simp [NoiseAlert.prepared,NoiseAlert.prepareTail,NoiseAlert.saveThree,NoiseAlert.saveTwo,X86Routine.pushWord,put,write]
private theorem gate_memory (s : X86Memory.State) : (NoiseAlert.gate s).core.memory=s.memory := by
  unfold NoiseAlert.gate; split <;> rfl

def admitted (s : X86Memory.State) : Prop := (NoiseAlert.gate (NoiseAlert.prepared s)).pc=0x26f83
instance (s : X86Memory.State) : Decidable (admitted s) := inferInstanceAs (Decidable (_=(_ : Nat)))
def charge (s : X86Memory.State) : Nat := if admitted s then 1 else 0

private theorem prologue_safe (layout : List Word) (s : X86Memory.State) (safe : SectorSafe layout s) :
    PrologueSafe s := by
  intro a ha b hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
  rcases ha with rfl|rfl|rfl
  · apply safe.counter b
    have incl : b ∈ stackWrites s ++ markWrites s := List.mem_append_left _ hb
    simpa [stackWrites,markWrites,E1M1NoiseFootprint.sectorWrites] using incl
  · exact safe.stack _ safe.member _ (by simp [markReads]) _ hb
  · exact safe.stack _ safe.member _ (by simp [markReads]) _ hb

/-- The actual sector prefix updates the whole ledger, preserves its address
layout and generation, and pays for any admission from the global credit. -/
theorem sector_step (layout : List Word) (generation : Word) (s : X86Memory.State) (xs : Ledger)
    (shape : addresses xs=layout) (rep : Represents generation s.memory xs) (safe : SectorSafe layout s) :
    ∃ ys, addresses ys=layout ∧ Represents generation (E1M1NoiseAlert.sectorResult s).core.memory ys ∧
      credit ys+charge s≤credit xs := by
  have counter := E1M1NoiseFootprint.sector_frame s (0x13580#32) safe.counter
  have counter' := counter.trans rep.1
  obtain ⟨b,count⟩ : ∃ b : Bool, s.regs 2=blocks b := by
    rcases safe.count with h|h
    · exact ⟨false,h⟩
    · exact ⟨true,h⟩
  have ps := prologue_safe layout s safe
  have gen : (NoiseAlert.prepared s).regs 2=generation := by
    rw [←prepared_generation]
    have keep := prepared_frame s (0x13580#32) (fun a ha => ps _ (by simp) a ha)
    exact keep.trans rep.1
  have current (p : Word × Mark) (hp : p ∈ xs) (eq : p.1=s.regs 0) :
      GateInputs (NoiseAlert.prepared s) p.2 b := by
    apply prepared_inputs s p.2 b _ count ps
    rw [rep.1,←eq]
    exact rep.2 p hp
  by_cases enter : admitted s
  · refine ⟨update (s.regs 0) b xs,(update_addresses _ _ _).trans shape,⟨counter',?_⟩,?_⟩
    · intro q hq
      obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hq
      by_cases eq : p.1=s.regs 0
      · simp only [if_pos eq]
        have result := (machine_progress (NoiseAlert.prepared s) p.2 b (current p hp eq) (prepared_generation s) enter).1
        change (NoiseAlert.gate (NoiseAlert.prepared s)).pc=0x26f83 at enter
        simpa only [E1M1NoiseAlert.sectorResult,enter,ite_true,gen,(prepared_regs s).1,eq] using result
      · simp only [if_neg eq]
        apply (rep.2 p hp).frame (E1M1NoiseFootprint.sector_frame s)
        have member : p.1 ∈ layout := by rw [←shape]; exact List.mem_map.mpr ⟨p,hp,rfl⟩
        intro a ha c hc
        have parts : c ∈ stackWrites s ∨ c ∈ markWrites s := by
          simpa [stackWrites,markWrites,E1M1NoiseFootprint.sectorWrites,or_assoc] using hc
        rcases parts with h|h
        · exact safe.stack _ member a ha c h
        · exact safe.others _ member eq a ha c h
    · have bound := (update_credit (s.regs 0) b xs (fun p hp eq =>
        (gate_admits _ p.2 b (current p hp eq)).mp enter)).2 (by rw [shape]; exact safe.member)
      simpa only [charge,enter,ite_true] using bound
  · refine ⟨xs,shape,⟨counter',?_⟩,by simp [charge,enter]⟩
    intro p hp
    have member : p.1 ∈ layout := by rw [←shape]; exact List.mem_map.mpr ⟨p,hp,rfl⟩
    have kept := (rep.2 p hp).frame (prepared_frame s) (safe.stack _ member)
    change ¬(NoiseAlert.gate (NoiseAlert.prepared s)).pc=0x26f83 at enter
    simpa only [E1M1NoiseAlert.sectorResult,enter,ite_false,gate_memory] using kept

theorem sector_more_charge (s : X86Memory.State)
    (more : (E1M1NoiseAlert.sectorResult s).pc=0x26fa6) : charge s=1 := by
  have enter : admitted s := by
    by_cases yes : admitted s
    · exact yes
    exfalso
    change ¬(NoiseAlert.gate (NoiseAlert.prepared s)).pc=0x26f83 at yes
    simp only [E1M1NoiseAlert.sectorResult,if_neg yes] at more
    have endpoints (r : X86Memory.State) :
        (NoiseAlert.gate r).pc=0x26f83 ∨ (NoiseAlert.gate r).pc=0x27011 := by
      unfold NoiseAlert.gate
      split
      · exact Or.inl rfl
      · split
        · exact Or.inr rfl
        · exact Or.inl rfl
    have := endpoints (NoiseAlert.prepared s)
    omega
  simp [charge,enter]

theorem line_step (layout : List Word) (generation : Word) (s : X86Memory.State) (xs : Ledger)
    (shape : addresses xs=layout) (rep : Represents generation s.memory xs) (safe : LineSafe layout s) :
    Represents generation (E1M1NoiseIteration.dispatched s).core.memory xs := by
  refine ⟨(E1M1NoiseFootprint.dispatch_frame s _ safe.1).trans rep.1,?_⟩
  intro p hp
  have member : p.1 ∈ layout := by rw [←shape]; exact List.mem_map.mpr ⟨p,hp,rfl⟩
  exact (rep.2 p hp).frame (E1M1NoiseFootprint.dispatch_frame s) (safe.2 _ member)
end Doom.Proofs.E1M1NoiseLedger
