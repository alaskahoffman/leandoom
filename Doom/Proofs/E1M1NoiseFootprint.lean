import Doom.Proofs.E1M1NoiseFrame
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1600000
set_option linter.unusedSimpArgs false
namespace Doom.Proofs.E1M1NoiseFootprint
open Verification X86 X86Memory X86Control BlockSummary

/-- Conservative word-write footprints, not lists of observed values. -/
def sectorWrites (s : X86Memory.State) : List Word :=
  [s.regs 4-(4#32),s.regs 4-(8#32),s.regs 4-(12#32),s.regs 4-(16#32),s.regs 4-(20#32),
   s.regs 0+(66#32),s.regs 0+(18#32),s.regs 0+(22#32)]
def lineWrites (s : X86Memory.State) : List Word :=
  [s.regs 4-(4#32),s.regs 4-(8#32),s.regs 4-(12#32),s.regs 4-(16#32),s.regs 4-(20#32),
   s.regs 4,0x2c034,0x2c030,0x2c02c,0x2c038]

/-- Compose footprint guarantees without assuming that writes are separated. -/
theorem frame_trans {a b c : Memory} {xs ys : List Word}
    (h : PlayerHeight.Frame a b xs) (g : PlayerHeight.Frame b c ys) :
    PlayerHeight.Frame a c (xs++ys) := by
  intro x safe
  rw [g x (fun y hy => safe y (List.mem_append_right _ hy))]
  exact h x (fun y hy => safe y (List.mem_append_left _ hy))

@[simp] theorem sector_sp (s : X86Memory.State) :
    (E1M1NoiseAlert.sectorResult s).core.regs 4=s.regs 4-(24#32) := by
  simp only [E1M1NoiseAlert.sectorResult]
  split <;> simp only [NoiseAlert.gate] <;> split <;>
    simp [NoiseAlert.updated,NoiseAlert.prepared,NoiseAlert.prepareTail,NoiseAlert.saveThree,
      NoiseAlert.saveTwo,X86Routine.pushWord,put,write,BitVec.sub_eq_add_neg,BitVec.add_assoc]

private theorem gate_memory (s : X86Memory.State) : (NoiseAlert.gate s).core.memory=s.memory := by
  unfold NoiseAlert.gate; split <;> rfl
private theorem gate_sector (s : X86Memory.State) :
    (NoiseAlert.gate (NoiseAlert.prepared s)).core.regs 3=s.regs 0 := by
  unfold NoiseAlert.gate; split <;>
    simp [NoiseAlert.prepared,NoiseAlert.prepareTail,NoiseAlert.saveThree,NoiseAlert.saveTwo,X86Routine.pushWord,put,write]

theorem sector_frame (s : X86Memory.State) :
    PlayerHeight.Frame s.memory (E1M1NoiseAlert.sectorResult s).core.memory (sectorWrites s) := by
  intro a safe
  have prep : load32 (NoiseAlert.prepared s).memory a=load32 s.memory a := by
    rw [E1M1NoiseFrame.prepared_memory]
    unfold E1M1NoiseFrame.savedMemory
    repeat rw [load_store_apart _ _ _ _ (safe _ (by simp [sectorWrites]))]
  simp only [E1M1NoiseAlert.sectorResult]
  split
  · rw [NoiseAlert.update_frame _ a (by simpa only [gate_sector] using
        (show ∀ b, b ∈ [s.regs 0+(66#32),s.regs 0+(18#32),s.regs 0+(22#32)] → Apart a b from
          fun b hb => safe b (by simp only [sectorWrites,List.mem_cons,List.not_mem_nil,or_false] at *; exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hb)))))))]
    rw [gate_memory]; exact prep
  · rw [gate_memory]; exact prep

@[simp] theorem opening_sp (s : X86Memory.State) : (E1M1NoiseOpening.result s).core.regs 4=s.regs 4+(4#32) := by
  simp only [E1M1NoiseOpening.result]
  split <;> simp [NoiseOpening.closed,NoiseOpening.entry,NoiseOpening.prepared,NoiseOpening.saved,
    NoiseOpening.returned,NoiseOpening.range,NoiseOpening.floor,NoiseOpening.floorInputs,
    NoiseOpening.ceiling,NoiseOpening.ceilingInputs,PspriteLoop.popped,X86Routine.pushWord,
    put,write,BitVec.sub_eq_add_neg,BitVec.add_assoc]

private theorem opening_frame (s : X86Memory.State) (a : Word)
    (safe : ∀ b, b ∈ [s.regs 4-(4#32),s.regs 4-(8#32),s.regs 4-(12#32),s.regs 4-(16#32),
      (0x2c034#32),0x2c030,0x2c02c,0x2c038] → Apart a b) :
    load32 (E1M1NoiseOpening.result s).core.memory a=load32 s.memory a := by
  have keep (b : Word) (hb : b ∈ [s.regs 4-(4#32),s.regs 4-(8#32),s.regs 4-(12#32),s.regs 4-(16#32),
      (0x2c034#32),0x2c030,0x2c02c,0x2c038]) (m : Memory) (v : Word) := load_store_apart m b a v (safe b hb)
  simp only [E1M1NoiseOpening.result]
  split <;> simp only [NoiseOpening.closed,NoiseOpening.entry,NoiseOpening.prepared,NoiseOpening.saved,
    NoiseOpening.returned,NoiseOpening.range,NoiseOpening.floor,NoiseOpening.floorInputs,
    NoiseOpening.ceiling,NoiseOpening.ceilingInputs,PspriteLoop.popped,X86Routine.pushWord,put,write]
  all_goals
    simp only [ite_true,ite_false,BitVec.sub_sub]
    repeat rw [keep _ (by simp)]

@[simp] theorem opened_sp (s : X86Memory.State) (f : Option Flags) :
    (E1M1NoiseOpening.opened s f).core.regs 4=s.regs 4 := by
  simp [E1M1NoiseOpening.opened,opening_sp,NoiseTraversal.openingCall,X86Routine.pushWord,put,write,
    BitVec.sub_eq_add_neg,BitVec.add_assoc]

theorem opened_frame (s : X86Memory.State) (f : Option Flags) :
    PlayerHeight.Frame s.memory (E1M1NoiseOpening.opened s f).core.memory (lineWrites s) := by
  intro a safe
  have h := opening_frame (NoiseTraversal.openingCall s f).core a (by
    intro b hb
    apply safe b
    simp only [NoiseTraversal.openingCall,X86Routine.pushWord,put,write,ite_false,ite_true,BitVec.sub_sub] at hb
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
    rcases hb with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> simp [lineWrites])
  change load32 (E1M1NoiseOpening.result (NoiseTraversal.openingCall s f).core).core.memory a=_
  rw [h]
  apply load_store_apart
  simpa [put,write] using safe (s.regs 4-(4#32)) (by simp [lineWrites])

@[simp] theorem neighbor_sp (s : X86Memory.State) : (E1M1NoiseOpening.neighbor s).core.regs 4=s.regs 4 := by
  simp only [E1M1NoiseOpening.neighbor]
  split <;> simp [NoiseOpening.backNeighbor,NoiseOpening.frontNeighbor,NoiseOpening.neighborGate,
    NoiseOpening.neighborInputs,put,write]
private theorem neighbor_frame (s : X86Memory.State) :
    PlayerHeight.Frame s.memory (E1M1NoiseOpening.neighbor s).core.memory [s.regs 4] := by
  intro a safe
  simp only [E1M1NoiseOpening.neighbor]
  split <;> simp only [NoiseOpening.backNeighbor,NoiseOpening.frontNeighbor,NoiseOpening.neighborGate,
    NoiseOpening.neighborInputs,put,write,ite_true,ite_false]
  all_goals exact load_store_apart _ _ _ _ (safe _ (by simp))

@[simp] theorem line_result_sp (s : X86Memory.State) (f : Option Flags) :
    (E1M1NoiseOpening.lineResult s f).core.regs 4=s.regs 4 := by
  simp only [E1M1NoiseOpening.lineResult]; split <;> simp [NoiseTraversal.openingGate]
private theorem line_result_frame (s : X86Memory.State) (f : Option Flags) :
    PlayerHeight.Frame s.memory (E1M1NoiseOpening.lineResult s f).core.memory (lineWrites s) := by
  intro a safe
  simp only [E1M1NoiseOpening.lineResult]; split
  · rw [neighbor_frame _ a (by simpa [NoiseTraversal.openingGate] using
      (show ∀ b, b ∈ [s.regs 4] → Apart a b from fun b hb => safe b (by simp_all [lineWrites])))]
    exact opened_frame s f a safe
  · exact opened_frame s f a safe

@[simp] theorem block_sp (s : X86Memory.State) :
    (NoiseTraversal.blockResult s).core.regs 4=
      if (NoiseTraversal.blockResult s).pc=0x26f60 then s.regs 4-(4#32) else s.regs 4 := by
  simp only [NoiseTraversal.blockResult]; split
  · rfl
  · split <;> simp [NoiseTraversal.recursiveCall,X86Routine.pushWord,put,write]
private theorem block_frame (s : X86Memory.State) :
    PlayerHeight.Frame s.memory (NoiseTraversal.blockResult s).core.memory [s.regs 4-(4#32)] := by
  intro a safe
  simp only [NoiseTraversal.blockResult]; split
  · exact load_store_apart _ _ _ _ (safe _ (by simp [put,write]))
  · split
    · exact load_store_apart _ _ _ _ (safe _ (by simp [put,write]))
    · rfl

private theorem line_result_not_call (s : X86Memory.State) (f : Option Flags) :
    (E1M1NoiseOpening.lineResult s f).pc≠0x26f60 := by
  simp only [E1M1NoiseOpening.lineResult]; split
  · simp only [E1M1NoiseOpening.neighbor]; split <;> simp [NoiseOpening.backNeighbor,NoiseOpening.frontNeighbor]
  · simp only [NoiseTraversal.openingGate]; split <;> decide

private theorem opening_block_sp (s : X86Memory.State) (f : Option Flags) :
    (E1M1NoiseOpening.blockResult s f).core.regs 4=
      if (E1M1NoiseOpening.blockResult s f).pc=0x26f60 then s.regs 4-(4#32) else s.regs 4 := by
  simp only [E1M1NoiseOpening.blockResult]; split
  · rw [block_sp,line_result_sp]
  · simp only [line_result_sp,if_neg (line_result_not_call s f)]

@[simp] theorem dispatch_sp (s : X86Memory.State) :
    (E1M1NoiseIteration.dispatched s).core.regs 4=
      if (E1M1NoiseIteration.dispatched s).pc=0x26f60 then s.regs 4-(4#32) else s.regs 4 := by
  have gate_sp : (NoiseTraversal.lineGate s).core.regs 4=s.regs 4 := by
    simp [NoiseTraversal.lineGate,NoiseTraversal.selected,put,write]
  simp only [E1M1NoiseIteration.dispatched]; split
  · rw [opening_block_sp,gate_sp]
  · have pc : (NoiseTraversal.lineGate s).pc≠0x26f60 := by
      simp only [NoiseTraversal.lineGate]; split <;> decide
    rw [if_neg pc,gate_sp]

theorem dispatch_frame (s : X86Memory.State) :
    PlayerHeight.Frame s.memory (E1M1NoiseIteration.dispatched s).core.memory (lineWrites s) := by
  intro a safe
  have gate_sp : (NoiseTraversal.lineGate s).core.regs 4=s.regs 4 := by
    simp [NoiseTraversal.lineGate,NoiseTraversal.selected,put,write]
  have gate_mem : (NoiseTraversal.lineGate s).core.memory=s.memory := rfl
  have safe' : ∀ b, b ∈ lineWrites (NoiseTraversal.lineGate s).core → Apart a b := by
    simpa only [lineWrites,gate_sp] using safe
  simp only [E1M1NoiseIteration.dispatched]; split
  · simp only [E1M1NoiseOpening.blockResult]; split
    · rw [block_frame _ a (by
        intro b hb; simp only [List.mem_singleton] at hb; subst b
        rw [line_result_sp,gate_sp]; exact safe _ (by simp [lineWrites]))]
      exact line_result_frame _ _ a safe'
    · exact line_result_frame _ _ a safe'
  · rfl
end Doom.Proofs.E1M1NoiseFootprint
