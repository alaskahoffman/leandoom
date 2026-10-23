import Doom.Proofs.OriginalInterceptVector
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1800000
set_option linter.unusedSimpArgs false
namespace Doom.Proofs.OriginalLineFraction
open Verification X86 X86Memory X86Control BlockSummary
def code : List UInt8 := [0x8b,0x1,0x8b,0x0,0x89,0x4,0x24,0x8b,0x1,0x8b,0x40,0x4,0x89,0x44,0x24,0x4,0x8b,0x41,0x8,0x89,0x44,0x24,0x8,0x8b,0x41,0xc,0x89,0xe2,0x89,0x44,0x24,0xc,0xb8,0x10,0xba,0x2,0x0,0xe8,0x15,0xfc,0xff,0xff]
def bytesProgram (bytes : List UInt8) : X86Routine.Program := fun pc =>
  if 0x2c691≤pc ∧ pc<0x2c6bb then X86Routine.decodeAt bytes (pc-0x2c691)
  else OriginalInterceptVector.program pc
def program := bytesProgram code
def listed : X86Routine.Program
  | 0x2c691 => some (.control (.block (.legacy (.load 0 1 0))),2)
  | 0x2c693 => some (.control (.block (.legacy (.load 0 0 0))),2)
  | 0x2c695 => some (.control (.block (.store ⟨some 4,none,0,0⟩ 0)),3)
  | 0x2c698 => some (.control (.block (.legacy (.load 0 1 0))),2)
  | 0x2c69a => some (.control (.block (.legacy (.load 0 0 4))),3)
  | 0x2c69d => some (.control (.block (.store ⟨some 4,none,0,4⟩ 0)),4)
  | 0x2c6a1 => some (.control (.block (.legacy (.load 0 1 8))),3)
  | 0x2c6a4 => some (.control (.block (.store ⟨some 4,none,0,8⟩ 0)),4)
  | 0x2c6a8 => some (.control (.block (.legacy (.load 0 1 12))),3)
  | 0x2c6ab => some (.control (.block (.legacy (.mov 2 4))),2)
  | 0x2c6ad => some (.control (.block (.store ⟨some 4,none,0,12⟩ 0)),4)
  | 0x2c6b1 => some (.immediate 0 0x2ba10,5)
  | 0x2c6b6 => some (.call (-1003),5)
  | _ => none

theorem decoded (pc : Nat) (h : listed pc≠none) : program pc=listed pc := by
  fun_cases listed pc <;> simp_all [listed] <;> decide

theorem contains_helper (pc : Nat) (h : OriginalInterceptVector.program pc≠none) :
    program pc=OriginalInterceptVector.program pc := by
  have range : (0x2c2d0≤pc ∧ pc<0x2c334) ∨ (0x1d180≤pc ∧ pc<0x1d1c1) := by
    by_cases r : 0x2c2d0≤pc ∧ pc<0x2c334
    · exact Or.inl r
    · by_cases d : 0x1d180≤pc ∧ pc<0x1d1c1
      · exact Or.inr d
      · simp [OriginalInterceptVector.program,OriginalInterceptVector.bytesProgram,OriginalDivMemory.program,OriginalDivMemory.bytesProgram,r,d] at h
  simp [program,bytesProgram,show ¬(0x2c691≤pc ∧ pc<0x2c6bb) by omega]
def step1 (s : X86Memory.State) := put s 0 (load32 s.memory (s.regs 1+(0#32)))
def step2 (s : X86Memory.State) := put (step1 s) 0 (load32 (step1 s).memory ((step1 s).regs 0+(0#32)))
def step3 (s : X86Memory.State) := {(step2 s) with memory:=store32 (step2 s).memory ((step2 s).regs 4+(0#32)) ((step2 s).regs 0)}
def step4 (s : X86Memory.State) := put (step3 s) 0 (load32 (step3 s).memory ((step3 s).regs 1+(0#32)))
def step5 (s : X86Memory.State) := put (step4 s) 0 (load32 (step4 s).memory ((step4 s).regs 0+(4#32)))
def step6 (s : X86Memory.State) := {(step5 s) with memory:=store32 (step5 s).memory ((step5 s).regs 4+(4#32)) ((step5 s).regs 0)}
def step7 (s : X86Memory.State) := put (step6 s) 0 (load32 (step6 s).memory ((step6 s).regs 1+(8#32)))
def step8 (s : X86Memory.State) := {(step7 s) with memory:=store32 (step7 s).memory ((step7 s).regs 4+(8#32)) ((step7 s).regs 0)}
def step9 (s : X86Memory.State) := put (step8 s) 0 (load32 (step8 s).memory ((step8 s).regs 1+(12#32)))
def step10 (s : X86Memory.State) := put (step9 s) 2 ((step9 s).regs 4)
def step11 (s : X86Memory.State) := {(step10 s) with memory:=store32 (step10 s).memory ((step10 s).regs 4+(12#32)) ((step10 s).regs 0)}
def step12 (s : X86Memory.State) := put (step11 s) 0 0x2ba10
def step13 (s : X86Memory.State) := X86Routine.pushWord (step12 s) 0x2c6bb
def setup := step13
theorem setup_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.Prefix program [] 13 ⟨s,f,0x2c691⟩ ⟨setup s,f,0x2c2d0⟩ := by
  have path : X86Routine.Prefix listed [] 13 ⟨s,f,0x2c691⟩ ⟨setup s,f,0x2c2d0⟩ := by
    apply X86Routine.Prefix.step (middle:=⟨step1 s,f,0x2c693⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,X86Routine.pushWord,step1])
    apply X86Routine.Prefix.step (middle:=⟨step2 s,f,0x2c695⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,X86Routine.pushWord,step1,step2])
    apply X86Routine.Prefix.step (middle:=⟨step3 s,f,0x2c698⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,X86Routine.pushWord,step1,step2,step3])
    apply X86Routine.Prefix.step (middle:=⟨step4 s,f,0x2c69a⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,X86Routine.pushWord,step1,step2,step3,step4])
    apply X86Routine.Prefix.step (middle:=⟨step5 s,f,0x2c69d⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,X86Routine.pushWord,step1,step2,step3,step4,step5])
    apply X86Routine.Prefix.step (middle:=⟨step6 s,f,0x2c6a1⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,X86Routine.pushWord,step1,step2,step3,step4,step5,step6])
    apply X86Routine.Prefix.step (middle:=⟨step7 s,f,0x2c6a4⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,X86Routine.pushWord,step1,step2,step3,step4,step5,step6,step7])
    apply X86Routine.Prefix.step (middle:=⟨step8 s,f,0x2c6a8⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,X86Routine.pushWord,step1,step2,step3,step4,step5,step6,step7,step8])
    apply X86Routine.Prefix.step (middle:=⟨step9 s,f,0x2c6ab⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,X86Routine.pushWord,step1,step2,step3,step4,step5,step6,step7,step8,step9])
    apply X86Routine.Prefix.step (middle:=⟨step10 s,f,0x2c6ad⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,X86Routine.pushWord,step1,step2,step3,step4,step5,step6,step7,step8,step9,step10])
    apply X86Routine.Prefix.step (middle:=⟨step11 s,f,0x2c6b1⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,X86Routine.pushWord,step1,step2,step3,step4,step5,step6,step7,step8,step9,step10,step11])
    apply X86Routine.Prefix.step (middle:=⟨step12 s,f,0x2c6b6⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,X86Routine.pushWord,step1,step2,step3,step4,step5,step6,step7,step8,step9,step10,step11,step12])
    apply X86Routine.Prefix.step (middle:=⟨step13 s,f,0x2c2d0⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,X86Routine.pushWord,step1,step2,step3,step4,step5,step6,step7,step8,step9,step10,step11,step12,step13])
    exact .nil _
  exact path.transfer program [] decoded (by simp)

def result (s : X86Memory.State) := OriginalInterceptVector.result (setup s)
theorem execution (s : X86Memory.State) (f : Option Flags)
    (safe : OriginalInterceptVector.Safe (setup s)) :
    ∃ n≤80, X86Routine.Prefix program [] n ⟨s,f,0x2c691⟩ (result s) := by
  obtain ⟨n,hn,hp⟩ := OriginalInterceptVector.execution (setup s) f safe
  exact ⟨13+n,by omega,OriginalGroupBounds.prefix_join (setup_execution s f) (hp.transfer program [] contains_helper (by simp))⟩

theorem setup_regs (s : X86Memory.State) :
    (setup s).regs 0=(0x2ba10#32) ∧ (setup s).regs 2=s.regs 4 ∧
    (setup s).regs 4=s.regs 4-(4#32) ∧ (setup s).regs 1=s.regs 1 := by
  simp [setup,step1,step2,step3,step4,step5,step6,step7,step8,step9,step10,step11,step12,step13,X86Routine.pushWord,put,write]
theorem setup_return (s : X86Memory.State) : load32 (setup s).memory ((setup s).regs 4)=(0x2c6bb#32) := by
  simp [setup,step1,step2,step3,step4,step5,step6,step7,step8,step9,step10,step11,step12,step13,X86Routine.pushWord,put,write,load_store]
theorem returned (s : X86Memory.State) :
    (result s).pc=0x2c6bb ∧ (result s).core.regs 4=s.regs 4 ∧ (result s).core.regs 1=s.regs 1 := by
  have k := OriginalInterceptVector.returned (setup s)
  refine ⟨?_,?_,?_⟩
  · rw [show (result s).pc=(load32 (setup s).memory ((setup s).regs 4)).toNat from k.2.2.2.2.2.2,setup_return]; rfl
  · simpa [result,(setup_regs s).2.2.1,BitVec.sub_eq_add_neg,BitVec.add_assoc] using k.1
  · exact k.2.2.2.2.1.trans (setup_regs s).2.2.2

/-- The crossing callback's local divline represents this map line. The memory
relation is explicit so callers must supply real encoded geometry. -/
def Encoded (s : X86Memory.State) (trace : Collision.Divline) (line : Collision.Line) : Prop :=
  OriginalInterceptVector.Inputs (setup s) trace ⟨line.x,line.y,line.dx,line.dy⟩ 0x2ba10 (s.regs 4)

theorem live (s : X86Memory.State) (trace : Collision.Divline) (line : Collision.Line)
    (h : Encoded s trace line)
    (ok : (Collision.interceptVector trace ⟨line.x,line.y,line.dx,line.dy⟩).isOk=true) :
    (Collision.interceptVector trace ⟨line.x,line.y,line.dx,line.dy⟩).toOption.map
      (fun v => v.raw.toBitVec)=some ((result s).core.regs 0) :=
  OriginalInterceptVector.live (setup s) trace _ _ _ h ok


def reads (p v : Word) : List Word := [p,p+(8#32),p+(12#32),v,v+(4#32),0x2ba10,0x2ba14,0x2ba18,0x2ba1c]
structure Inputs (s : X86Memory.State) (trace : Collision.Divline) (line : Collision.Line) (p v : Word) : Prop where
  pointer : s.regs 1=p
  vertex : load32 s.memory p=v
  x : load32 s.memory v=line.x.raw.toBitVec
  y : load32 s.memory (v+(4#32))=line.y.raw.toBitVec
  dx : load32 s.memory (p+(8#32))=line.dx.raw.toBitVec
  dy : load32 s.memory (p+(12#32))=line.dy.raw.toBitVec
  tx : load32 s.memory (0x2ba10#32)=trace.x.raw.toBitVec
  ty : load32 s.memory (0x2ba14#32)=trace.y.raw.toBitVec
  tdx : load32 s.memory (0x2ba18#32)=trace.dx.raw.toBitVec
  tdy : load32 s.memory (0x2ba1c#32)=trace.dy.raw.toBitVec
  safe : ∀ a∈reads p v, ∀ off∈[(0#32),4,8,12,-4,-8,-12,-16,-20,-24], Apart a (s.regs 4+off)

def localMemory (s : X86Memory.State) (line : Collision.Line) :=
  store32 (store32 (store32 (store32 (store32 s.memory (s.regs 4) line.x.raw.toBitVec)
    (s.regs 4+(4#32)) line.y.raw.toBitVec) (s.regs 4+(8#32)) line.dx.raw.toBitVec)
    (s.regs 4+(12#32)) line.dy.raw.toBitVec) (s.regs 4-(4#32)) (0x2c6bb#32)

theorem setup_memory (s : X86Memory.State) (trace : Collision.Divline) (line : Collision.Line)
    (p v : Word) (h : Inputs s trace line p v) : (setup s).memory=localMemory s line := by
  have keep (m : Memory) (a value : Word) (ha : a∈reads p v) (off : Word)
      (ho : off∈[(0#32),4,8,12,-4,-8,-12,-16,-20,-24]) := load_store_apart m (s.regs 4+off) a value (h.safe a ha off ho)
  have keep0 (m : Memory) (a value : Word) (ha : a∈reads p v) :
      load32 (store32 m (s.regs 4) value) a=load32 m a := by simpa only [BitVec.add_zero] using keep m a value ha (0#32) (by simp)
  simp [setup,step1,step2,step3,step4,step5,step6,step7,step8,step9,step10,step11,step12,step13,X86Routine.pushWord,put,write,h.pointer,localMemory,keep0,keep,reads,h.vertex,h.x,h.y,h.dx,h.dy]

theorem local_frame (s : X86Memory.State) (line : Collision.Line) (a : Word)
    (safe : ∀ off∈[(0#32),4,8,12,-4], Apart a (s.regs 4+off)) :
    load32 (localMemory s line) a=load32 s.memory a := by
  unfold localMemory
  rw [load_store_apart _ _ _ _ (by simpa only [BitVec.sub_eq_add_neg] using safe (-(4#32)) (by simp))]
  rw [load_store_apart _ _ _ _ (safe (12#32) (by simp)),load_store_apart _ _ _ _ (safe (8#32) (by simp)),load_store_apart _ _ _ _ (safe (4#32) (by simp))]
  exact load_store_apart _ _ _ _ (by simpa only [BitVec.add_zero] using safe (0#32) (by simp))
theorem local_x (s : X86Memory.State) (line : Collision.Line) : load32 (localMemory s line) (s.regs 4+(0#32))=line.x.raw.toBitVec := by
  unfold localMemory
  rw [load_store_apart _ _ _ _ (by simpa only [BitVec.sub_eq_add_neg,BitVec.add_zero] using OriginalPathXStep.apart_translate (s.regs 4) (0#32) (-(4#32)) (by unfold Apart; decide))]
  rw [load_store_apart _ _ _ _ (by simpa only [BitVec.sub_eq_add_neg,BitVec.add_zero] using OriginalPathXStep.apart_translate (s.regs 4) (0#32) (12#32) (by unfold Apart; decide))]
  rw [load_store_apart _ _ _ _ (by simpa only [BitVec.sub_eq_add_neg,BitVec.add_zero] using OriginalPathXStep.apart_translate (s.regs 4) (0#32) (8#32) (by unfold Apart; decide))]
  rw [load_store_apart _ _ _ _ (by simpa only [BitVec.sub_eq_add_neg,BitVec.add_zero] using OriginalPathXStep.apart_translate (s.regs 4) (0#32) (4#32) (by unfold Apart; decide))]
  simp only [BitVec.add_zero]
  rw [load_store]
theorem local_y (s : X86Memory.State) (line : Collision.Line) : load32 (localMemory s line) (s.regs 4+(4#32))=line.y.raw.toBitVec := by
  unfold localMemory
  rw [load_store_apart _ _ _ _ (by simpa only [BitVec.sub_eq_add_neg,BitVec.add_zero] using OriginalPathXStep.apart_translate (s.regs 4) (4#32) (-(4#32)) (by unfold Apart; decide))]
  rw [load_store_apart _ _ _ _ (by simpa only [BitVec.sub_eq_add_neg,BitVec.add_zero] using OriginalPathXStep.apart_translate (s.regs 4) (4#32) (12#32) (by unfold Apart; decide))]
  rw [load_store_apart _ _ _ _ (by simpa only [BitVec.sub_eq_add_neg,BitVec.add_zero] using OriginalPathXStep.apart_translate (s.regs 4) (4#32) (8#32) (by unfold Apart; decide))]
  rw [load_store]
theorem local_dx (s : X86Memory.State) (line : Collision.Line) : load32 (localMemory s line) (s.regs 4+(8#32))=line.dx.raw.toBitVec := by
  unfold localMemory
  rw [load_store_apart _ _ _ _ (by simpa only [BitVec.sub_eq_add_neg,BitVec.add_zero] using OriginalPathXStep.apart_translate (s.regs 4) (8#32) (-(4#32)) (by unfold Apart; decide))]
  rw [load_store_apart _ _ _ _ (by simpa only [BitVec.sub_eq_add_neg,BitVec.add_zero] using OriginalPathXStep.apart_translate (s.regs 4) (8#32) (12#32) (by unfold Apart; decide))]
  rw [load_store]
theorem local_dy (s : X86Memory.State) (line : Collision.Line) : load32 (localMemory s line) (s.regs 4+(12#32))=line.dy.raw.toBitVec := by
  unfold localMemory
  rw [load_store_apart _ _ _ _ (by simpa only [BitVec.sub_eq_add_neg,BitVec.add_zero] using OriginalPathXStep.apart_translate (s.regs 4) (12#32) (-(4#32)) (by unfold Apart; decide))]
  rw [load_store]

theorem encoded (s : X86Memory.State) (trace : Collision.Divline) (line : Collision.Line)
    (p v : Word) (h : Inputs s trace line p v) : Encoded s trace line := by
  have regs := setup_regs s
  have mem := setup_memory s trace line p v h
  have keep (a : Word) (ha : a∈reads p v) : load32 (setup s).memory a=load32 s.memory a := by
    rw [mem]; apply local_frame
    intro off ho
    exact h.safe a ha off (by simp only [List.mem_cons,List.not_mem_nil,or_false] at ho ⊢; rcases ho with rfl|rfl|rfl|rfl|rfl <;> simp)
  refine ⟨regs.1,regs.2.1,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · change load32 (setup s).memory (0x2ba10#32)=_; rw [keep _ (by simp [reads]),h.tx]
  · change load32 (setup s).memory (0x2ba14#32)=_; rw [keep _ (by simp [reads]),h.ty]
  · change load32 (setup s).memory (0x2ba18#32)=_; rw [keep _ (by simp [reads]),h.tdx]
  · change load32 (setup s).memory (0x2ba1c#32)=_; rw [keep _ (by simp [reads]),h.tdy]
  · rw [mem]; simpa only [BitVec.add_zero] using local_x s line
  · rw [mem]; exact local_y s line
  · rw [mem]; exact local_dx s line
  · rw [mem]; exact local_dy s line
  · intro a ha off ho
    rw [regs.2.2.1]
    have localSep (up down : Word) (hu : up∈[(0#32),4,8,12]) (hd : down∈[(4#32),8,12,16,20]) :
        Apart (s.regs 4+up) (s.regs 4-(4#32)-down) := by
      have base : Apart up (-(4#32)-down) := by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hu hd
        rcases hu with rfl|rfl|rfl|rfl <;> rcases hd with rfl|rfl|rfl|rfl|rfl <;> unfold Apart <;> decide
      simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using OriginalPathXStep.apart_translate (s.regs 4) up (-(4#32)-down) base
    have traceSep (a : Word) (ha : a∈reads p v) : Apart a (s.regs 4-(4#32)-off) := by
      have offmem : -(4#32)-off∈[(0#32),4,8,12,-4,-8,-12,-16,-20,-24] := by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at ho
        rcases ho with rfl|rfl|rfl|rfl|rfl <;> decide
      simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using h.safe a ha (-(4#32)-off) offmem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact traceSep _ (by simp [reads])
    · exact traceSep _ (by simp [reads])
    · exact traceSep _ (by simp [reads])
    · exact traceSep _ (by simp [reads])
    · simpa only [BitVec.add_zero] using localSep (0#32) off (by simp) ho
    · exact localSep (4#32) off (by simp) ho
    · exact localSep (8#32) off (by simp) ho
    · exact localSep (12#32) off (by simp) ho

end Doom.Proofs.OriginalLineFraction
