import Doom.Proofs.OriginalLineFraction
import Doom.Proofs.OriginalThingSecondSide
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1800000
set_option linter.unusedSimpArgs false
namespace Doom.Proofs.OriginalThingFraction
open Verification X86 X86Memory X86Control BlockSummary
open OriginalThingDiagonal (points)
def thingFraction : List UInt8 := [0x8b,0x44,0x24,0x14,0x89,0xe2,0x89,0x3c,0x24,0x89,0x74,0x24,0x4,0x29,0xf8,0x29,0xf5,0x89,0x44,0x24,0x8,0xb8,0x10,0xba,0x2,0x0,0x89,0x6c,0x24,0xc,0xe8,0xff,0xfa,0xff,0xff,0x85,0xc0,0x7d,0xf,0xb8,0x1,0x0,0x0,0x0]
def bytesProgram (bytes : List UInt8) : X86Routine.Program := fun pc =>
  if 0x2c7ae≤pc ∧ pc<0x2c7da then X86Routine.decodeAt bytes (pc-0x2c7ae)
  else OriginalInterceptVector.program pc
def program := bytesProgram thingFraction
def listed : X86Routine.Program
  | 0x2c7ae => some (.control (.block (.load 0 ⟨some 4,none,0,20⟩)),4)
  | 0x2c7b2 => some (.control (.block (.legacy (.mov 2 4))),2)
  | 0x2c7b4 => some (.control (.block (.store ⟨some 4,none,0,0⟩ 7)),3)
  | 0x2c7b7 => some (.control (.block (.store ⟨some 4,none,0,4⟩ 6)),4)
  | 0x2c7bb => some (.control (.block (.arithmetic (.sub 0 7))),2)
  | 0x2c7bd => some (.control (.block (.arithmetic (.sub 5 6))),2)
  | 0x2c7bf => some (.control (.block (.store ⟨some 4,none,0,8⟩ 0)),4)
  | 0x2c7c3 => some (.immediate 0 0x2ba10,5)
  | 0x2c7c8 => some (.control (.block (.store ⟨some 4,none,0,12⟩ 5)),4)
  | 0x2c7cc => some (.call (-1281),5)
  | 0x2c7d1 => some (.control (.testWord 0 0),2)
  | 0x2c7d3 => some (.jumpSigned 0 15,2)
  | 0x2c7d5 => some (.immediate 0 1,5)
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
  simp [program,bytesProgram,show ¬(0x2c7ae≤pc ∧ pc<0x2c7da) by omega]

def step1 (s : X86Memory.State) := put s 0 (load32 s.memory (s.regs 4+(20#32)))
def step2 (s : X86Memory.State) := put (step1 s) 2 (s.regs 4)
def step3 (s : X86Memory.State) : X86Memory.State := {step2 s with memory:=store32 s.memory (s.regs 4) (s.regs 7)}
def step4 (s : X86Memory.State) : X86Memory.State := {step3 s with memory:=store32 (step3 s).memory (s.regs 4+(4#32)) (s.regs 6)}
def step5 (s : X86Memory.State) := put (step4 s) 0 ((step4 s).regs 0-s.regs 7)
def step6 (s : X86Memory.State) := put (step5 s) 5 (s.regs 5-s.regs 6)
def step7 (s : X86Memory.State) : X86Memory.State := {step6 s with memory:=store32 (step6 s).memory (s.regs 4+(8#32)) ((step6 s).regs 0)}
def step8 (s : X86Memory.State) := put (step7 s) 0 0x2ba10
def step9 (s : X86Memory.State) : X86Memory.State := {step8 s with memory:=store32 (step8 s).memory (s.regs 4+(12#32)) ((step8 s).regs 5)}
def setup (s : X86Memory.State) := X86Routine.pushWord (step9 s) 0x2c7d1

theorem setup_execution (s : X86Memory.State) (f : Option Flags) :
    X86Routine.Prefix program [] 10 ⟨s,f,0x2c7ae⟩ ⟨setup s,none,0x2c2d0⟩ := by
  have path : X86Routine.Prefix listed [] 10 ⟨s,f,0x2c7ae⟩ ⟨setup s,none,0x2c2d0⟩ := by
    apply X86Routine.Prefix.step (middle:=⟨step1 s,f,0x2c7b2⟩) (by simp) (by rfl) (by simp [setup,step1,step2,step3,step4,step5,step6,step7,step8,step9,X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,X86Routine.pushWord])
    apply X86Routine.Prefix.step (middle:=⟨step2 s,f,0x2c7b4⟩) (by simp) (by rfl) (by simp [setup,step1,step2,step3,step4,step5,step6,step7,step8,step9,X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,X86Routine.pushWord])
    apply X86Routine.Prefix.step (middle:=⟨step3 s,f,0x2c7b7⟩) (by simp) (by rfl) (by simp [setup,step1,step2,step3,step4,step5,step6,step7,step8,step9,X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,X86Routine.pushWord])
    apply X86Routine.Prefix.step (middle:=⟨step4 s,f,0x2c7bb⟩) (by simp) (by rfl) (by simp [setup,step1,step2,step3,step4,step5,step6,step7,step8,step9,X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,X86Routine.pushWord])
    apply X86Routine.Prefix.step (middle:=⟨step5 s,none,0x2c7bd⟩) (by simp) (by rfl) (by simp [setup,step1,step2,step3,step4,step5,step6,step7,step8,step9,X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,X86Routine.pushWord])
    apply X86Routine.Prefix.step (middle:=⟨step6 s,none,0x2c7bf⟩) (by simp) (by rfl) (by simp [setup,step1,step2,step3,step4,step5,step6,step7,step8,step9,X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,X86Routine.pushWord])
    apply X86Routine.Prefix.step (middle:=⟨step7 s,none,0x2c7c3⟩) (by simp) (by rfl) (by simp [setup,step1,step2,step3,step4,step5,step6,step7,step8,step9,X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,X86Routine.pushWord])
    apply X86Routine.Prefix.step (middle:=⟨step8 s,none,0x2c7c8⟩) (by simp) (by rfl) (by simp [setup,step1,step2,step3,step4,step5,step6,step7,step8,step9,X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,X86Routine.pushWord])
    apply X86Routine.Prefix.step (middle:=⟨step9 s,none,0x2c7cc⟩) (by simp) (by rfl) (by simp [setup,step1,step2,step3,step4,step5,step6,step7,step8,step9,X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,X86Routine.pushWord])
    apply X86Routine.Prefix.step (middle:=⟨setup s,none,0x2c2d0⟩) (by simp) (by rfl) (by simp [setup,step1,step2,step3,step4,step5,step6,step7,step8,step9,X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86.execute,X86Block.Address.eval,blockPreservesFlags,put,write,X86Routine.pushWord])
    exact .nil _
  exact path.transfer program [] decoded (by simp)

def fraction (s : X86Memory.State) := OriginalInterceptVector.result (setup s)
theorem fraction_execution (s : X86Memory.State) (f : Option Flags)
    (safe : OriginalInterceptVector.Safe (setup s)) :
    ∃ n≤77, X86Routine.Prefix program [] n ⟨s,f,0x2c7ae⟩ (fraction s) := by
  obtain ⟨n,hn,hp⟩ := OriginalInterceptVector.execution (setup s) none safe
  exact ⟨10+n,by omega,OriginalGroupBounds.prefix_join (setup_execution s f) (hp.transfer program [] contains_helper (by simp))⟩

theorem setup_regs (s : X86Memory.State) :
    (setup s).regs 0=(0x2ba10#32) ∧ (setup s).regs 2=s.regs 4 ∧
    (setup s).regs 4=s.regs 4-(4#32) ∧ (setup s).regs 1=s.regs 1 := by
  simp [setup,step1,step2,step3,step4,step5,step6,step7,step8,step9,X86Routine.pushWord,put,write]

theorem setup_return (s : X86Memory.State) : load32 (setup s).memory ((setup s).regs 4)=(0x2c7d1#32) := by
  simp [setup,step1,step2,step3,step4,step5,step6,step7,step8,step9,X86Routine.pushWord,put,write,load_store]
theorem returned (s : X86Memory.State) :
    (fraction s).pc=0x2c7d1 ∧ (fraction s).core.regs 4=s.regs 4 ∧ (fraction s).core.regs 1=s.regs 1 := by
  have k := OriginalInterceptVector.returned (setup s)
  refine ⟨?_,?_,?_⟩
  · rw [show (fraction s).pc=(load32 (setup s).memory ((setup s).regs 4)).toNat from k.2.2.2.2.2.2,setup_return]; rfl
  · simpa [fraction,(setup_regs s).2.2.1,BitVec.sub_eq_add_neg,BitVec.add_assoc] using k.1
  · exact k.2.2.2.2.1.trans (setup_regs s).2.2.2


def diagonal (trace : Collision.Divline) (thing : Collision.SolidThing) : Collision.Divline :=
  let p := points trace thing
  ⟨p.1,p.2.1,p.2.2.1-p.1,p.2.2.2-p.2.1⟩
def traceReads : List Word := [0x2ba10,0x2ba14,0x2ba18,0x2ba1c]
def Safe (sp a : Word) : Prop :=
  ∀ off∈[(0#32),4,8,12,-4,-8,-12,-16,-20,-24,-28,-32,-36,-40], Apart a (sp+off)
structure Inputs (s : X86Memory.State) (trace : Collision.Divline) (thing : Collision.SolidThing) : Prop where
  x1 : s.regs 7=(points trace thing).1.raw.toBitVec
  y1 : s.regs 6=(points trace thing).2.1.raw.toBitVec
  x2 : load32 s.memory (s.regs 4+(20#32))=(points trace thing).2.2.1.raw.toBitVec
  y2 : s.regs 5=(points trace thing).2.2.2.raw.toBitVec
  tx : load32 s.memory (0x2ba10#32)=trace.x.raw.toBitVec
  ty : load32 s.memory (0x2ba14#32)=trace.y.raw.toBitVec
  tdx : load32 s.memory (0x2ba18#32)=trace.dx.raw.toBitVec
  tdy : load32 s.memory (0x2ba1c#32)=trace.dy.raw.toBitVec
  safe : ∀ a∈traceReads, Safe (s.regs 4) a
def localMemory (s : X86Memory.State) (line : Collision.Divline) :=
  store32 (store32 (store32 (store32 (store32 s.memory (s.regs 4) line.x.raw.toBitVec)
    (s.regs 4+(4#32)) line.y.raw.toBitVec) (s.regs 4+(8#32)) line.dx.raw.toBitVec)
    (s.regs 4+(12#32)) line.dy.raw.toBitVec) (s.regs 4-(4#32)) (0x2c7d1#32)

theorem setup_memory (s : X86Memory.State) (trace : Collision.Divline) (thing : Collision.SolidThing)
    (h : Inputs s trace thing) : (setup s).memory=localMemory s (diagonal trace thing) := by
  have sub (a b : Fixed) : (a-b).raw.toBitVec=a.raw.toBitVec-b.raw.toBitVec := by
    change (a.raw-b.raw).toBitVec=_
    exact Int32.toBitVec_sub
  simp [setup,step1,step2,step3,step4,step5,step6,step7,step8,step9,X86Routine.pushWord,put,write,localMemory,diagonal,h.x1,h.y1,h.x2,h.y2,sub]
theorem local_frame (s : X86Memory.State) (line : Collision.Divline) (a : Word)
    (safe : ∀ off∈[(0#32),4,8,12,-4], Apart a (s.regs 4+off)) :
    load32 (localMemory s line) a=load32 s.memory a := by
  unfold localMemory
  rw [load_store_apart _ _ _ _ (by simpa only [BitVec.sub_eq_add_neg] using safe (-(4#32)) (by simp))]
  rw [load_store_apart _ _ _ _ (safe (12#32) (by simp)),load_store_apart _ _ _ _ (safe (8#32) (by simp)),load_store_apart _ _ _ _ (safe (4#32) (by simp))]
  exact load_store_apart _ _ _ _ (by simpa only [BitVec.add_zero] using safe (0#32) (by simp))
theorem local_x (s : X86Memory.State) (line : Collision.Divline) : load32 (localMemory s line) (s.regs 4+(0#32))=line.x.raw.toBitVec := by
  unfold localMemory
  rw [load_store_apart _ _ _ _ (by simpa only [BitVec.sub_eq_add_neg,BitVec.add_zero] using OriginalPathXStep.apart_translate (s.regs 4) (0#32) (-(4#32)) (by unfold Apart; decide))]
  rw [load_store_apart _ _ _ _ (by simpa only [BitVec.sub_eq_add_neg,BitVec.add_zero] using OriginalPathXStep.apart_translate (s.regs 4) (0#32) (12#32) (by unfold Apart; decide))]
  rw [load_store_apart _ _ _ _ (by simpa only [BitVec.sub_eq_add_neg,BitVec.add_zero] using OriginalPathXStep.apart_translate (s.regs 4) (0#32) (8#32) (by unfold Apart; decide))]
  rw [load_store_apart _ _ _ _ (by simpa only [BitVec.sub_eq_add_neg,BitVec.add_zero] using OriginalPathXStep.apart_translate (s.regs 4) (0#32) (4#32) (by unfold Apart; decide))]
  simp only [BitVec.add_zero]
  rw [load_store]
theorem local_y (s : X86Memory.State) (line : Collision.Divline) : load32 (localMemory s line) (s.regs 4+(4#32))=line.y.raw.toBitVec := by
  unfold localMemory
  rw [load_store_apart _ _ _ _ (by simpa only [BitVec.sub_eq_add_neg,BitVec.add_zero] using OriginalPathXStep.apart_translate (s.regs 4) (4#32) (-(4#32)) (by unfold Apart; decide))]
  rw [load_store_apart _ _ _ _ (by simpa only [BitVec.sub_eq_add_neg,BitVec.add_zero] using OriginalPathXStep.apart_translate (s.regs 4) (4#32) (12#32) (by unfold Apart; decide))]
  rw [load_store_apart _ _ _ _ (by simpa only [BitVec.sub_eq_add_neg,BitVec.add_zero] using OriginalPathXStep.apart_translate (s.regs 4) (4#32) (8#32) (by unfold Apart; decide))]
  rw [load_store]
theorem local_dx (s : X86Memory.State) (line : Collision.Divline) : load32 (localMemory s line) (s.regs 4+(8#32))=line.dx.raw.toBitVec := by
  unfold localMemory
  rw [load_store_apart _ _ _ _ (by simpa only [BitVec.sub_eq_add_neg,BitVec.add_zero] using OriginalPathXStep.apart_translate (s.regs 4) (8#32) (-(4#32)) (by unfold Apart; decide))]
  rw [load_store_apart _ _ _ _ (by simpa only [BitVec.sub_eq_add_neg,BitVec.add_zero] using OriginalPathXStep.apart_translate (s.regs 4) (8#32) (12#32) (by unfold Apart; decide))]
  rw [load_store]
theorem local_dy (s : X86Memory.State) (line : Collision.Divline) : load32 (localMemory s line) (s.regs 4+(12#32))=line.dy.raw.toBitVec := by
  unfold localMemory
  rw [load_store_apart _ _ _ _ (by simpa only [BitVec.sub_eq_add_neg,BitVec.add_zero] using OriginalPathXStep.apart_translate (s.regs 4) (12#32) (-(4#32)) (by unfold Apart; decide))]
  rw [load_store]

theorem encoded (s : X86Memory.State) (trace : Collision.Divline) (thing : Collision.SolidThing)
    (h : Inputs s trace thing) :
    OriginalInterceptVector.Inputs (setup s) trace (diagonal trace thing) 0x2ba10 (s.regs 4) := by
  let line := diagonal trace thing
  have regs := setup_regs s
  have mem := setup_memory s trace thing h
  have keep (a : Word) (ha : a∈traceReads) : load32 (setup s).memory a=load32 s.memory a := by
    rw [mem]; apply local_frame
    intro off ho
    exact h.safe a ha off (by simp only [List.mem_cons,List.not_mem_nil,or_false] at ho ⊢; rcases ho with rfl|rfl|rfl|rfl|rfl <;> simp)
  refine ⟨regs.1,regs.2.1,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · change load32 (setup s).memory (0x2ba10#32)=_; rw [keep _ (by simp [traceReads]),h.tx]
  · change load32 (setup s).memory (0x2ba14#32)=_; rw [keep _ (by simp [traceReads]),h.ty]
  · change load32 (setup s).memory (0x2ba18#32)=_; rw [keep _ (by simp [traceReads]),h.tdx]
  · change load32 (setup s).memory (0x2ba1c#32)=_; rw [keep _ (by simp [traceReads]),h.tdy]
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
    have traceSep (a : Word) (ha : a∈traceReads) : Apart a (s.regs 4-(4#32)-off) := by
      have offmem : -(4#32)-off∈[(0#32),4,8,12,-4,-8,-12,-16,-20,-24,-28,-32,-36,-40] := by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at ho
        rcases ho with rfl|rfl|rfl|rfl|rfl <;> decide
      simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using h.safe a ha (-(4#32)-off) offmem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact traceSep _ (by simp [traceReads])
    · exact traceSep _ (by simp [traceReads])
    · exact traceSep _ (by simp [traceReads])
    · exact traceSep _ (by simp [traceReads])
    · simpa only [BitVec.add_zero] using localSep (0#32) off (by simp) ho
    · exact localSep (4#32) off (by simp) ho
    · exact localSep (8#32) off (by simp) ho
    · exact localSep (12#32) off (by simp) ho

theorem live (s : X86Memory.State) (trace : Collision.Divline) (thing : Collision.SolidThing)
    (h : Inputs s trace thing) (frac : Fixed)
    (ok : Collision.interceptVector trace (diagonal trace thing)=.ok frac) :
    (fraction s).core.regs 0=frac.raw.toBitVec := by
  have value := OriginalInterceptVector.live (setup s) trace (diagonal trace thing) 0x2ba10 (s.regs 4)
    (encoded s trace thing h) (by rw [ok]; rfl)
  simpa [fraction,ok,Except.toOption] using value.symm

def tested (s : X86Memory.State) : X86Control.State :=
  if (s.regs 0).toInt<0 then ⟨put s 0 1,some (logical32 (s.regs 0)),0x2c7da⟩
  else ⟨s,some (logical32 (s.regs 0)),0x2c7e4⟩

theorem test_execution (s : X86Memory.State) (f : Option Flags) :
    ∃ n≤3, X86Routine.Prefix program [] n ⟨s,f,0x2c7d1⟩ (tested s) := by
  have flags : logical32 (s.regs 0)=compare32 (s.regs 0) 0 := by simp [logical32,compare32,BitVec.ult_eq_decide]
  have path : ∃ n≤3, X86Routine.Prefix listed [] n ⟨s,f,0x2c7d1⟩ (tested s) := by
    by_cases neg : (s.regs 0).toInt<0
    · refine ⟨3,by omega,?_⟩
      apply X86Routine.Prefix.step (middle:=⟨s,some (logical32 (s.regs 0)),0x2c7d3⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute])
      apply X86Routine.Prefix.step (middle:=⟨s,some (logical32 (s.regs 0)),0x2c7d5⟩) (by simp) (by rfl) (by simp [X86Routine.execute,flags,PlayerHeight.cmp_ge_prop,show ¬0≤(s.regs 0).toInt by omega])
      apply X86Routine.Prefix.step (middle:=tested s) (by simp) (by rfl) (by simp [tested,neg,X86Routine.execute])
      exact .nil _
    · refine ⟨2,by omega,?_⟩
      apply X86Routine.Prefix.step (middle:=⟨s,some (logical32 (s.regs 0)),0x2c7d3⟩) (by simp) (by rfl) (by simp [X86Routine.execute,X86Control.execute])
      apply X86Routine.Prefix.step (middle:=tested s) (by simp) (by rfl) (by simp [tested,neg,X86Routine.execute,flags,PlayerHeight.cmp_ge_prop,show 0≤(s.regs 0).toInt by omega])
      exact .nil _
  obtain ⟨n,hn,path⟩ := path
  exact ⟨n,hn,path.transfer program [] decoded (by simp)⟩

def result (s : X86Memory.State) := tested (fraction s).core

theorem execution (s : X86Memory.State) (f : Option Flags)
    (safe : OriginalInterceptVector.Safe (setup s)) :
    ∃ n≤80, X86Routine.Prefix program [] n ⟨s,f,0x2c7ae⟩ (result s) := by
  obtain ⟨n,hn,a⟩ := fraction_execution s f safe
  obtain ⟨m,hm,b⟩ := test_execution (fraction s).core (fraction s).flags
  rw [OriginalPathXStep.at_pc _ _ (returned s).1] at b
  exact ⟨n+m,by omega,OriginalGroupBounds.prefix_join a b⟩

theorem decision_live (s : X86Memory.State) (trace : Collision.Divline) (thing : Collision.SolidThing)
    (h : Inputs s trace thing) (frac : Fixed)
    (ok : Collision.interceptVector trace (diagonal trace thing)=.ok frac) :
    (result s).pc=(if frac.raw<0 then 0x2c7da else 0x2c7e4) ∧
    (result s).core.regs 0=(if frac.raw<0 then (1#32) else frac.raw.toBitVec) ∧
    (result s).core.regs 4=s.regs 4 ∧ (result s).core.regs 1=s.regs 1 := by
  have v := live s trace thing h frac ok
  have neg : ((fraction s).core.regs 0).toInt<0 ↔ frac.raw<0 := by
    simp [v,Int32.toInt_toBitVec,Int32.lt_iff_toInt_lt]
  unfold result tested
  simp only [neg]
  by_cases hn : frac.raw<0 <;> simp [hn,v,put,write,(returned s).2.1,(returned s).2.2]

theorem production (trace : Collision.Divline) (thing : Collision.SolidThing) (frac : Fixed)
    (crossed : OriginalThingSecondSide.firstSide trace thing≠OriginalThingSecondSide.lastSide trace thing)
    (ok : Collision.interceptVector trace (diagonal trace thing)=.ok frac) :
    Collision.thingIntercept trace thing=.ok (if frac.raw<0 then none else some frac) := by
  rw [OriginalThingDiagonal.production]
  change (if OriginalThingSecondSide.firstSide trace thing == OriginalThingSecondSide.lastSide trace thing then _ else _)=_
  simp only [beq_eq_false_iff_ne.mpr crossed,Bool.false_eq_true,if_false]
  change (do let f ← Collision.interceptVector trace (diagonal trace thing); pure (if f.raw<0 then none else some f))=_
  rw [ok]
  rfl

theorem setup_frame (s : X86Memory.State) (a : Word) (safe : Safe (s.regs 4) a) :
    load32 (setup s).memory a=load32 s.memory a := by
  have keep (m : Memory) (value off : Word) (ho : off∈[(0#32),4,8,12,-4,-8,-12,-16,-20,-24,-28,-32,-36,-40]) :=
    load_store_apart m (s.regs 4+off) a value (safe off ho)
  have keep0 (m : Memory) (value : Word) : load32 (store32 m (s.regs 4) value) a=load32 m a := by
    simpa only [BitVec.add_zero] using keep m value (0#32) (by simp)
  simp [setup,step1,step2,step3,step4,step5,step6,step7,step8,step9,X86Routine.pushWord,
    put,write,BitVec.sub_eq_add_neg,keep,keep0]

theorem frame (s : X86Memory.State) (a : Word) (safe : Safe (s.regs 4) a) :
    load32 (result s).core.memory a=load32 s.memory a := by
  have test (t : X86Memory.State) : (tested t).core.memory=t.memory := by
    unfold tested
    split <;> rfl
  rw [show (result s).core.memory=(fraction s).core.memory from test _]
  apply (OriginalInterceptVector.frame (setup s) a ?_).trans (setup_frame s a safe)
  rw [(setup_regs s).2.2.1]
  intro off ho
  have member : -(4#32)-off∈[(0#32),4,8,12,-4,-8,-12,-16,-20,-24,-28,-32,-36,-40] := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ho
    rcases ho with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
  simpa [BitVec.sub_eq_add_neg,BitVec.add_assoc] using safe (-(4#32)-off) member
end Doom.Proofs.OriginalThingFraction
