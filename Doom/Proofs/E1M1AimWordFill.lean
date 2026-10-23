import Doom.Proofs.E1M1AimSideMemset
import Doom.Verification.X86WordFillRoutine
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
namespace Doom.Proofs.E1M1AimWordFill
open Verification X86 X86Memory X86Control BlockSummary
open X86WordFillRoutine (Knowledge)
def zeros (m : Memory) (a : Word) : Nat → Memory
  | 0 => m
  | n+1 => store32 (zeros m a n) (a+BitVec.ofNat 32 (4*n)) 0

theorem store_zero_keeps (m : Memory) (a b : Word) (h : m b=0) :
    store32 m a 0 b=0 := by simp [store32,h]
theorem zeros_byte (m : Memory) (a : Word) (n j : Nat) (h : j<4*n) :
    zeros m a n (a+BitVec.ofNat 32 j)=0 := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases old : j<4*n
    · exact store_zero_keeps _ _ _ (ih old)
    · have cases : j=4*n ∨ j=4*n+1 ∨ j=4*n+2 ∨ j=4*n+3 := by omega
      rcases cases with h|h|h|h <;> subst j <;>
        simp [zeros,store32,BitVec.ofNat_add,BitVec.add_assoc]
theorem zeros_frame (m : Memory) (a b : Word) (n : Nat)
    (safe : ∀ k<n, Apart b (a+BitVec.ofNat 32 (4*k))) :
    load32 (zeros m a n) b=load32 m b := by
  induction n with
  | zero => rfl
  | succ n ih =>
    exact (load_store_apart _ _ _ _ (safe n (by omega))).trans
      (ih (fun k hk=>safe k (by omega)))
theorem zeros_add (m : Memory) (a : Word) (n k : Nat) :
    zeros m a (n+k)=zeros (zeros m a n) (a+BitVec.ofNat 32 (4*n)) k := by
  induction k with
  | zero => simp [zeros]
  | succ k ih =>
    change store32 (zeros m a (n+k)) (a+BitVec.ofNat 32 (4*(n+k))) 0 = _
    rw [ih]
    simp [Nat.mul_add,BitVec.ofNat_add,BitVec.add_assoc,zeros]

def wordsBytes : List UInt8 := [0xb,0xc9,0x74,0x67,0xa8,0x1f,0x74,0x8,0x89,0x10,0x8d,0x40,0x4,0x49,0x75,0xf4,0x51,0xc1,0xe9,0x2,0x74,0x3a,0x49,0x74,0x29,0x89,0x10,0x89,0x50,0x4,0x49,0x89,0x50,0x8,0x89,0x50,0xc,0x74,0x18,0x38,0x50,0x20,0x89,0x50,0x10,0x89,0x50,0x14,0x49,0x89,0x50,0x18,0x89,0x50,0x1c,0x8d,0x40,0x20,0x75,0xdd,0x8d,0x40,0xf0,0x8d,0x40,0x10,0x89,0x10,0x89,0x50,0x4,0x89,0x50,0x8,0x89,0x50,0xc,0x8d,0x40,0x10,0x59,0x83,0xe1,0x3,0x74,0x15,0x89,0x10,0x8d,0x40,0x4,0x49,0x74,0xd,0x89,0x10,0x8d,0x40,0x4,0x49,0x74,0x5,0x89,0x10,0x8d,0x40,0x4,0xc3]
def program : X86WordFillRoutine.Program := fun pc =>
  if 0x41917≤pc ∧ pc<0x41983 then X86WordFillRoutine.decodeAt wordsBytes (pc-0x41917)
  else X86WordFillRoutine.liftProgram E1M1AimSideMemset.program pc
abbrev op (i : X86Routine.Op) : X86WordFillRoutine.Op := .base (.base (.base (.base i)))
abbrev store (off : Word) := op (.control (.block (.store ⟨some 0,none,0,off⟩ 2)))
abbrev lea (off : Word) := op (.control (.block (.legacy (.lea 0 0 off))))
abbrev jump (z : Bool) (d : Int) := op (.control (.jumpZero z d))
def listed : X86WordFillRoutine.Program
  | 0x41917 => some (.base (.orRegisters 1 1),2)
  | 0x41919 => some (jump true 103,2)
  | 0x4191b => some (op (.testByteImmediate 0 31),2)
  | 0x4191d => some (jump true 8,2)
  | 0x4191f => some (store 0,2)
  | 0x41921 => some (lea 4,3)
  | 0x41924 => some (.decrement 1,1)
  | 0x41925 => some (jump false (-12),2)
  | 0x41927 => some (op (.push 1),1)
  | 0x41928 => some (.shiftRightTwo 1,3)
  | 0x4192b => some (jump true 58,2)
  | 0x4192d => some (.decrement 1,1)
  | 0x4192e => some (jump true 41,2)
  | 0x41930 => some (store 0,2)
  | 0x41932 => some (store 4,3)
  | 0x41935 => some (.decrement 1,1)
  | 0x41936 => some (store 8,3)
  | 0x41939 => some (store 12,3)
  | 0x4193c => some (jump true 24,2)
  | 0x4193e => some (.base (.compareMemoryByte ⟨some 0,none,0,32⟩ 2),3)
  | 0x41941 => some (store 16,3)
  | 0x41944 => some (store 20,3)
  | 0x41947 => some (.decrement 1,1)
  | 0x41948 => some (store 24,3)
  | 0x4194b => some (store 28,3)
  | 0x4194e => some (lea 32,3)
  | 0x41951 => some (jump false (-35),2)
  | 0x41953 => some (lea (-16),3)
  | 0x41956 => some (lea 16,3)
  | 0x41959 => some (store 0,2)
  | 0x4195b => some (store 4,3)
  | 0x4195e => some (store 8,3)
  | 0x41961 => some (store 12,3)
  | 0x41964 => some (lea 16,3)
  | 0x41967 => some (op (.pop 1),1)
  | 0x41968 => some (op (.andRegister 1 3),3)
  | 0x4196b => some (jump true 21,2)
  | 0x4196d => some (store 0,2)
  | 0x4196f => some (lea 4,3)
  | 0x41972 => some (.decrement 1,1)
  | 0x41973 => some (jump true 13,2)
  | 0x41975 => some (store 0,2)
  | 0x41977 => some (lea 4,3)
  | 0x4197a => some (.decrement 1,1)
  | 0x4197b => some (jump true 5,2)
  | 0x4197d => some (store 0,2)
  | 0x4197f => some (lea 4,3)
  | 0x41982 => some (op .ret,1)
  | _ => none
theorem decoded (pc : Nat) (h : listed pc≠none) : program pc=listed pc := by
  fun_cases listed pc <;> simp_all [listed] <;> decide

def firstHalf (s : X86Memory.State) (f : Knowledge) : X86WordFillRoutine.State :=
  ⟨put {s with memory:=zeros s.memory (s.regs 0) 4} 1 (s.regs 1-1),
    .legacy (some {compare32 (s.regs 1) 1 with carry:=f.carry}),0x4193c⟩
def pairResult (s : X86Memory.State) : X86WordFillRoutine.State :=
  ⟨put (put {s with memory:=zeros s.memory (s.regs 0) 8} 1 (s.regs 1-1-1)) 0 (s.regs 0+32),
    .legacy (some {compare32 (s.regs 1-1) 1 with carry:=some false}),0x41930⟩
macro "fill_simp" : tactic => `(tactic| simp [X86WordFillRoutine.execute,
  X86WordFillRoutine.embed,X86WordFillRoutine.preserves,Knowledge.carry,
  X86FillRoutine.execute,X86StartupRoutine.execute,X86ByteRoutine.execute,
  X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,
  X86Block.Address.eval,blockPreservesFlags,put,write,zeros,BitVec.add_assoc])
theorem first_half_execution (s : X86Memory.State) (f : Knowledge) (zero : s.regs 2=0) :
    X86WordFillRoutine.Prefix listed [] 5 ⟨s,f,0x41930⟩ (firstHalf s f) := by
  cases f <;>
    (refine .step (by simp) rfl rfl ?_
     refine .step (by simp) rfl rfl ?_
     refine .step (by simp) rfl rfl ?_
     refine .step (by simp) rfl rfl ?_
     refine .step (middle:=firstHalf s _) (by simp) rfl ?_ (.nil _)
     simp only [firstHalf,zero]
     fill_simp
     simp [zero])
theorem pair_execution (s : X86Memory.State) (f : Knowledge)
    (zero : s.regs 2=0) (first : s.regs 1-1≠0) (second : s.regs 1-1-1≠0) :
    X86WordFillRoutine.Prefix program [] 14 ⟨s,f,0x41930⟩ (pairResult s) := by
  simp only [BitVec.ofNat_eq_ofNat] at first second zero
  have suffix : X86WordFillRoutine.Prefix listed [] 9 (firstHalf s f) (pairResult s) := by
    refine .step (middle:={firstHalf s f with pc:=0x4193e}) (by simp [firstHalf]) rfl ?_ ?_
    · simp [firstHalf,X86WordFillRoutine.execute,X86WordFillRoutine.embed,
        X86FillRoutine.execute,X86StartupRoutine.execute,X86ByteRoutine.execute,
        X86Routine.execute,X86Control.execute,compare32,first]
    refine .step (by simp [firstHalf]) rfl rfl ?_
    refine .step (by simp [firstHalf]) rfl rfl ?_
    refine .step (by simp [firstHalf]) rfl rfl ?_
    refine .step (by simp [firstHalf]) rfl rfl ?_
    refine .step (by simp [firstHalf]) rfl rfl ?_
    refine .step (by simp [firstHalf]) rfl rfl ?_
    refine .step (by simp [firstHalf]) rfl rfl ?_
    refine .step (middle:=pairResult s) (by simp [firstHalf]) rfl ?_ (.nil _)
    simp [firstHalf,pairResult,X86WordFillRoutine.execute,X86WordFillRoutine.embed,
      Knowledge.carry,X86FillRoutine.execute,X86StartupRoutine.execute,X86ByteRoutine.execute,
      X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,
      X86Block.Address.eval,blockPreservesFlags,put,write,zeros,BitVec.add_assoc,
      compare32,X86ByteRoutine.compare8,readByte,byteReg,zero,second,BitVec.ult]
  exact ((first_half_execution s f zero).trans suffix).transfer _ [] decoded (by simp)
def pairs (s : X86Memory.State) : Nat → X86Memory.State
  | 0 => s
  | k+1 => pairs (pairResult s).core k

theorem word_ne_zero (n : Nat) (positive : 0<n) (bound : n<4294967296) :
    BitVec.ofNat 32 n≠(0:Word) := by
  intro h
  have hn := congrArg BitVec.toNat h
  change n%4294967296=0 at hn
  omega

theorem pairs_execution (k r : Nat) (s : X86Memory.State) (f : Knowledge)
    (zero : s.regs 2=0) (count : s.regs 1=BitVec.ofNat 32 (2*k+r))
    (positive : 0<r) (bound : 2*k+r<4294967296) :
    ∃ g, X86WordFillRoutine.Prefix program [] (14*k) ⟨s,f,0x41930⟩
      ⟨pairs s k,g,0x41930⟩ := by
  induction k generalizing s f with
  | zero => exact ⟨f,.nil _⟩
  | succ k ih =>
    have arith : 2*(k+1)+r=(2*k+r)+2 := by omega
    have one : s.regs 1-1=BitVec.ofNat 32 (2*k+r+1) := by
      rw [count,arith]
      simp [BitVec.ofNat_add,BitVec.sub_eq_add_neg,BitVec.add_assoc]
    have two : s.regs 1-1-1=BitVec.ofNat 32 (2*k+r) := by
      rw [one]
      simp [BitVec.ofNat_add,BitVec.sub_eq_add_neg,BitVec.add_assoc]
    have first : s.regs 1-1≠0 := by rw [one]; exact word_ne_zero _ (by omega) (by omega)
    have second : s.regs 1-1-1≠0 := by rw [two]; exact word_ne_zero _ (by omega) (by omega)
    have nextZero : (pairResult s).core.regs 2=0 := by simp [pairResult,put,write,zero]
    have nextCount : (pairResult s).core.regs 1=BitVec.ofNat 32 (2*k+r) := by
      simpa [pairResult,put,write] using two
    obtain ⟨g,rest⟩ := ih (pairResult s).core (pairResult s).flags nextZero nextCount (by omega)
    refine ⟨g,?_⟩
    have joined := (pair_execution s f zero first second).trans rest
    simpa [pairs,Nat.mul_add,Nat.add_comm] using joined

theorem pairs_memory (s : X86Memory.State) (k : Nat) :
    (pairs s k).memory=zeros s.memory (s.regs 0) (8*k) := by
  induction k generalizing s with
  | zero => rfl
  | succ k ih =>
    rw [pairs,ih]
    simp only [pairResult,put,write,ite_true]
    rw [show 8*(k+1)=8+8*k by omega,zeros_add]
    rfl

theorem pairs_registers (s : X86Memory.State) (k : Nat) :
    (pairs s k).regs=write (write s.regs 1 (s.regs 1-BitVec.ofNat 32 (2*k)))
      0 (s.regs 0+BitVec.ofNat 32 (32*k)) := by
  induction k generalizing s with
  | zero => funext r; by_cases h : r=0 <;> by_cases h1 : r=1 <;> simp [pairs,write,h,h1]
  | succ k ih =>
    rw [pairs,ih]
    funext r
    by_cases h : r=0 <;> by_cases h1 : r=1 <;>
      simp [pairResult,put,write,h,h1,Nat.mul_add,BitVec.ofNat_add,
        BitVec.sub_eq_add_neg,BitVec.neg_add,BitVec.add_assoc,BitVec.add_comm] <;>
      first | ac_rfl | (rw [←BitVec.add_assoc]; rfl)
def doneCore (s : X86Memory.State) (words : Nat) : X86Memory.State :=
  put (put {s with memory:=zeros s.memory (s.regs 0) words} 1 0) 0
    (s.regs 0+BitVec.ofNat 32 (4*words))

theorem terminal_execution (s : X86Memory.State) (f : Knowledge)
    (zero : s.regs 2=0) (r : Nat) (small : r=1 ∨ r=2)
    (count : s.regs 1=BitVec.ofNat 32 r) :
    ∃ n≤21, ∃ g, X86WordFillRoutine.Prefix program [] n ⟨s,f,0x41930⟩
      ⟨doneCore s (4*(r+1)),g,0x41967⟩ := by
  rcases small with hr|hr <;> subst r
  · let g : Knowledge := .legacy (some {compare32 1 1 with carry:=f.carry})
    have suffix : X86WordFillRoutine.Prefix listed [] 7 (firstHalf s f)
        ⟨doneCore s 8,g,0x41967⟩ := by
      refine .step (middle:={firstHalf s f with pc:=0x41956}) (by simp [firstHalf]) rfl ?_ ?_
      · simp [firstHalf,X86WordFillRoutine.execute,X86WordFillRoutine.embed,
          X86FillRoutine.execute,X86StartupRoutine.execute,X86ByteRoutine.execute,
          X86Routine.execute,X86Control.execute,compare32,count]
      refine .step (by simp [firstHalf]) rfl rfl ?_
      refine .step (by simp [firstHalf]) rfl rfl ?_
      refine .step (by simp [firstHalf]) rfl rfl ?_
      refine .step (by simp [firstHalf]) rfl rfl ?_
      refine .step (by simp [firstHalf]) rfl rfl ?_
      refine .step (middle:=⟨doneCore s 8,g,0x41967⟩) (by simp [firstHalf]) rfl ?_ (.nil _)
      simp [firstHalf,doneCore,g,X86WordFillRoutine.execute,X86WordFillRoutine.embed,
        Knowledge.carry,X86FillRoutine.execute,X86StartupRoutine.execute,X86ByteRoutine.execute,
        X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,
        X86Block.Address.eval,blockPreservesFlags,put,write,zeros,BitVec.add_assoc,zero,count]
    exact ⟨12,by omega,g,((first_half_execution s f zero).trans suffix).transfer _ [] decoded (by simp)⟩
  · let g : Knowledge := .legacy (some {compare32 1 1 with carry:=some false})
    have middle : X86WordFillRoutine.Prefix listed [] 9 (firstHalf s f)
        {pairResult s with pc:=0x41953} := by
      refine .step (middle:={firstHalf s f with pc:=0x4193e}) (by simp [firstHalf]) rfl ?_ ?_
      · simp [firstHalf,X86WordFillRoutine.execute,X86WordFillRoutine.embed,
          X86FillRoutine.execute,X86StartupRoutine.execute,X86ByteRoutine.execute,
          X86Routine.execute,X86Control.execute,compare32,count]
      refine .step (by simp [firstHalf]) rfl rfl ?_
      refine .step (by simp [firstHalf]) rfl rfl ?_
      refine .step (by simp [firstHalf]) rfl rfl ?_
      refine .step (by simp [firstHalf]) rfl rfl ?_
      refine .step (by simp [firstHalf]) rfl rfl ?_
      refine .step (by simp [firstHalf]) rfl rfl ?_
      refine .step (by simp [firstHalf]) rfl rfl ?_
      refine .step (middle:={pairResult s with pc:=0x41953}) (by simp [firstHalf]) rfl ?_ (.nil _)
      simp [firstHalf,pairResult,X86WordFillRoutine.execute,X86WordFillRoutine.embed,
        Knowledge.carry,X86FillRoutine.execute,X86StartupRoutine.execute,X86ByteRoutine.execute,
        X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,
        X86Block.Address.eval,blockPreservesFlags,put,write,zeros,BitVec.add_assoc,
        compare32,X86ByteRoutine.compare8,readByte,byteReg,zero,count,BitVec.ult]
    have suffix : X86WordFillRoutine.Prefix listed [] 7 {pairResult s with pc:=0x41953}
        ⟨doneCore s 12,g,0x41967⟩ := by
      refine .step (by simp [pairResult]) rfl rfl ?_
      refine .step (by simp [pairResult]) rfl rfl ?_
      refine .step (by simp [pairResult]) rfl rfl ?_
      refine .step (by simp [pairResult]) rfl rfl ?_
      refine .step (by simp [pairResult]) rfl rfl ?_
      refine .step (by simp [pairResult]) rfl rfl ?_
      refine .step (middle:=⟨doneCore s 12,g,0x41967⟩) (by simp [pairResult]) rfl ?_ (.nil _)
      simp [pairResult,doneCore,g,X86WordFillRoutine.execute,X86WordFillRoutine.embed,
        Knowledge.carry,X86FillRoutine.execute,X86StartupRoutine.execute,X86ByteRoutine.execute,
        X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,
        X86Block.Address.eval,blockPreservesFlags,put,write,zeros,BitVec.add_assoc,zero,count]
    exact ⟨21,by omega,g,(((first_half_execution s f zero).trans middle).trans suffix).transfer _ [] decoded (by simp)⟩
theorem done_pairs (s : X86Memory.State) (k w : Nat) :
    doneCore (pairs s k) w=doneCore s (8*k+w) := by
  simp only [doneCore,put,pairs_registers,pairs_memory,write,ite_true,show (0:Reg)≠1 by decide,ite_false]
  congr 1
  · funext r
    by_cases h : r=0 <;> by_cases h1 : r=1 <;>
      simp [write,h,h1,Nat.mul_add,BitVec.ofNat_add,BitVec.add_assoc,←Nat.mul_assoc]
  · rw [zeros_add]
    simp [←Nat.mul_assoc]

theorem groups_execution (k r : Nat) (s : X86Memory.State) (f : Knowledge)
    (zero : s.regs 2=0) (count : s.regs 1=BitVec.ofNat 32 (2*k+r))
    (small : r=1 ∨ r=2) (bound : 2*k+r<4294967296) :
    ∃ n≤14*k+21, ∃ g, X86WordFillRoutine.Prefix program [] n ⟨s,f,0x41930⟩
      ⟨doneCore s (8*k+4*(r+1)),g,0x41967⟩ := by
  obtain ⟨g,lead⟩ := pairs_execution k r s f zero count (by omega) bound
  have nextZero : (pairs s k).regs 2=0 := by rw [pairs_registers]; simp [write,zero]
  have nextCount : (pairs s k).regs 1=BitVec.ofNat 32 r := by
    rw [pairs_registers]
    simp [write,count,BitVec.ofNat_add,BitVec.add_sub_comm]
  obtain ⟨n,hb,final,suffix⟩ := terminal_execution (pairs s k) g nextZero r small nextCount
  refine ⟨14*k+n,by omega,final,?_⟩
  have joined := lead.trans suffix
  rwa [done_pairs] at joined
def groupStart32 (s : X86Memory.State) : X86WordFillRoutine.State :=
  ⟨put (X86Routine.pushWord s 2916) 1 728,
    .legacy (some {compare32 729 1 with carry:=none}),0x41930⟩
def filled32 (s : X86Memory.State) : X86Memory.State := doneCore (groupStart32 s).core 2916

theorem aligned32_setup (s : X86Memory.State) (f : Knowledge)
    (count : s.regs 1=2916) (aligned32 : readByte s.regs 0 &&& 31=0) :
    X86WordFillRoutine.Prefix program [] 9 ⟨s,f,0x41917⟩ (groupStart32 s) := by
  simp only [BitVec.ofNat_eq_ofNat] at count aligned32
  have path : X86WordFillRoutine.Prefix listed [] 9 ⟨s,f,0x41917⟩ (groupStart32 s) := by
    refine .step (middle:=⟨s,.legacy (some (logical32 2916)),0x41919⟩) (by simp) rfl ?_ ?_
    · have regs : write s.regs 1 2916=s.regs := by
        funext r; by_cases h : r=1 <;> simp [write,h,count]
      simp only [BitVec.ofNat_eq_ofNat] at regs
      cases f <;> simp [X86WordFillRoutine.execute,X86WordFillRoutine.embed,
        X86WordFillRoutine.preserves,X86FillRoutine.execute,put,count,regs]
    refine .step (middle:=⟨s,.legacy (some (logical32 2916)),0x4191b⟩) (by simp) rfl rfl ?_
    refine .step (by simp) rfl rfl ?_
    refine .step (middle:=⟨s,.legacy (some (logical8 0)),0x41927⟩) (by simp) rfl ?_ ?_
    · simp [X86WordFillRoutine.execute,X86WordFillRoutine.embed,
        X86FillRoutine.execute,X86StartupRoutine.execute,X86ByteRoutine.execute,
        X86Routine.execute,X86Control.execute,aligned32,logical8]
    refine .step (by simp) rfl rfl ?_
    refine .step (by simp) rfl rfl ?_
    refine .step (middle:=⟨put (X86Routine.pushWord s 2916) 1 729,.zeroOnly false,0x4192d⟩)
      (by simp) rfl ?_ ?_
    · simp [X86WordFillRoutine.execute,X86WordFillRoutine.embed,
        X86FillRoutine.execute,X86StartupRoutine.execute,X86ByteRoutine.execute,
        X86Routine.execute,X86Routine.pushWord,put,write,count]
    refine .step (by simp) rfl rfl ?_
    refine .step (middle:=groupStart32 s) (by simp) rfl ?_ (.nil _)
    simp [X86WordFillRoutine.execute,X86WordFillRoutine.embed,Knowledge.carry,groupStart32,
      X86FillRoutine.execute,X86StartupRoutine.execute,X86ByteRoutine.execute,
      X86Routine.execute,X86Control.execute,X86Routine.pushWord,put,write,count,compare32]
  exact path.transfer _ [] decoded (by simp)

theorem aligned32_body (s : X86Memory.State) (f : Knowledge)
    (count : s.regs 1=2916) (zero : s.regs 2=0)
    (aligned32 : readByte s.regs 0 &&& 31=0) :
    (∃ n≤5112, ∃ g, X86WordFillRoutine.Prefix program [] n ⟨s,f,0x41917⟩
      ⟨filled32 s,g,0x41967⟩) ∧
    (∀ j<11664, (filled32 s).memory (s.regs 0+BitVec.ofNat 32 j)=0) := by
  have nextZero : (groupStart32 s).core.regs 2=0 := by simp [groupStart32,X86Routine.pushWord,put,write,zero]
  have nextCount : (groupStart32 s).core.regs 1=BitVec.ofNat 32 (2*363+2) := by
    simp [groupStart32,X86Routine.pushWord,put,write]
  obtain ⟨n,bound,g,path⟩ := groups_execution 363 2 (groupStart32 s).core
    (groupStart32 s).flags nextZero nextCount (by simp) (by decide)
  constructor
  · exact ⟨9+n,by omega,g,(aligned32_setup s f count aligned32).trans path⟩
  · intro j hj
    simpa [filled32,doneCore,groupStart32,X86Routine.pushWord,put,write] using
      zeros_byte (X86Routine.pushWord s 2916).memory (s.regs 0) 2916 j hj
def returnListing : X86WordFillRoutine.Program
  | 0x41967 => some (op (.pop 1),1)
  | 0x41968 => some (op (.andRegister 1 3),3)
  | 0x4196b => some (jump true 21,2)
  | 0x41982 => some (op .ret,1)
  | 0x418fc => some (op (.pop 1),1)
  | 0x418fd => some (op (.andRegister 1 3),3)
  | 0x41900 => some (jump true 14,2)
  | 0x41910 => some (op .ret,1)
  | 0x3fe85 => some (op (.pop 1),1)
  | 0x3fe86 => some (op (.pop 0),1)
  | 0x3fe87 => some (op .ret,1)
  | _ => none
theorem returns_decoded (pc : Nat) (h : returnListing pc≠none) : program pc=returnListing pc := by
  fun_cases returnListing pc <;> simp_all [returnListing] <;> decide

def ReturnWords (s : X86Memory.State) (base : Word) : Prop :=
  load32 s.memory (s.regs 4)=2916 ∧
  load32 s.memory (s.regs 4+4)=0x418fc ∧
  load32 s.memory (s.regs 4+8)=11664 ∧
  load32 s.memory (s.regs 4+12)=0x3fe85 ∧
  load32 s.memory (s.regs 4+16)=9 ∧
  load32 s.memory (s.regs 4+20)=base ∧
  load32 s.memory (s.regs 4+24)=0x2e437
def returned (s : X86Memory.State) (base : Word) : X86WordFillRoutine.State :=
  ⟨put (put (put s 1 9) 0 base) 4 (s.regs 4+28),.legacy (some (logical32 0)),0x2e437⟩

theorem returns_execution (s : X86Memory.State) (f : Knowledge) (base : Word)
    (saved : ReturnWords s base) :
    X86WordFillRoutine.Prefix program [] 11 ⟨s,f,0x41967⟩ (returned s base) := by
  rcases saved with ⟨h0,h4,h8,h12,h16,h20,h24⟩
  simp only [BitVec.ofNat_eq_ofNat] at h0 h4 h8 h12 h16 h20 h24
  let a := put (put s 4 (s.regs 4+4)) 1 0
  let b := put (put s 4 (s.regs 4+12)) 1 0
  have path : X86WordFillRoutine.Prefix returnListing [] 11 ⟨s,f,0x41967⟩ (returned s base) := by
    cases f <;>
      (refine .step (by simp) rfl rfl ?_
       refine .step (by simp) rfl rfl ?_
       refine .step (middle:=⟨a,.legacy (some (logical32 0)),0x41982⟩) (by simp) rfl ?_ ?_)
    all_goals first
      | (simp [a,X86WordFillRoutine.execute,X86WordFillRoutine.embed,X86WordFillRoutine.preserves,
          X86FillRoutine.execute,X86StartupRoutine.execute,X86ByteRoutine.execute,
          X86Routine.execute,X86Control.execute,put,write,h0,logical32])
      | skip
    all_goals
      refine .step (middle:=⟨put a 4 (s.regs 4+8),.legacy (some (logical32 0)),0x418fc⟩)
        (by simp) rfl ?_ ?_
      · simp [a,X86WordFillRoutine.execute,X86WordFillRoutine.embed,
          X86FillRoutine.execute,X86StartupRoutine.execute,X86ByteRoutine.execute,
          X86Routine.execute,X86Control.execute,put,write,h4,BitVec.add_assoc,logical32]
      refine .step (by simp) rfl rfl ?_
      refine .step (by simp) rfl rfl ?_
      refine .step (middle:=⟨b,.legacy (some (logical32 0)),0x41910⟩) (by simp) rfl ?_ ?_
      · simp [a,b,X86WordFillRoutine.execute,X86WordFillRoutine.embed,
          X86FillRoutine.execute,X86StartupRoutine.execute,X86ByteRoutine.execute,
          X86Routine.execute,X86Control.execute,put,write,h8,logical32,BitVec.add_assoc]
        funext r
        by_cases h : r=4 <;> by_cases h1 : r=1 <;> simp [write,h,h1]
      refine .step (middle:=⟨put b 4 (s.regs 4+16),.legacy (some (logical32 0)),0x3fe85⟩)
        (by simp) rfl ?_ ?_
      · simp [b,X86WordFillRoutine.execute,X86WordFillRoutine.embed,
          X86FillRoutine.execute,X86StartupRoutine.execute,X86ByteRoutine.execute,
          X86Routine.execute,X86Control.execute,put,write,h12,BitVec.add_assoc]
      refine .step (by simp) rfl rfl ?_
      refine .step (by simp) rfl rfl ?_
      refine .step (middle:=returned s base) (by simp) rfl ?_ (.nil _)
      simp [b,returned,X86WordFillRoutine.execute,X86WordFillRoutine.embed,
        X86FillRoutine.execute,X86StartupRoutine.execute,X86ByteRoutine.execute,
        X86Routine.execute,X86Control.execute,put,write,h16,h20,h24,BitVec.add_assoc]
      funext r
      by_cases h : r=4 <;> by_cases h1 : r=1 <;> by_cases h0 : r=0 <;> simp [write,h,h1,h0]
  exact path.transfer _ [] returns_decoded (by simp)
theorem previous_agrees (pc : Nat)
    (h : X86WordFillRoutine.liftProgram E1M1AimSideMemset.program pc≠none) :
    program pc=X86WordFillRoutine.liftProgram E1M1AimSideMemset.program pc := by
  by_cases word : 0x41917≤pc ∧ pc<0x41983
  · have a : ¬(0x3fe70≤pc ∧ pc<0x3fe88) := by omega
    have b : ¬(0x418e0≤pc ∧ pc<0x41911) := by omega
    have c : ¬((0x2e3e0≤pc ∧ pc<0x2e445) ∨ (0x38bb0≤pc ∧ pc<0x38be4)) := by omega
    have d : ¬((0x2e639≤pc ∧ pc<0x2e63e) ∨ (0x39690≤pc ∧ pc<0x396f8)) := by omega
    have e : ¬(0x396f8≤pc ∧ pc<0x39731) := by omega
    have g : ¬(0x39731≤pc ∧ pc<0x39776) := by omega
    have i : ¬(0x2e63e≤pc ∧ pc<0x2e661) := by omega
    have j : ¬(0x241c0≤pc ∧ pc<0x241dc) := by omega
    simp [X86WordFillRoutine.liftProgram,E1M1AimSideMemset.program,E1M1AimSideMemset.bytesProgram,
      X86FillRoutine.liftProgram,E1M1AimSideAllocate.program,E1M1AimSideAllocate.lift,
      X86StartupRoutine.liftProgram,X86ByteRoutine.liftProgram,OriginalGroupMalloc.program,
      OriginalGroupSelected.program,OriginalGroupHandoff.program,OriginalGroupEntry.program,
      OriginalGroupEntry.bytesProgram,a,b,c,d,e,g,i,j] at h
  · simp [program,word]

/-- Static separation from every output store of the actual seven nested stack words. -/
def Saved32Safe (s : X86Memory.State) : Prop :=
  ∀ i : Fin 7, ∀ k<2916, Apart (s.regs 4-24+BitVec.ofNat 32 (4*i.val))
    (s.regs 0+BitVec.ofNat 32 (4*k))

def pushed32 (s : X86Memory.State) := (groupStart32 (E1M1AimSideMemset.wordsCalled s).core).core

theorem pushed_return_words (s : X86Memory.State) (index : s.regs 1=9)
    (ret : load32 s.memory (s.regs 4)=0x2e437) : ReturnWords (pushed32 s) (s.regs 0) := by
  simp only [load32,BitVec.ofNat_eq_ofNat] at ret
  simp [ReturnWords,pushed32,groupStart32,E1M1AimSideMemset.wordsCalled,
    E1M1AimSideMemset.callWords,E1M1AimSideMemset.fillCalled,X86Routine.pushWord,put,write,
    load32,store32,BitVec.sub_eq_add_neg,BitVec.add_assoc,index,ret]
  have h := load_store (fun _=>0) 0 (s.regs 0)
  simpa [load32,store32] using h

theorem filled_return_words (s : X86Memory.State) (index : s.regs 1=9)
    (ret : load32 s.memory (s.regs 4)=0x2e437) (safe : Saved32Safe s) :
    ReturnWords (filled32 (E1M1AimSideMemset.wordsCalled s).core) (s.regs 0) := by
  have frame (i : Fin 7) :
      load32 (filled32 (E1M1AimSideMemset.wordsCalled s).core).memory
        (s.regs 4-24+BitVec.ofNat 32 (4*i.val)) =
      load32 (pushed32 s).memory (s.regs 4-24+BitVec.ofNat 32 (4*i.val)) := by
    exact zeros_frame (pushed32 s).memory (s.regs 0)
      (s.regs 4-24+BitVec.ofNat 32 (4*i.val)) 2916 (safe i)
  have sp : (filled32 (E1M1AimSideMemset.wordsCalled s).core).regs 4=s.regs 4-24 := by
    simp [filled32,doneCore,pushed32,groupStart32,E1M1AimSideMemset.wordsCalled,
      E1M1AimSideMemset.callWords,E1M1AimSideMemset.fillCalled,X86Routine.pushWord,put,write,
      BitVec.sub_eq_add_neg,BitVec.add_assoc]
  have oldsp : (pushed32 s).regs 4=s.regs 4-24 := by
    simp [pushed32,groupStart32,E1M1AimSideMemset.wordsCalled,
      E1M1AimSideMemset.callWords,E1M1AimSideMemset.fillCalled,X86Routine.pushWord,put,write,
      BitVec.sub_eq_add_neg,BitVec.add_assoc]
  have old := pushed_return_words s index ret
  simp only [ReturnWords,oldsp] at old
  simp only [ReturnWords,sp]
  have frame0 : load32 (filled32 (E1M1AimSideMemset.wordsCalled s).core).memory (s.regs 4-24)=
      load32 (pushed32 s).memory (s.regs 4-24) := by
    simpa only [Fin.val_zero,Nat.mul_zero,BitVec.ofNat_eq_ofNat,BitVec.add_zero] using frame 0
  exact And.intro (frame0.trans old.1) (And.intro ((frame 1).trans old.2.1)
      (And.intro ((frame 2).trans old.2.2.1) (And.intro ((frame 3).trans old.2.2.2.1)
      (And.intro ((frame 4).trans old.2.2.2.2.1) (And.intro ((frame 5).trans old.2.2.2.2.2.1)
        ((frame 6).trans old.2.2.2.2.2.2))))))

def completed32 (s : X86Memory.State) :=
  returned (filled32 (E1M1AimSideMemset.wordsCalled s).core) (s.regs 0)

theorem memset32_execution (s : X86Memory.State) (f : Option Flags)
    (zero : s.regs 2=0) (size : s.regs 3=11664) (index : s.regs 1=9)
    (ret : load32 s.memory (s.regs 4)=0x2e437)
    (aligned32 : readByte s.regs 0 &&& 31=0) (safe : Saved32Safe s) :
    (∃ n≤5140, X86WordFillRoutine.Prefix program [] n (X86WordFillRoutine.embed ⟨s,f,0x3fe70⟩)
      (completed32 s)) ∧ (completed32 s).pc=0x2e437 ∧
      (∀ j<11664, (completed32 s).core.memory (s.regs 0+BitVec.ofNat 32 j)=0) := by
  have aligned4 : readByte s.regs 0 &&& 3=0 := by
    have := congrArg (fun x : BitVec 8=>x &&& 3) aligned32
    simpa [BitVec.and_assoc] using this
  have lead := (X86WordFillRoutine.lift_prefix
    (E1M1AimSideMemset.nested_execution s f zero size aligned4)).transfer program [] previous_agrees (by simp)
  have wc : (E1M1AimSideMemset.wordsCalled s).core.regs 1=2916 := by
    simp [E1M1AimSideMemset.wordsCalled,E1M1AimSideMemset.callWords,X86Routine.pushWord,put,write]
  have wz : (E1M1AimSideMemset.wordsCalled s).core.regs 2=0 := by
    simp [E1M1AimSideMemset.wordsCalled,E1M1AimSideMemset.callWords,E1M1AimSideMemset.fillCalled,X86Routine.pushWord,put,write]
  have wa : readByte (E1M1AimSideMemset.wordsCalled s).core.regs 0 &&& 31=0 := by
    simpa [readByte,byteReg,E1M1AimSideMemset.wordsCalled,E1M1AimSideMemset.callWords,
      E1M1AimSideMemset.fillCalled,X86Routine.pushWord,put,write] using aligned32
  obtain ⟨⟨n,bound,g,body⟩,zeros⟩ := aligned32_body (E1M1AimSideMemset.wordsCalled s).core (.legacy none) wc wz wa
  have tail := returns_execution (filled32 (E1M1AimSideMemset.wordsCalled s).core) g (s.regs 0)
    (filled_return_words s index ret safe)
  refine ⟨⟨17+n+11,by omega,(lead.trans body).trans tail⟩,rfl,?_⟩
  simpa [completed32,returned,put,E1M1AimSideMemset.wordsCalled,E1M1AimSideMemset.callWords,
    E1M1AimSideMemset.fillCalled,X86Routine.pushWord,write] using zeros
theorem filled32_frame (s : X86Memory.State) (a : Word)
    (stack : Apart a (s.regs 4-4))
    (safe : ∀ k<2916, Apart a (s.regs 0+BitVec.ofNat 32 (4*k))) :
    load32 (filled32 s).memory a=load32 s.memory a := by
  exact (zeros_frame (store32 s.memory (s.regs 4-4) 2916) (s.regs 0) a 2916 safe).trans
    (load_store_apart _ _ _ _ stack)

def Entry32Safe (s : X86Memory.State) (v : OriginalGroupHeap.View) : Prop :=
  ∀ i : Fin 7, ∀ k<2916, Apart (s.regs 4-60+BitVec.ofNat 32 (4*i.val))
    (v.block+24+BitVec.ofNat 32 (4*k))
def finished32 (s : X86Memory.State) := completed32 (E1M1AimSidePublish.published s).core

theorem entry32_execution (s : X86Memory.State) (f : Option Flags) (table : Word)
    (h : E1M1AimSideEntry.Initial s table) (v : OriginalGroupHeap.View)
    (heap : E1M1AimSideAllocate.HeapInitial s v) (frame : E1M1AimSidePublish.AllocationFrame s v)
    (aligned32 : (v.block+24).extractLsb' 0 8 &&& 31=0) (safe : Entry32Safe s v) :
    (∃ n≤5240, X86WordFillRoutine.Prefix program [] n (X86WordFillRoutine.embed ⟨s,f,0x2e3e0⟩)
      (finished32 s)) ∧ (finished32 s).pc=0x2e437 ∧
      (∀ j<11664, (finished32 s).core.memory (v.block+24+BitVec.ofNat 32 j)=0) := by
  obtain ⟨⟨n,bound,path⟩,pc,base,index,zero,size,sp,ret⟩ :=
    E1M1AimSidePublish.execution s f table h v heap frame
  have align : readByte (E1M1AimSidePublish.published s).core.regs 0 &&& 31=0 := by
    simpa [readByte,byteReg,base] using aligned32
  have stack : Saved32Safe (E1M1AimSidePublish.published s).core := by
    simpa [Saved32Safe,Entry32Safe,sp,base,BitVec.sub_eq_add_neg,BitVec.add_assoc] using safe
  obtain ⟨⟨m,mb,suffix⟩,endpc,zeros⟩ := memset32_execution (E1M1AimSidePublish.published s).core
    (E1M1AimSidePublish.published s).flags zero size index ret align stack
  have seam : (⟨(E1M1AimSidePublish.published s).core,(E1M1AimSidePublish.published s).flags,
      0x3fe70⟩ : X86Control.State)=E1M1AimSidePublish.published s := by rw [←pc]
  rw [seam] at suffix
  have lead := (X86WordFillRoutine.lift_prefix ((X86FillRoutine.lift_prefix path).transfer
    E1M1AimSideMemset.program [] E1M1AimSideMemset.startup_agrees (by simp))).transfer
    program [] previous_agrees (by simp)
  refine ⟨⟨n+m,by omega,lead.trans suffix⟩,endpc,?_⟩
  simpa [finished32,base] using zeros

theorem entry32_registers (s : X86Memory.State) (f : Option Flags) (table : Word)
    (h : E1M1AimSideEntry.Initial s table) (v : OriginalGroupHeap.View)
    (heap : E1M1AimSideAllocate.HeapInitial s v) (frame : E1M1AimSidePublish.AllocationFrame s v) :
    (finished32 s).core.regs 0=v.block+24 ∧ (finished32 s).core.regs 1=9 ∧
    (finished32 s).core.regs 2=0 ∧ (finished32 s).core.regs 3=11664 ∧
    (finished32 s).core.regs 4=s.regs 4-32 := by
  obtain ⟨_,pc,base,index,zero,size,sp,ret⟩ := E1M1AimSidePublish.execution s f table h v heap frame
  simp [finished32,completed32,returned,filled32,doneCore,groupStart32,
    E1M1AimSideMemset.wordsCalled,E1M1AimSideMemset.callWords,E1M1AimSideMemset.fillCalled,
    X86Routine.pushWord,put,write,base,size,sp,BitVec.sub_eq_add_neg,BitVec.add_assoc]

theorem entry32_nested_frame (s : X86Memory.State) (f : Option Flags) (table : Word)
    (h : E1M1AimSideEntry.Initial s table) (v : OriginalGroupHeap.View)
    (heap : E1M1AimSideAllocate.HeapInitial s v) (frame : E1M1AimSidePublish.AllocationFrame s v)
    (a : Word) (stack : Apart a (s.regs 4-60))
    (safe : ∀ k<2916, Apart a (v.block+24+BitVec.ofNat 32 (4*k))) :
    load32 (finished32 s).core.memory a=load32 (E1M1AimSideMemset.nested s).core.memory a := by
  obtain ⟨_,pc,base,index,zero,size,sp,ret⟩ := E1M1AimSidePublish.execution s f table h v heap frame
  apply filled32_frame
  · simpa [E1M1AimSideMemset.wordsCalled,E1M1AimSideMemset.callWords,E1M1AimSideMemset.fillCalled,
      X86Routine.pushWord,put,write,sp,BitVec.sub_eq_add_neg,BitVec.add_assoc] using stack
  · simpa [E1M1AimSideMemset.wordsCalled,E1M1AimSideMemset.callWords,E1M1AimSideMemset.fillCalled,
      X86Routine.pushWord,put,write,base] using safe
def OutputSafe (s : X86Memory.State) (v : OriginalGroupHeap.View) (a : Word) : Prop :=
  Apart a (s.regs 4-60) ∧ ∀ k<2916, Apart a (v.block+24+BitVec.ofNat 32 (4*k))

theorem entry32_count_preserved (s : X86Memory.State) (f : Option Flags) (table : Word)
    (h : E1M1AimSideEntry.Initial s table) (v : OriginalGroupHeap.View)
    (heap : E1M1AimSideAllocate.HeapInitial s v) (frame : E1M1AimSidePublish.AllocationFrame s v)
    (before : E1M1AimSideMemset.EntrySafe s 0x2c11c) (output : OutputSafe s v 0x2c11c) :
    load32 (finished32 s).core.memory 0x2c11c=648 := by
  exact (entry32_nested_frame s f table h v heap frame _ output.1 output.2).trans
    (E1M1AimSideMemset.count_preserved s f table h v heap frame before)

theorem entry32_base_preserved (s : X86Memory.State) (f : Option Flags) (table : Word)
    (h : E1M1AimSideEntry.Initial s table) (v : OriginalGroupHeap.View)
    (heap : E1M1AimSideAllocate.HeapInitial s v) (frame : E1M1AimSidePublish.AllocationFrame s v)
    (before : OriginalGroupHeap.Separated 0x2c118
      [s.regs 4-36,s.regs 4-40,s.regs 4-44,s.regs 4-48,s.regs 4-52,s.regs 4-56])
    (output : OutputSafe s v 0x2c118) :
    load32 (finished32 s).core.memory 0x2c118=v.block+24 := by
  exact (entry32_nested_frame s f table h v heap frame _ output.1 output.2).trans
    (E1M1AimSideMemset.base_preserved s f table h v heap before)

theorem entry32_upper_preserved (s : X86Memory.State) (f : Option Flags) (table : Word)
    (h : E1M1AimSideEntry.Initial s table) (v : OriginalGroupHeap.View)
    (heap : E1M1AimSideAllocate.HeapInitial s v) (frame : E1M1AimSidePublish.AllocationFrame s v)
    (a : Word) (ha : a∈E1M1AimSidePublish.upperWords s)
    (before : E1M1AimSideMemset.EntrySafe s a) (output : OutputSafe s v a) :
    load32 (finished32 s).core.memory a=load32 (E1M1AimSideEntry.savedMemory s) a := by
  exact (entry32_nested_frame s f table h v heap frame a output.1 output.2).trans
    (E1M1AimSideMemset.upper_preserved s f table h v heap frame a ha before)
end Doom.Proofs.E1M1AimWordFill
