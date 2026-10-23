import Doom.Proofs.OriginalTextureComparator
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1600000
set_option linter.unusedSimpArgs false
namespace Doom.Proofs.OriginalTextureSearch
open Verification X86 X86Memory X86Control BlockSummary

def continuationBytes : List UInt8 := [0x85,0xc0,0x75,0x08,0x89,0xc8,0x5f,0x5e,0x5a,0x59,0x5b,0xc3,0x8b,0x1d,0xe4,0,3,0,0x41,0x83,0xc6,4,0x39,0xd9,0x7c,0xd2]
def bytesProgram (continuation restore : List UInt8) (prior : X86ByteRoutine.Program) : X86ByteRoutine.Program := fun pc =>
  if 0x34722≤pc ∧ pc<0x3473c then X86ByteRoutine.decodeAt continuation (pc-0x34722)
  else if 0x34741≤pc ∧ pc<0x34747 then X86ByteRoutine.decodeAt restore (pc-0x34741)
  else prior pc
def program := bytesProgram continuationBytes OriginalTextureDash.restoreBytes OriginalTextureComparator.joined

def branch (s : X86Memory.State) : X86Control.State :=
  ⟨s,some (logical32 (s.regs 0)),if s.regs 0=0 then 0x34726 else 0x3472e⟩
def matched (s : X86Memory.State) (f : Option Flags) := OriginalTextureDash.result (put s 0 (s.regs 1)) f
def advancedCore (s : X86Memory.State) :=
  put (put (put s 3 (load32 s.memory 0x300e4)) 1 (s.regs 1+1)) 6 (s.regs 6+4)
def advanced (s : X86Memory.State) : X86Control.State :=
  ⟨advancedCore s,some (compare32 (s.regs 1+1) (load32 s.memory 0x300e4)),
    if (s.regs 1+1).toInt<(load32 s.memory 0x300e4).toInt then 0x3470e else 0x3473c⟩
def exhausted (s : X86Memory.State) (f : Option Flags) := OriginalTextureDash.result (put s 0 0xffffffff) f

theorem branch_execution (s : X86Memory.State) (f : Option Flags) :
    X86ByteRoutine.Prefix program [] 2 ⟨s,f,0x34722⟩ (branch s) := by
  apply X86ByteRoutine.Prefix.step (middle := ⟨s,some (logical32 (s.regs 0)),0x34724⟩) (by simp) (show program 0x34722=some (.base (.control (.testWord 0 0)),2) by decide) (by simp [X86ByteRoutine.execute,X86Routine.execute,X86Control.execute])
  apply X86ByteRoutine.Prefix.step (middle := branch s) (by simp) (show program 0x34724=some (.base (.control (.jumpZero false 8)),2) by decide)
  · by_cases h : s.regs 0=(0#32) <;> simp [branch,X86ByteRoutine.execute,X86Routine.execute,X86Control.execute,logical32,h]
  · exact .nil _

private def popCore (s : X86Memory.State) (r : Reg) :=
  put (put s 4 (s.regs 4+4)) r (load32 s.memory (s.regs 4))
private def pops (s : X86Memory.State) := popCore (popCore (popCore (popCore (popCore s 7) 6) 2) 1) 3

private theorem restore_prefix (s : X86Memory.State) (f : Option Flags) (start : Nat)
    (h : start=0x34728 ∨ start=0x34741) :
    X86ByteRoutine.Prefix program [] 6 ⟨s,f,start⟩ (OriginalTextureDash.result s f) := by
  have finish : ⟨put (pops s) 4 ((pops s).regs 4+4),f,
      (load32 (pops s).memory ((pops s).regs 4)).toNat⟩=OriginalTextureDash.result s f := by
    simp [pops,popCore,OriginalTextureDash.result,OriginalTextureDash.restored,put,write,BitVec.add_assoc]
    funext r
    by_cases h : r=4 <;> simp [write,h]
  rw [← finish]
  rcases h with rfl | rfl
  · apply X86ByteRoutine.Prefix.step (middle := ⟨popCore (s) 7,f,0x34729⟩) (by simp) (show program 0x34728=some (.base (.pop 7),1) by decide) (by rfl)
    apply X86ByteRoutine.Prefix.step (middle := ⟨popCore (popCore (s) 7) 6,f,0x3472a⟩) (by simp) (show program 0x34729=some (.base (.pop 6),1) by decide) (by rfl)
    apply X86ByteRoutine.Prefix.step (middle := ⟨popCore (popCore (popCore (s) 7) 6) 2,f,0x3472b⟩) (by simp) (show program 0x3472a=some (.base (.pop 2),1) by decide) (by rfl)
    apply X86ByteRoutine.Prefix.step (middle := ⟨popCore (popCore (popCore (popCore (s) 7) 6) 2) 1,f,0x3472c⟩) (by simp) (show program 0x3472b=some (.base (.pop 1),1) by decide) (by rfl)
    apply X86ByteRoutine.Prefix.step (middle := ⟨popCore (popCore (popCore (popCore (popCore (s) 7) 6) 2) 1) 3,f,0x3472d⟩) (by simp) (show program 0x3472c=some (.base (.pop 3),1) by decide) (by rfl)
    apply X86ByteRoutine.Prefix.step (by simp) (show program 0x3472d=some (.base .ret,1) by decide) (by rfl)
    exact .nil _
  · apply X86ByteRoutine.Prefix.step (middle := ⟨popCore (s) 7,f,0x34742⟩) (by simp) (show program 0x34741=some (.base (.pop 7),1) by decide) (by rfl)
    apply X86ByteRoutine.Prefix.step (middle := ⟨popCore (popCore (s) 7) 6,f,0x34743⟩) (by simp) (show program 0x34742=some (.base (.pop 6),1) by decide) (by rfl)
    apply X86ByteRoutine.Prefix.step (middle := ⟨popCore (popCore (popCore (s) 7) 6) 2,f,0x34744⟩) (by simp) (show program 0x34743=some (.base (.pop 2),1) by decide) (by rfl)
    apply X86ByteRoutine.Prefix.step (middle := ⟨popCore (popCore (popCore (popCore (s) 7) 6) 2) 1,f,0x34745⟩) (by simp) (show program 0x34744=some (.base (.pop 1),1) by decide) (by rfl)
    apply X86ByteRoutine.Prefix.step (middle := ⟨popCore (popCore (popCore (popCore (popCore (s) 7) 6) 2) 1) 3,f,0x34746⟩) (by simp) (show program 0x34745=some (.base (.pop 3),1) by decide) (by rfl)
    apply X86ByteRoutine.Prefix.step (by simp) (show program 0x34746=some (.base .ret,1) by decide) (by rfl)
    exact .nil _


theorem matched_execution (s : X86Memory.State) (f : Option Flags) :
    X86ByteRoutine.Prefix program [] 7 ⟨s,f,0x34726⟩ (matched s f) := by
  apply X86ByteRoutine.Prefix.step (middle := ⟨put s 0 (s.regs 1),f,0x34728⟩) (by simp) (show program 0x34726=some (.base (.control (.block (.legacy (.mov 0 1)))),2) by decide) (by rfl)
  exact restore_prefix _ _ _ (Or.inl rfl)

theorem exhausted_execution (s : X86Memory.State) (f : Option Flags) :
    X86ByteRoutine.Prefix program [] 7 ⟨s,f,0x3473c⟩ (exhausted s f) := by
  apply X86ByteRoutine.Prefix.step (middle := ⟨put s 0 0xffffffff,f,0x34741⟩) (by simp) (show program 0x3473c=some (.base (.immediate 0 0xffffffff),5) by decide) (by rfl)
  exact restore_prefix _ _ _ (Or.inr rfl)

theorem advance_execution (s : X86Memory.State) (f : Option Flags) :
    X86ByteRoutine.Prefix program [] 5 ⟨s,f,0x3472e⟩ (advanced s) := by
  apply X86ByteRoutine.Prefix.step (middle := ⟨put s 3 (load32 s.memory 0x300e4),f,0x34734⟩) (by simp) (show program 0x3472e=some (.base (.control (.block (.load 3 ⟨none,none,0,0x300e4⟩))),6) by decide) (by rfl)
  apply X86ByteRoutine.Prefix.step (middle := ⟨put (put s 3 (load32 s.memory 0x300e4)) 1 (s.regs 1+1),none,0x34735⟩) (by simp) (show program 0x34734=some (.base (.addImmediate 1 1),1) by decide) (by rfl)
  apply X86ByteRoutine.Prefix.step (middle := ⟨advancedCore s,none,0x34738⟩) (by simp) (show program 0x34735=some (.base (.addImmediate 6 4),3) by decide) (by rfl)
  apply X86ByteRoutine.Prefix.step (middle := ⟨advancedCore s,some (compare32 (s.regs 1+1) (load32 s.memory 0x300e4)),0x3473a⟩) (by simp) (show program 0x34738=some (.base (.compareRegisters 1 3),2) by decide) (by rfl)
  apply X86ByteRoutine.Prefix.step (middle := advanced s) (by simp) (show program 0x3473a=some (.base (.jumpSigned 3 (-46)),2) by decide)
  · by_cases h : (s.regs 1+1).toInt<(load32 s.memory (0x300e4#32)).toInt
    all_goals simp_all [advanced,X86ByteRoutine.execute,X86Routine.execute,advancedCore,put,write,PlayerHeight.cmp_ge_prop]
  · exact .nil _

theorem prior_agreement (pc : Nat) (h : OriginalTextureComparator.joined pc≠none) :
    program pc=OriginalTextureComparator.joined pc := by
  have outside : ¬(0x34722≤pc ∧ pc<0x3473c) ∧ ¬(0x34741≤pc ∧ pc<0x34747) := by
    by_cases inside : (0x34722≤pc ∧ pc<0x3473c) ∨ (0x34741≤pc ∧ pc<0x34747)
    · have b1 : ¬(0x4198c≤pc ∧ pc<0x41999) := by omega
      have b2 : ¬(0x419b5≤pc ∧ pc<0x419ce) := by omega
      have b3 : ¬(0x41999≤pc ∧ pc<0x419b5) := by omega
      have b4 : ¬(0x34700≤pc ∧ pc<0x34722) := by omega
      have b5 : ¬(0x3473c≤pc ∧ pc<0x34741) := by omega
      simp [OriginalTextureComparator.joined,OriginalTextureComparator.combine,
        OriginalTextureIteration.program,OriginalTextureIteration.bytesProgram,
        OriginalTextureFold.bytesProgram,OriginalTextureTable.program,
        OriginalTextureTable.bytesProgram,X86ByteRoutine.liftProgram,b1,b2,b3,b4,b5] at h
    · omega
  simp [program,bytesProgram,outside.1,outside.2]

def texture (s : X86Memory.State) := load32 s.memory (s.regs 6+load32 s.memory 0x300e0)
def comparison (s : X86Memory.State) : X86Control.State :=
  ⟨X86Routine.pushWord (put (put (put s 0 (texture s)) 3 8) 2 (s.regs 7)) 0x34722,none,0x4198c⟩
def compared (s : X86Memory.State) := OriginalTextureComparator.complete (comparison s).core

theorem comparison_registers (s : X86Memory.State) :
    (compared s).pc=0x34722 ∧ (compared s).core.regs 1=s.regs 1 ∧
      (compared s).core.regs 4=s.regs 4 ∧ (compared s).core.regs 6=s.regs 6 := by
  have safe : Apart ((comparison s).core.regs 4) ((comparison s).core.regs 4-4) := by
    have h := HalfMemory.translate (s.regs 4) (-4) (-8) 4 4 (show Apart (-4) (-8) from by unfold Apart; decide)
    change Apart (s.regs 4+(-4)) (s.regs 4+(-8)) at h
    simpa [comparison,X86Routine.pushWord,put,write,BitVec.sub_eq_add_neg,BitVec.add_assoc] using h
  have hr := OriginalTextureComparator.complete_restoration (comparison s).core safe
  have hf := (OriginalTextureComparator.complete_frame (comparison s).core).2 6 (by decide) (by decide) (by decide) (by decide) (by decide)
  simpa [compared,comparison,X86Routine.pushWord,put,write,load_store,BitVec.sub_eq_add_neg,BitVec.add_assoc] using And.intro hr.2.2 (And.intro hr.1 (And.intro hr.2.1 hf))

theorem comparison_execution (s : X86Memory.State) (f : Option Flags) :
    ∃ k≤188, X86ByteRoutine.Prefix program [] k ⟨s,f,0x3470e⟩ (compared s) := by
  have start : X86ByteRoutine.Prefix program [] 5 ⟨s,f,0x3470e⟩ {(comparison s) with flags:=f} := by
    apply X86ByteRoutine.Prefix.step (middle := ⟨put s 0 (load32 s.memory 0x300e0),f,0x34713⟩) (by simp) (show program 0x3470e=some (.base (.control (.block (.load 0 ⟨none,none,0,0x300e0⟩))),5) by decide) (by rfl)
    apply X86ByteRoutine.Prefix.step (middle := ⟨put (put s 0 (load32 s.memory 0x300e0)) 3 8,f,0x34718⟩) (by simp) (show program 0x34713=some (.base (.immediate 3 8),5) by decide) (by rfl)
    apply X86ByteRoutine.Prefix.step (middle := ⟨put (put (put s 0 (load32 s.memory 0x300e0)) 3 8) 2 (s.regs 7),f,0x3471a⟩) (by simp) (show program 0x34718=some (.base (.control (.block (.legacy (.mov 2 7)))),2) by decide) (by rfl)
    apply X86ByteRoutine.Prefix.step (middle := ⟨put (put (put s 0 (texture s)) 3 8) 2 (s.regs 7),f,0x3471d⟩) (by simp) (show program 0x3471a=some (.base (.control (.block (.load 0 ⟨some 6,some 0,0,0⟩))),3) by decide)
    · simp [X86ByteRoutine.execute,X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,X86Block.Address.eval,blockPreservesFlags,texture,put,write]
      funext r
      by_cases h : r=0 <;> simp [write,h]
    · apply X86ByteRoutine.Prefix.step (middle := {(comparison s) with flags:=f}) (by simp) (show program 0x3471d=some (.base (.call 53866),5) by decide) (by simp [comparison,X86ByteRoutine.execute,X86Routine.execute])
      exact .nil _
  obtain ⟨k,hk,hp⟩ := OriginalTextureComparator.complete_execution (comparison s).core f
  have agreement (pc : Nat) (h : OriginalTextureIteration.program pc≠none) : program pc=OriginalTextureIteration.program pc := by
    have joined := OriginalTextureComparator.joined_comparator pc h
    exact (prior_agreement pc (by rw [joined]; exact h)).trans joined
  exact ⟨5+k,by simp [comparison,X86Routine.pushWord,put,write] at hk; omega,
    start.trans (hp.transfer program [] agreement (by simp))⟩

def continues (s : X86Memory.State) : Prop :=
  (compared s).core.regs 0≠0 ∧ (advanced (compared s).core).pc=0x3470e
instance (s : X86Memory.State) : Decidable (continues s) := inferInstanceAs (Decidable (_ ∧ _))
def round (s : X86Memory.State) : X86Control.State :=
  let t := compared s
  if t.core.regs 0=0 then matched t.core (branch t.core).flags
  else let u := advanced t.core
    if u.pc=0x3470e then u else exhausted u.core u.flags

theorem round_execution (s : X86Memory.State) (f : Option Flags) :
    ∃ k≤202, X86ByteRoutine.Prefix program [] k ⟨s,f,0x3470e⟩ (round s) := by
  obtain ⟨k,hk,hp⟩ := comparison_execution s f
  have seam : ⟨(compared s).core,(compared s).flags,0x34722⟩=compared s := by
    have h := (comparison_registers s).1
    cases e : compared s
    simp_all
  have bp := branch_execution (compared s).core (compared s).flags
  rw [seam] at bp
  have bp := hp.trans bp
  by_cases h : (compared s).core.regs 0=(0#32)
  · have p := matched_execution (compared s).core (branch (compared s).core).flags
    have seam : ⟨(compared s).core,(branch (compared s).core).flags,0x34726⟩=branch (compared s).core := by simp [branch,h]
    rw [seam] at p
    exact ⟨k+2+7,by omega,by simpa [round,h] using bp.trans p⟩
  · have p := advance_execution (compared s).core (branch (compared s).core).flags
    have seam : ⟨(compared s).core,(branch (compared s).core).flags,0x3472e⟩=branch (compared s).core := by simp [branch,h]
    rw [seam] at p
    by_cases go : (advanced (compared s).core).pc=0x3470e
    · exact ⟨k+2+5,by omega,by simpa [round,h,go] using bp.trans p⟩
    · have tail := exhausted_execution (advanced (compared s).core).core (advanced (compared s).core).flags
      have seam : ⟨(advanced (compared s).core).core,(advanced (compared s).core).flags,0x3473c⟩=advanced (compared s).core := by
        simp only [advanced] at go ⊢
        split at go <;> simp_all
      rw [seam] at tail
      exact ⟨k+2+5+7,by omega,by simpa [round,h,go] using (bp.trans p).trans tail⟩

theorem continuing_round (s : X86Memory.State) (go : continues s) :
    round s=advanced (compared s).core ∧ (round s).pc=0x3470e ∧
      (round s).core.regs 1=s.regs 1+1 ∧ (round s).core.regs 4=s.regs 4 ∧
      (round s).core.regs 6=s.regs 6+4 := by
  have same : round s=advanced (compared s).core := by simp only [round,go.1,go.2,↓reduceIte]
  refine ⟨same,by rw [same]; exact go.2,?_,?_,?_⟩
  all_goals simp [same,advanced,advancedCore,put,write,(comparison_registers s).2.1,
    (comparison_registers s).2.2.1,(comparison_registers s).2.2.2]

/-- The signed JL cannot continue at INT_MAX, even if the count cell aliases
stack writes and changes between calls. No stable-table or success assumption. -/
theorem search_descent (n : Nat) (s : X86Memory.State)
    (measure : (s.regs 1).toNat+(n+1)=2147483647) (go : continues s) :
    0<n ∧ ((round s).core.regs 1).toNat+n=2147483647 := by
  have inc : (s.regs 1+1).toNat=(s.regs 1).toNat+1 := by
    simp [BitVec.toNat_add]
    omega
  have nextSigned : (s.regs 1+1).toInt=((s.regs 1).toNat+1 : Int) := by
    rw [BitVec.toInt_eq_toNat_cond]
    rw [inc]
    rw [if_pos (by omega)]
    simp
  have bound := (load32 (compared s).core.memory (0x300e4#32)).toInt_lt
  have lt : (s.regs 1+1).toInt<(load32 (compared s).core.memory (0x300e4#32)).toInt := by
    have h := go.2
    simp only [advanced,(comparison_registers s).2.1] at h
    split at h
    · assumption
    · contradiction
  constructor
  · rw [nextSigned] at lt
    change (load32 (compared s).core.memory (0x300e4#32)).toInt<2147483648 at bound
    omega
  · rw [(continuing_round s go).2.2.1,inc]
    omega

def search : Nat → X86Memory.State → Option Flags → X86Control.State
  | 0,s,f => ⟨s,f,0x3470e⟩
  | n+1,s,_ => if continues s then search n (round s).core (round s).flags else round s

theorem search_execution (n : Nat) (s : X86Memory.State) (f : Option Flags)
    (positive : 0<n) (measure : (s.regs 1).toNat+n=2147483647) :
    ∃ k≤202*n, X86ByteRoutine.Prefix program [] k ⟨s,f,0x3470e⟩ (search n s f) := by
  induction n generalizing s f with
  | zero => omega
  | succ n ih =>
    obtain ⟨k,hk,hp⟩ := round_execution s f
    by_cases go : continues s
    · have desc := search_descent n s measure go
      obtain ⟨j,hj,pj⟩ := ih (round s).core (round s).flags desc.1 desc.2
      have seam : ⟨(round s).core,(round s).flags,0x3470e⟩=round s := by
        have h := (continuing_round s go).2.1
        cases e : round s
        simp_all
      rw [seam] at pj
      exact ⟨k+j,by omega,by simpa only [search,go,↓reduceIte] using hp.trans pj⟩
    · exact ⟨k,by omega,by simpa only [search,go,↓reduceIte] using hp⟩

theorem full_search_execution (s : X86Memory.State) (f : Option Flags) (zero : s.regs 1=0) :
    ∃ k≤202*2147483647, X86ByteRoutine.Prefix program [] k ⟨s,f,0x3470e⟩ (search 2147483647 s f) := by
  exact search_execution _ s f (by decide) (by simp [zero])

def comparisonMemory (s : X86Memory.State) := store32 (store32 s.memory (s.regs 4-4) 0x34722) (s.regs 4-8) (s.regs 1)
theorem comparison_memory (s : X86Memory.State) : (compared s).core.memory=comparisonMemory s := by
  simpa [compared,comparison,OriginalTextureIteration.prepared,X86Routine.pushWord,comparisonMemory,put,write,BitVec.sub_eq_add_neg,BitVec.add_assoc] using (OriginalTextureComparator.complete_frame (comparison s).core).1

theorem comparison_result (s : X86Memory.State) :
    (compared s).core.regs 0=OriginalTextureComparator.compareBytes 8 (comparisonMemory s) (texture s) (s.regs 7) := by
  simpa [compared,comparison,OriginalTextureIteration.prepared,X86Routine.pushWord,comparisonMemory,put,write,BitVec.sub_eq_add_neg,BitVec.add_assoc] using OriginalTextureComparator.complete_result (comparison s).core

theorem round_memory (s : X86Memory.State) : (round s).core.memory=comparisonMemory s := by
  simp only [round]
  split
  · exact comparison_memory s
  · split <;> exact comparison_memory s

theorem round_frame (s : X86Memory.State) (a : Word)
    (callSafe : Apart a (s.regs 4-4)) (pushSafe : Apart a (s.regs 4-8)) :
    load32 (round s).core.memory a=load32 s.memory a := by
  rw [round_memory]
  exact (load_store_apart _ _ _ _ pushSafe).trans (load_store_apart _ _ _ _ callSafe)

theorem search_frame (n : Nat) (s : X86Memory.State) (f : Option Flags) (a : Word)
    (callSafe : Apart a (s.regs 4-4)) (pushSafe : Apart a (s.regs 4-8)) :
    load32 (search n s f).core.memory a=load32 s.memory a := by
  induction n generalizing s f with
  | zero => rfl
  | succ n ih =>
    simp only [search]
    split
    · rename_i go
      have sp := (continuing_round s go).2.2.2.1
      rw [ih _ _ (by rwa [sp]) (by rwa [sp])]
      exact round_frame s a callSafe pushSafe
    · exact round_frame s a callSafe pushSafe

theorem slot_separation (sp off : Word) (member : off∈[(0#32),4,8,12,16,20,24,28,32]) :
    Apart (sp+off) (sp-4) ∧ Apart (sp+off) (sp-8) := by
  have a : Apart off (-4) ∧ Apart off (-8) := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals constructor <;> unfold Apart <;> decide
  have a1 := HalfMemory.translate sp off (-4) 4 4 a.1
  have a2 := HalfMemory.translate sp off (-8) 4 4 a.2
  change Apart (sp+off) (sp+(-4)) at a1
  change Apart (sp+off) (sp+(-8)) at a2
  simpa [BitVec.sub_eq_add_neg] using And.intro a1 a2

theorem terminal_round (s : X86Memory.State) (stop : ¬continues s) :
    (round s).pc=(load32 s.memory (s.regs 4+20)).toNat ∧
    (round s).core.regs 4=s.regs 4+24 ∧
    ((round s).core.regs 0=s.regs 1 ∨ (round s).core.regs 0=0xffffffff) := by
  have mem : load32 (compared s).core.memory (s.regs 4+20)=load32 s.memory (s.regs 4+20) := by
    rw [comparison_memory]
    have sep := slot_separation (s.regs 4) 20 (by simp)
    exact (load_store_apart _ _ _ _ sep.2).trans (load_store_apart _ _ _ _ sep.1)
  have regs := comparison_registers s
  by_cases zero : (compared s).core.regs 0=(0#32)
  · simp only [round,zero,↓reduceIte]
    simp_all [matched,OriginalTextureDash.result,OriginalTextureDash.restored,put,write]
  · have no : (advanced (compared s).core).pc≠0x3470e := by intro h; exact stop ⟨zero,h⟩
    simp only [round,zero,no,↓reduceIte]
    simp_all [exhausted,OriginalTextureDash.result,OriginalTextureDash.restored,advanced,advancedCore,put,write]

theorem search_return (n : Nat) (s : X86Memory.State) (f : Option Flags)
    (positive : 0<n) (measure : (s.regs 1).toNat+n=2147483647) :
    (search n s f).pc=(load32 s.memory (s.regs 4+20)).toNat ∧
    (search n s f).core.regs 4=s.regs 4+24 ∧
    ((search n s f).core.regs 0=0xffffffff ∨ ((search n s f).core.regs 0).toNat<2147483647) := by
  induction n generalizing s f with
  | zero => omega
  | succ n ih =>
    by_cases go : continues s
    · have desc := search_descent n s measure go
      have h := ih (round s).core (round s).flags desc.1 desc.2
      have sp := (continuing_round s go).2.2.2.1
      have sep := slot_separation (s.regs 4) 20 (by simp)
      have mem := round_frame s (s.regs 4+20) sep.1 sep.2
      simpa only [search,go,↓reduceIte,sp,mem] using h
    · have h := terminal_round s go
      simp only [search,go,↓reduceIte]
      refine ⟨h.1,h.2.1,?_⟩
      rcases h.2.2 with found|missing
      · right; rw [found]; omega
      · exact Or.inl missing

theorem comparison_ebp (s : X86Memory.State) : (compared s).core.regs 5=s.regs 5 := by
  simpa [compared,comparison,X86Routine.pushWord,put,write] using
    (OriginalTextureComparator.complete_frame (comparison s).core).2 5 (by decide) (by decide) (by decide) (by decide) (by decide)

private theorem saved_frame (s : X86Memory.State) (off : Word) (h : off∈[(0#32),4,8,12,16]) :
    load32 (compared s).core.memory (s.regs 4+off)=load32 s.memory (s.regs 4+off) := by
  have member : off∈[(0#32),4,8,12,16,20,24,28,32] := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at h ⊢
    rcases h with rfl|rfl|rfl|rfl|rfl <;> simp
  have sep := slot_separation (s.regs 4) off member
  rw [comparison_memory]
  exact (load_store_apart _ _ _ _ sep.2).trans (load_store_apart _ _ _ _ sep.1)

theorem round_saved (s : X86Memory.State) (r : Reg) (h0 : r≠0) (h4 : r≠4) :
    (if continues s then (OriginalTextureDash.restored (round s).core).regs r else (round s).core.regs r)=
      (OriginalTextureDash.restored s).regs r := by
  have cases : r=1 ∨ r=2 ∨ r=3 ∨ r=5 ∨ r=6 ∨ r=7 := by
    have all : ∀ r : Reg, r=0 ∨ r=1 ∨ r=2 ∨ r=3 ∨ r=4 ∨ r=5 ∨ r=6 ∨ r=7 := by decide
    simpa only [h0,h4,false_or,or_false] using all r
  have m0 := saved_frame s 0 (by simp)
  have m4 := saved_frame s 4 (by simp)
  have m8 := saved_frame s 8 (by simp)
  have m12 := saved_frame s 12 (by simp)
  have m16 := saved_frame s 16 (by simp)
  simp at m0 m4 m8 m12 m16
  have sp := (comparison_registers s).2.2.1
  have bp := comparison_ebp s
  by_cases go : continues s
  · rw [if_pos go,(continuing_round s go).1]
    rcases cases with rfl|rfl|rfl|rfl|rfl|rfl
    all_goals simp [OriginalTextureDash.restored,advanced,advancedCore,put,write,sp,bp,m0,m4,m8,m12,m16]
  · rw [if_neg go]
    by_cases z : (compared s).core.regs 0=(0#32)
    · simp only [round,z,↓reduceIte]
      rcases cases with rfl|rfl|rfl|rfl|rfl|rfl
      all_goals simp [matched,OriginalTextureDash.result,OriginalTextureDash.restored,put,write,sp,bp,m0,m4,m8,m12,m16]
    · have no : (advanced (compared s).core).pc≠0x3470e := by intro h; exact go ⟨z,h⟩
      simp only [round,z,no,↓reduceIte]
      rcases cases with rfl|rfl|rfl|rfl|rfl|rfl
      all_goals simp [z,exhausted,OriginalTextureDash.result,OriginalTextureDash.restored,advanced,advancedCore,put,write,sp,bp,m0,m4,m8,m12,m16]

theorem search_saved (n : Nat) (s : X86Memory.State) (f : Option Flags)
    (positive : 0<n) (measure : (s.regs 1).toNat+n=2147483647)
    (r : Reg) (h0 : r≠0) (h4 : r≠4) :
    (search n s f).core.regs r=(OriginalTextureDash.restored s).regs r := by
  induction n generalizing s f with
  | zero => omega
  | succ n ih =>
    have saved := round_saved s r h0 h4
    by_cases go : continues s
    · have desc := search_descent n s measure go
      simpa only [search,go,↓reduceIte] using
        (ih (round s).core (round s).flags desc.1 desc.2).trans (by simpa only [go,↓reduceIte] using saved)
    · simpa only [search,go,↓reduceIte] using saved
end Doom.Proofs.OriginalTextureSearch
