import Doom.Proofs.E1M1AimWordFill
/-! Opt-in completion for every four-byte-aligned destination. The head count is
derived from initial low address bits, not supplied as a reached alignment.
The actual post-head PUSH saves the remaining count. Static separation justifies
commuting that store for the memory summary; instruction ordering is unchanged.
The predecessor's symbolic groups and both terminal paths are reused unchanged.
No claim about the later cache/read/gate or production initialized state. -/
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
namespace Doom.Proofs.E1M1AimWordAligned
open Verification X86 X86Memory X86Control BlockSummary E1M1AimWordFill
open X86WordFillRoutine (Knowledge)

def headCore (s : X86Memory.State) (h : Nat) : X86Memory.State :=
  put (put {s with memory:=zeros s.memory (s.regs 0) h} 1
    (s.regs 1-BitVec.ofNat 32 h)) 0 (s.regs 0+BitVec.ofNat 32 (4*h))

theorem low_add (a : Word) (n : Nat) :
    (a+BitVec.ofNat 32 n).extractLsb' 0 8 = a.extractLsb' 0 8+BitVec.ofNat 8 n := by
  rw [BitVec.extractLsb'_add (by decide)]
  apply congrArg (fun b => a.extractLsb' 0 8+b)
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.extractLsb',Nat.mod_mod_of_dvd,show 256 ∣ 4294967296 by decide]

theorem alignment_head (a : Word) (aligned : a.extractLsb' 0 8 &&& 3=0) :
    ∃ h<8, (a+BitVec.ofNat 32 (4*h)).extractLsb' 0 8 &&& 31=0 ∧
      ∀ j<h, (a+BitVec.ofNat 32 (4*j)).extractLsb' 0 8 &&& 31≠0 := by
  have finite : ∀ b : BitVec 8, b &&& 3=0 →
      ∃ h : Fin 8, (b+BitVec.ofNat 8 (4*h.val)) &&& 31=0 ∧
        ∀ j : Fin 8, j.val<h.val → (b+BitVec.ofNat 8 (4*j.val)) &&& 31≠0 := by decide +kernel
  obtain ⟨h,done,prior⟩ := finite (a.extractLsb' 0 8) aligned
  refine ⟨h.val,h.isLt,?_,?_⟩
  · simpa only [low_add] using done
  · intro j hj
    simpa only [low_add] using prior ⟨j,by omega⟩ hj

theorem headCore_zero (s : X86Memory.State) : headCore s 0=s := by
  cases s with | mk regs memory =>
    simp [headCore,zeros,put,write]
    funext r
    by_cases h : r=0 <;> by_cases h1 : r=1 <;> simp [write,h,h1]

theorem headCore_next (s : X86Memory.State) (h : Nat) :
    headCore (headCore s h) 1=headCore s (h+1) := by
  simp [headCore,zeros,put,write,BitVec.ofNat_add,Nat.mul_add,
    BitVec.sub_eq_add_neg,BitVec.neg_add,BitVec.add_assoc]
  funext r
  by_cases h0 : r=0 <;> by_cases h1 : r=1 <;> simp [write,h0,h1]

theorem head_step (s : X86Memory.State) (f : Knowledge)
    (zero : s.regs 2=0) (misaligned : readByte s.regs 0 &&& 31≠0)
    (positive : s.regs 1-1≠0) :
    ∃ g, X86WordFillRoutine.Prefix program [] 6 ⟨s,f,0x4191b⟩
      ⟨headCore s 1,g,0x4191b⟩ := by
  simp only [BitVec.ofNat_eq_ofNat] at zero misaligned positive
  let g : Knowledge := .legacy (some {compare32 (s.regs 1) 1 with carry:=some false})
  have path : X86WordFillRoutine.Prefix listed [] 6 ⟨s,f,0x4191b⟩
      ⟨headCore s 1,g,0x4191b⟩ := by
    cases f <;>
      (refine .step (by simp) rfl rfl ?_
       refine .step (middle:=⟨s,.legacy (some (logical8 (readByte s.regs 0 &&& 31))),0x4191f⟩)
         (by simp) rfl ?_ ?_)
    all_goals first
      | (simp [X86WordFillRoutine.execute,X86WordFillRoutine.embed,X86WordFillRoutine.preserves,
          X86FillRoutine.execute,X86StartupRoutine.execute,X86ByteRoutine.execute,
          X86Routine.execute,X86Control.execute,logical8,misaligned])
      | skip
    all_goals
      refine .step (by simp) rfl rfl ?_
      refine .step (by simp) rfl rfl ?_
      refine .step (by simp) rfl rfl ?_
      refine .step (middle:=⟨headCore s 1,g,0x4191b⟩) (by simp) rfl ?_ (.nil _)
      simp [headCore,g,X86WordFillRoutine.execute,X86WordFillRoutine.embed,
        Knowledge.carry,X86FillRoutine.execute,X86StartupRoutine.execute,X86ByteRoutine.execute,
        X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,
        X86Block.Address.eval,blockPreservesFlags,put,write,zeros,BitVec.add_assoc,
        logical8,compare32,zero,positive]
      funext r
      by_cases h0 : r=0 <;> by_cases h1 : r=1 <;> simp [write,h0,h1]
  exact ⟨g,path.transfer _ [] decoded (by simp)⟩

theorem heads_execution (s : X86Memory.State) (f : Knowledge) (h : Nat)
    (count : s.regs 1=2916) (zero : s.regs 2=0) (small : h<8)
    (prior : ∀ j<h, (s.regs 0+BitVec.ofNat 32 (4*j)).extractLsb' 0 8 &&& 31≠0) :
    ∃ g, X86WordFillRoutine.Prefix program [] (6*h) ⟨s,f,0x4191b⟩
      ⟨headCore s h,g,0x4191b⟩ := by
  induction h with
  | zero => exact ⟨f,by simpa only [headCore_zero] using X86WordFillRoutine.Prefix.nil (program:=program) (exits:=[]) ⟨s,f,0x4191b⟩⟩
  | succ h ih =>
    obtain ⟨g,lead⟩ := ih (by omega) (fun j hj=>prior j (by omega))
    have hz : (headCore s h).regs 2=0 := by simp [headCore,put,write,zero]
    have ha : readByte (headCore s h).regs 0 &&& 31≠0 := by
      simpa [headCore,put,write,readByte,byteReg] using prior h (by omega)
    have hn : (headCore s h).regs 1-1≠0 := by
      simp [headCore,put,write,count]
      have cases : h=0 ∨ h=1 ∨ h=2 ∨ h=3 ∨ h=4 ∨ h=5 ∨ h=6 := by omega
      rcases cases with hh|hh|hh|hh|hh|hh|hh <;> subst h <;> decide
    obtain ⟨g',tail⟩ := head_step (headCore s h) g hz ha hn
    refine ⟨g',?_⟩
    have joined := lead.trans tail
    simpa only [headCore_next,Nat.mul_add,Nat.mul_one] using joined

theorem head_execution (s : X86Memory.State) (f : Knowledge)
    (count : s.regs 1=2916) (zero : s.regs 2=0)
    (aligned : readByte s.regs 0 &&& 3=0) :
    ∃ h<8, ∃ n≤46, ∃ t : X86WordFillRoutine.State,
      X86WordFillRoutine.Prefix program [] n ⟨s,f,0x41917⟩ t ∧
      t.pc=0x41927 ∧ t.core=headCore s h ∧
      readByte t.core.regs 0 &&& 31=0 := by
  obtain ⟨h,small,done,prior⟩ := alignment_head (s.regs 0) aligned
  have lead : X86WordFillRoutine.Prefix listed [] 2 ⟨s,f,0x41917⟩
      ⟨s,.legacy (some (logical32 2916)),0x4191b⟩ := by
    have regs : write s.regs 1 2916=s.regs := by
      funext r; by_cases hr : r=1 <;> simp [write,hr,count]
    simp only [BitVec.ofNat_eq_ofNat] at count regs
    refine .step (middle:=⟨s,.legacy (some (logical32 2916)),0x41919⟩) (by simp) rfl ?_ ?_
    · cases f <;> simp [X86WordFillRoutine.execute,X86WordFillRoutine.embed,
        X86WordFillRoutine.preserves,X86FillRoutine.execute,put,count,regs]
    exact .step (by simp) rfl rfl (.nil _)
  obtain ⟨g,body⟩ := heads_execution s (.legacy (some (logical32 2916))) h count zero small prior
  have aligned32 : readByte (headCore s h).regs 0 &&& 31=0 := by
    simpa [headCore,put,write,readByte,byteReg] using done
  let t : X86WordFillRoutine.State := ⟨headCore s h,.legacy (some (logical8 0)),0x41927⟩
  simp only [BitVec.ofNat_eq_ofNat] at aligned32
  have tail : X86WordFillRoutine.Prefix listed [] 2 ⟨headCore s h,g,0x4191b⟩ t := by
    cases g <;>
      (refine .step (by simp) rfl rfl ?_
       refine .step (middle:=t) (by simp) rfl ?_ (.nil _)
       simp [t,X86WordFillRoutine.execute,X86WordFillRoutine.embed,X86WordFillRoutine.preserves,
         X86FillRoutine.execute,X86StartupRoutine.execute,X86ByteRoutine.execute,
         X86Routine.execute,X86Control.execute,aligned32,logical8])
  exact ⟨h,small,2+6*h+2,by omega,t,
    ((lead.transfer _ [] decoded (by simp)).trans body).trans
      (tail.transfer _ [] decoded (by simp)),rfl,rfl,aligned32⟩
def groupStart (s : X86Memory.State) (w : Nat) : X86WordFillRoutine.State :=
  ⟨put (X86Routine.pushWord s (BitVec.ofNat 32 w)) 1 (BitVec.ofNat 32 (w/4)-1),
    .legacy (some {compare32 (BitVec.ofNat 32 (w/4)) 1 with carry:=none}),0x41930⟩

theorem group_setup (s : X86Memory.State) (f : Knowledge) (w : Nat)
    (low : 2909≤w) (high : w≤2916) (count : s.regs 1=BitVec.ofNat 32 w) :
    X86WordFillRoutine.Prefix program [] 5 ⟨s,f,0x41927⟩ (groupStart s w) := by
  have shift : (BitVec.ofNat 32 w) >>> 2=BitVec.ofNat 32 (w/4) := by
    have cases : w=2909 ∨ w=2910 ∨ w=2911 ∨ w=2912 ∨ w=2913 ∨ w=2914 ∨ w=2915 ∨ w=2916 := by omega
    rcases cases with h|h|h|h|h|h|h|h <;> subst w <;> decide
  have nz : BitVec.ofNat 32 (w/4)≠0 := word_ne_zero _ (by omega) (by omega)
  have nz1 : BitVec.ofNat 32 (w/4)-1≠0 := by
    have cases : w/4=727 ∨ w/4=728 ∨ w/4=729 := by omega
    rcases cases with h|h|h <;> rw [h] <;> decide
  simp only [BitVec.ofNat_eq_ofNat] at nz nz1
  have path : X86WordFillRoutine.Prefix listed [] 5 ⟨s,f,0x41927⟩ (groupStart s w) := by
    cases f <;>
      (refine .step (by simp) rfl rfl ?_
       refine .step (by simp) rfl rfl ?_
       refine .step (middle:=⟨put (X86Routine.pushWord s (BitVec.ofNat 32 w)) 1 (BitVec.ofNat 32 (w/4)),.zeroOnly false,0x4192d⟩)
         (by simp) rfl ?_ ?_)
    all_goals first
      | (simp [X86WordFillRoutine.execute,X86WordFillRoutine.embed,X86WordFillRoutine.preserves,
          X86FillRoutine.execute,X86StartupRoutine.execute,X86ByteRoutine.execute,
          X86Routine.execute,X86Routine.pushWord,put,write,count,shift,nz])
      | skip
    all_goals
      refine .step (by simp) rfl rfl ?_
      refine .step (middle:=groupStart s w) (by simp) rfl ?_ (.nil _)
      simp [groupStart,X86WordFillRoutine.execute,X86WordFillRoutine.embed,Knowledge.carry,
        X86FillRoutine.execute,X86StartupRoutine.execute,X86ByteRoutine.execute,
        X86Routine.execute,X86Control.execute,X86Routine.pushWord,put,write,count,shift,nz1,compare32]
  exact path.transfer _ [] decoded (by simp)

theorem grouped_execution (s : X86Memory.State) (f : Knowledge) (w : Nat)
    (low : 2909≤w) (high : w≤2916) (count : s.regs 1=BitVec.ofNat 32 w)
    (zero : s.regs 2=0) :
    ∃ n≤5110, ∃ g, X86WordFillRoutine.Prefix program [] n ⟨s,f,0x41927⟩
      ⟨doneCore (groupStart s w).core (4*(w/4)),g,0x41967⟩ := by
  let k := (w/4-2)/2
  let r := w/4-1-2*k
  have small : r=1 ∨ r=2 := by dsimp [r,k]; omega
  have total : 2*k+r=w/4-1 := by dsimp [r,k]; omega
  have words : 8*k+4*(r+1)=4*(w/4) := by dsimp [r,k]; omega
  have cnt : (groupStart s w).core.regs 1=BitVec.ofNat 32 (2*k+r) := by
    rw [total]
    simp only [groupStart,put,write,ite_true]
    have eq : w/4=(w/4-1)+1 := by omega
    conv => lhs; rw [eq]
    simp [BitVec.ofNat_add,BitVec.add_sub_cancel]
  have z : (groupStart s w).core.regs 2=0 := by
    simp [groupStart,X86Routine.pushWord,put,write,zero]
  obtain ⟨n,b,g,path⟩ := groups_execution k r (groupStart s w).core (groupStart s w).flags
    z cnt small (by rw [total]; omega)
  rw [words] at path
  refine ⟨5+n,?_,g,(group_setup s f w low high count).trans path⟩
  dsimp [k] at b
  omega
def tailCore (s : X86Memory.State) (r : Nat) : X86Memory.State :=
  put (put (put {s with memory:=zeros s.memory (s.regs 0) r}
    0 (s.regs 0+BitVec.ofNat 32 (4*r))) 1 (if r=3 then 1 else 0)) 4 (s.regs 4+4)

def tailFlags (r : Nat) : Knowledge :=
  .legacy (some (if r=3 then {compare32 2 1 with carry:=some false} else logical32 0))

theorem tail_stage (s : X86Memory.State) (r : Nat) (small : r<4)
    (count : s.regs 1=BitVec.ofNat 32 r) (zero : s.regs 2=0) :
    ∃ n≤11, X86WordFillRoutine.Prefix program [] n
      ⟨s,.legacy (some (logical32 (BitVec.ofNat 32 r))),0x4196b⟩
      ⟨{tailCore s r with regs:=write (tailCore s r).regs 4 (s.regs 4)},tailFlags r,0x41982⟩ := by
  have same : put s 1 (BitVec.ofNat 32 r)=s := by
    cases s with | mk regs memory =>
      simp only [put]
      congr 1
      funext k
      change regs 1=BitVec.ofNat 32 r at count
      by_cases hk : k=1 <;> simp [write,hk,count]
  let t : X86WordFillRoutine.State :=
    ⟨{tailCore s r with regs:=write (tailCore s r).regs 4 (s.regs 4)},tailFlags r,0x41982⟩
  suffices path : ∃ n≤11, X86WordFillRoutine.Prefix listed [] n
      ⟨put s 1 (BitVec.ofNat 32 r),.legacy (some (logical32 (BitVec.ofNat 32 r))),0x4196b⟩ t by
    obtain ⟨n,b,p⟩ := path
    rw [same] at p
    exact ⟨n,b,p.transfer _ [] decoded (by simp)⟩
  have cases : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases cases with h|h|h|h <;> subst r
  case' inl => refine ⟨1,by omega,?_⟩
  case' inr.inl => refine ⟨5,by omega,?_⟩
  case' inr.inr.inl => refine ⟨9,by omega,?_⟩
  case' inr.inr.inr => refine ⟨11,by omega,?_⟩
  all_goals
    repeat first
      | (exact X86WordFillRoutine.Prefix.nil _)
      | (refine X86WordFillRoutine.Prefix.step (middle:=t) (by simp) rfl ?_ (.nil _)
         simp [t,tailCore,tailFlags,X86WordFillRoutine.execute,
           X86WordFillRoutine.embed,X86WordFillRoutine.preserves,Knowledge.carry,
           X86FillRoutine.execute,X86StartupRoutine.execute,X86ByteRoutine.execute,
           X86Routine.execute,X86Control.execute,X86Block.execute,X86Memory.execute,
           X86Block.Address.eval,blockPreservesFlags,put,write,zeros,BitVec.add_assoc,
           logical32,compare32,count,zero]
         all_goals
           funext k
           by_cases h0 : k=0 <;> by_cases h1 : k=1 <;> by_cases h4 : k=4 <;> simp [write,h0,h1,h4])
      | (refine X86WordFillRoutine.Prefix.step (by simp) rfl rfl ?_
         simp [X86WordFillRoutine.embed,X86Block.execute,X86Memory.execute,
           X86.execute,X86Block.Address.eval,put,write,Knowledge.carry,compare32,logical32,
           blockPreservesFlags,zero])
theorem tail_execution (s : X86Memory.State) (f : Knowledge) (w : Nat)
    (low : 2909≤w) (high : w≤2916) (saved : load32 s.memory (s.regs 4)=BitVec.ofNat 32 w)
    (zero : s.regs 2=0) :
    ∃ n≤13, ∃ g, X86WordFillRoutine.Prefix program [] n ⟨s,f,0x41967⟩
      ⟨tailCore s (w%4),g,0x41982⟩ := by
  have mask : BitVec.ofNat 32 w &&& 3=BitVec.ofNat 32 (w%4) := by
    have cases : w=2909 ∨ w=2910 ∨ w=2911 ∨ w=2912 ∨ w=2913 ∨ w=2914 ∨ w=2915 ∨ w=2916 := by omega
    rcases cases with h|h|h|h|h|h|h|h <;> subst w <;> decide
  simp only [BitVec.ofNat_eq_ofNat] at mask
  let a := put (put s 4 (s.regs 4+4)) 1 (BitVec.ofNat 32 (w%4))
  have lead : X86WordFillRoutine.Prefix listed [] 2 ⟨s,f,0x41967⟩
      ⟨a,.legacy (some (logical32 (BitVec.ofNat 32 (w%4)))),0x4196b⟩ := by
    cases f <;>
      (refine .step (by simp) rfl rfl ?_
       refine .step (middle:=⟨a,.legacy (some (logical32 (BitVec.ofNat 32 (w%4)))),0x4196b⟩)
         (by simp) rfl ?_ (.nil _)
       simp [a,X86WordFillRoutine.execute,X86WordFillRoutine.embed,X86WordFillRoutine.preserves,
         X86FillRoutine.execute,X86StartupRoutine.execute,X86ByteRoutine.execute,
         X86Routine.execute,X86Control.execute,put,write,saved,mask,logical32])
  obtain ⟨n,b,path⟩ := tail_stage a (w%4) (by omega) (by simp [a,put,write])
    (by simp [a,put,write,zero])
  have seam : {tailCore a (w%4) with regs:=write (tailCore a (w%4)).regs 4 (a.regs 4)}=tailCore s (w%4) := by
    simp [tailCore,a,put,write]
    funext k
    by_cases h0 : k=0 <;> by_cases h1 : k=1 <;> by_cases h4 : k=4 <;> simp [write,h0,h1,h4]
  rw [seam] at path
  exact ⟨2+n,by omega,tailFlags (w%4),(lead.transfer _ [] decoded (by simp)).trans path⟩
theorem store_comm (m : Memory) (a b v z : Word) (safe : Apart a b) :
    store32 (store32 m a v) b z=store32 (store32 m b z) a v := by
  have h00 : a+0≠b+0 := safe 0 0
  have h01 : a+0≠b+1 := safe 0 1
  have h02 : a+0≠b+2 := safe 0 2
  have h03 : a+0≠b+3 := safe 0 3
  have h10 : a+1≠b+0 := safe 1 0
  have h11 : a+1≠b+1 := safe 1 1
  have h12 : a+1≠b+2 := safe 1 2
  have h13 : a+1≠b+3 := safe 1 3
  have h20 : a+2≠b+0 := safe 2 0
  have h21 : a+2≠b+1 := safe 2 1
  have h22 : a+2≠b+2 := safe 2 2
  have h23 : a+2≠b+3 := safe 2 3
  have h30 : a+3≠b+0 := safe 3 0
  have h31 : a+3≠b+1 := safe 3 1
  have h32 : a+3≠b+2 := safe 3 2
  have h33 : a+3≠b+3 := safe 3 3
  funext x
  by_cases h0 : x=a
  · subst x; simp_all [store32]
  by_cases h1 : x=a+1
  · subst x; simp_all [store32]
  by_cases h2 : x=a+2
  · subst x; simp_all [store32]
  by_cases h3 : x=a+3
  · subst x; simp_all [store32]
  simp only [BitVec.ofNat_eq_ofNat] at h1 h2 h3
  simp [store32,h0,h1,h2,h3]

theorem zeros_store_comm (m : Memory) (a b v : Word) (n : Nat)
    (safe : ∀ k<n, Apart b (a+BitVec.ofNat 32 (4*k))) :
    store32 (zeros m a n) b v=zeros (store32 m b v) a n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change store32 (store32 (zeros m a n) (a+BitVec.ofNat 32 (4*n)) 0) b v = _
    rw [store_comm _ _ _ _ _ (fun i j => (safe n (by omega) j i).symm),ih (fun k hk=>safe k (by omega))]
    rfl

def BodySafe (s : X86Memory.State) : Prop :=
  ∀ k<2916, Apart (s.regs 4-4) (s.regs 0+BitVec.ofNat 32 (4*k))
def bodyCore (s : X86Memory.State) (h : Nat) : X86Memory.State :=
  tailCore (doneCore (groupStart (headCore s h) (2916-h)).core (4*((2916-h)/4))) ((2916-h)%4)

theorem body_memory (s : X86Memory.State) (h : Nat) (small : h<8) (safe : BodySafe s) :
    (bodyCore s h).memory=zeros (store32 s.memory (s.regs 4-4) (BitVec.ofNat 32 (2916-h))) (s.regs 0) 2916 := by
  simp only [bodyCore,tailCore,doneCore,groupStart,headCore,X86Routine.pushWord,put,write]
  simp only [ite_true,show (0:Reg)≠1 by decide,show (0:Reg)≠4 by decide,
    show (4:Reg)≠0 by decide,show (4:Reg)≠1 by decide,ite_false]
  have guard : ∀ k<h, Apart (s.regs 4-(4#32)) (s.regs 0+BitVec.ofNat 32 (4*k)) :=
    fun k hk=>safe k (by omega)
  rw [zeros_store_comm s.memory (s.regs 0) (s.regs 4-(4#32)) (BitVec.ofNat 32 (2916-h)) h guard]
  rw [←zeros_add]
  rw [←zeros_add]
  congr 1
  omega
theorem group_saved (s : X86Memory.State) (h : Nat) (small : h<8) (safe : BodySafe s) :
    load32 (doneCore (groupStart (headCore s h) (2916-h)).core (4*((2916-h)/4))).memory
      (s.regs 4-4)=BitVec.ofNat 32 (2916-h) := by
  let m := store32 (zeros s.memory (s.regs 0) h) (s.regs 4-4) (BitVec.ofNat 32 (2916-h))
  change load32 (zeros m (s.regs 0+BitVec.ofNat 32 (4*h)) (4*((2916-h)/4))) (s.regs 4-4)=_
  have frame := zeros_frame m (s.regs 0+BitVec.ofNat 32 (4*h)) (s.regs 4-4)
    (4*((2916-h)/4)) (fun k hk=>by
      have guard := safe (h+k) (by omega)
      simpa only [Nat.mul_add,BitVec.ofNat_add,BitVec.add_assoc] using guard)
  exact frame.trans (load_store _ _ _)

theorem body_execution (s : X86Memory.State) (f : Knowledge)
    (count : s.regs 1=2916) (zero : s.regs 2=0)
    (align : readByte s.regs 0 &&& 3=0) (safe : BodySafe s) :
    ∃ h<8, (∃ n≤5170, ∃ g, X86WordFillRoutine.Prefix program [] n ⟨s,f,0x41917⟩
      ⟨bodyCore s h,g,0x41982⟩) ∧
      ∀ j<11664, (bodyCore s h).memory (s.regs 0+BitVec.ofNat 32 j)=0 := by
  obtain ⟨h,small,n,nb,t,lead,pc,core,aligned⟩ := head_execution s f count zero align
  rcases t with ⟨tc,tf,tp⟩
  simp only at pc core
  subst tc; subst tp
  have cnt : (headCore s h).regs 1=BitVec.ofNat 32 (2916-h) := by
    have eq : (2916:Word)=BitVec.ofNat 32 (2916-h)+BitVec.ofNat 32 h := by
      rw [←BitVec.ofNat_add,show (2916-h)+h=2916 by omega]
      rfl
    simp only [headCore,put,write,show (1:Reg)≠0 by decide,ite_false,ite_true,count,eq,BitVec.add_sub_cancel]
  have z : (headCore s h).regs 2=0 := by simp [headCore,put,write,zero]
  obtain ⟨m,mb,g,groups⟩ := grouped_execution (headCore s h) tf (2916-h) (by omega) (by omega) cnt z
  let u := doneCore (groupStart (headCore s h) (2916-h)).core (4*((2916-h)/4))
  have saved : load32 u.memory (u.regs 4)=BitVec.ofNat 32 (2916-h) := by
    have sp : u.regs 4=s.regs 4-4 := by simp [u,doneCore,groupStart,headCore,X86Routine.pushWord,put,write]
    rw [sp]; exact group_saved s h small safe
  have uz : u.regs 2=0 := by simp [u,doneCore,groupStart,headCore,X86Routine.pushWord,put,write,zero]
  obtain ⟨k,kb,last,tail⟩ := tail_execution u g (2916-h) (by omega) (by omega) saved uz
  refine ⟨h,small,⟨n+m+k,by omega,last,(lead.trans groups).trans tail⟩,?_⟩
  intro j hj
  rw [body_memory s h small safe]
  exact zeros_byte _ _ 2916 j hj

theorem body_registers (s : X86Memory.State) (h : Nat) (small : h<8) :
    (bodyCore s h).regs=write (write s.regs 0 (s.regs 0+11664)) 1
      (if (2916-h)%4=3 then 1 else 0) := by
  have sum : 4*h+4*(4*((2916-h)/4))+4*((2916-h)%4)=11664 := by omega
  simp only [bodyCore,tailCore,doneCore,groupStart,headCore,X86Routine.pushWord,put,write]
  funext k
  by_cases h0 : k=0 <;> by_cases h1 : k=1 <;> by_cases h4 : k=4 <;>
    simp [write,h0,h1,h4,BitVec.sub_eq_add_neg,BitVec.add_assoc]
  all_goals rw [←BitVec.ofNat_add,←BitVec.ofNat_add,←Nat.add_assoc,sum]

theorem body_frame (s : X86Memory.State) (h : Nat) (small : h<8) (safe : BodySafe s)
    (a : Word) (stack : Apart a (s.regs 4-4))
    (output : ∀ k<2916, Apart a (s.regs 0+BitVec.ofNat 32 (4*k))) :
    load32 (bodyCore s h).memory a=load32 s.memory a := by
  rw [body_memory s h small safe]
  exact (zeros_frame _ _ _ 2916 output).trans (load_store_apart _ _ _ _ stack)
def ReturnSix (s : X86Memory.State) (base : Word) : Prop :=
  load32 s.memory (s.regs 4)=0x418fc ∧
  load32 s.memory (s.regs 4+4)=11664 ∧
  load32 s.memory (s.regs 4+8)=0x3fe85 ∧
  load32 s.memory (s.regs 4+12)=9 ∧
  load32 s.memory (s.regs 4+16)=base ∧
  load32 s.memory (s.regs 4+20)=0x2e437

def returned4 (s : X86Memory.State) (base : Word) : X86WordFillRoutine.State :=
  ⟨put (put (put s 1 9) 0 base) 4 (s.regs 4+24),.legacy (some (logical32 0)),0x2e437⟩

theorem return_six_execution (s : X86Memory.State) (f : Knowledge) (base : Word)
    (saved : ReturnSix s base) :
    X86WordFillRoutine.Prefix program [] 8 ⟨s,f,0x41982⟩ (returned4 s base) := by
  rcases saved with ⟨h0,h4,h8,h12,h16,h20⟩
  simp only [BitVec.ofNat_eq_ofNat] at h0 h4 h8 h12 h16 h20
  let b := put (put s 4 (s.regs 4+8)) 1 0
  let a : X86WordFillRoutine.State := ⟨put s 4 (s.regs 4+4),f,0x418fc⟩
  have path : X86WordFillRoutine.Prefix returnListing [] 8 ⟨s,f,0x41982⟩ (returned4 s base) := by
    cases f <;>
      (refine .step (middle:=a) (by simp) rfl ?_ ?_)
    all_goals first
      | (simp [a,X86WordFillRoutine.execute,X86WordFillRoutine.embed,X86WordFillRoutine.preserves,
          X86FillRoutine.execute,X86StartupRoutine.execute,X86ByteRoutine.execute,
          X86Routine.execute,put,write,h0])
      | skip
    all_goals
      refine .step (by simp [a]) rfl rfl ?_
      refine .step (by simp [a]) rfl rfl ?_
      refine .step (middle:=⟨b,.legacy (some (logical32 0)),0x41910⟩) (by simp [a]) rfl ?_ ?_
      · simp [a,b,X86WordFillRoutine.execute,X86WordFillRoutine.embed,X86WordFillRoutine.preserves,
          X86FillRoutine.execute,X86StartupRoutine.execute,X86ByteRoutine.execute,
          X86Routine.execute,X86Control.execute,put,write,h4,logical32,BitVec.add_assoc]
      refine .step (middle:=⟨put b 4 (s.regs 4+12),.legacy (some (logical32 0)),0x3fe85⟩)
        (by simp) rfl ?_ ?_
      · simp [b,X86WordFillRoutine.execute,X86WordFillRoutine.embed,
          X86FillRoutine.execute,X86StartupRoutine.execute,X86ByteRoutine.execute,
          X86Routine.execute,put,write,h8,BitVec.add_assoc]
      refine .step (by simp) rfl rfl ?_
      refine .step (by simp) rfl rfl ?_
      refine .step (middle:=returned4 s base) (by simp) rfl ?_ (.nil _)
      simp [b,returned4,X86WordFillRoutine.execute,X86WordFillRoutine.embed,
        X86FillRoutine.execute,X86StartupRoutine.execute,X86ByteRoutine.execute,
        X86Routine.execute,put,write,h12,h16,h20,BitVec.add_assoc]
      funext k
      by_cases h0 : k=0 <;> by_cases h1 : k=1 <;> by_cases h4 : k=4 <;> simp [write,h0,h1,h4]
  exact path.transfer _ [] returns_decoded (by simp)

theorem nested_return_words (s : X86Memory.State) (index : s.regs 1=9)
    (ret : load32 s.memory (s.regs 4)=0x2e437) :
    ReturnSix (E1M1AimSideMemset.wordsCalled s).core (s.regs 0) := by
  simp only [load32,BitVec.ofNat_eq_ofNat] at ret
  simp [ReturnSix,E1M1AimSideMemset.wordsCalled,E1M1AimSideMemset.callWords,
    E1M1AimSideMemset.fillCalled,X86Routine.pushWord,put,write,load32,store32,
    BitVec.sub_eq_add_neg,BitVec.add_assoc,index,ret]
  have h := load_store (fun _=>0) 0 (s.regs 0)
  simpa [load32,store32] using h

theorem slot_succ (sp : Word) (n : Nat) :
    sp+BitVec.ofNat 32 (4*(n+1))=sp+4+BitVec.ofNat 32 (4*n) := by
  simp only [Nat.mul_add,Nat.mul_one,BitVec.ofNat_add,BitVec.ofNat_eq_ofNat]
  ac_rfl

theorem slot_above_push (sp : Word) (i : Fin 6) :
    Apart (sp+BitVec.ofNat 32 (4*i.val)) (sp-4) := by
  have h := PlayerHeight.slots_apart (sp-4) (⟨i.val+1,by omega⟩:Fin 8) 0 (by
    intro eq; have := congrArg Fin.val eq; simp at this)
  simpa only [Fin.val_mk,Fin.val_zero,Nat.mul_zero,BitVec.ofNat_eq_ofNat,
    BitVec.add_zero,slot_succ,BitVec.sub_add_cancel] using h

theorem body_return_words (s : X86Memory.State) (h : Nat) (small : h<8)
    (index : s.regs 1=9) (ret : load32 s.memory (s.regs 4)=0x2e437) (safe : Saved32Safe s) :
    ReturnSix (bodyCore (E1M1AimSideMemset.wordsCalled s).core h) (s.regs 0) := by
  let w := (E1M1AimSideMemset.wordsCalled s).core
  have sp : w.regs 4=s.regs 4-20 := by
    simp [w,E1M1AimSideMemset.wordsCalled,E1M1AimSideMemset.callWords,E1M1AimSideMemset.fillCalled,
      X86Routine.pushWord,put,write,BitVec.sub_eq_add_neg,BitVec.add_assoc]
  have base : w.regs 0=s.regs 0 := by
    simp [w,E1M1AimSideMemset.wordsCalled,E1M1AimSideMemset.callWords,E1M1AimSideMemset.fillCalled,
      X86Routine.pushWord,put,write]
  have bs : BodySafe w := by
    intro k hk
    have a := safe 0 k hk
    simpa [sp,base,BitVec.sub_eq_add_neg,BitVec.add_assoc] using a
  have frame (i : Fin 6) : load32 (bodyCore w h).memory (w.regs 4+BitVec.ofNat 32 (4*i.val))=
      load32 w.memory (w.regs 4+BitVec.ofNat 32 (4*i.val)) := by
    apply body_frame w h small bs _ (slot_above_push _ i)
    intro k hk
    have a := safe ⟨i.val+1,by omega⟩ k hk
    simp only [Fin.val_mk,slot_succ] at a
    simpa [sp,base,BitVec.sub_eq_add_neg,BitVec.add_assoc] using a
  have finalsp : (bodyCore w h).regs 4=w.regs 4 := by rw [body_registers w h small]; simp [write]
  have old := nested_return_words s index ret
  change ReturnSix w (s.regs 0) at old
  simp only [ReturnSix] at old
  change ReturnSix (bodyCore w h) (s.regs 0)
  simp only [ReturnSix,finalsp]
  have frame0 : load32 (bodyCore w h).memory (w.regs 4)=load32 w.memory (w.regs 4) := by
    simpa only [Fin.val_zero,Nat.mul_zero,BitVec.ofNat_eq_ofNat,BitVec.add_zero] using frame 0
  exact ⟨frame0.trans old.1,(frame 1).trans old.2.1,(frame 2).trans old.2.2.1,
    (frame 3).trans old.2.2.2.1,(frame 4).trans old.2.2.2.2.1,(frame 5).trans old.2.2.2.2.2⟩
def completed (s : X86Memory.State) (h : Nat) :=
  returned4 (bodyCore (E1M1AimSideMemset.wordsCalled s).core h) (s.regs 0)

theorem nested_body_safe (s : X86Memory.State) (safe : Saved32Safe s) :
    BodySafe (E1M1AimSideMemset.wordsCalled s).core := by
  intro k hk
  have a := safe 0 k hk
  simpa [E1M1AimSideMemset.wordsCalled,E1M1AimSideMemset.callWords,E1M1AimSideMemset.fillCalled,
    X86Routine.pushWord,put,write,BitVec.sub_eq_add_neg,BitVec.add_assoc] using a

theorem memset_execution (s : X86Memory.State) (f : Option Flags)
    (zero : s.regs 2=0) (size : s.regs 3=11664) (index : s.regs 1=9)
    (ret : load32 s.memory (s.regs 4)=0x2e437)
    (aligned : readByte s.regs 0 &&& 3=0) (safe : Saved32Safe s) :
    ∃ h<8, (∃ n≤5200, X86WordFillRoutine.Prefix program [] n (X86WordFillRoutine.embed ⟨s,f,0x3fe70⟩)
      (completed s h)) ∧ (completed s h).pc=0x2e437 ∧
      (∀ j<11664, (completed s h).core.memory (s.regs 0+BitVec.ofNat 32 j)=0) := by
  have lead := (X86WordFillRoutine.lift_prefix
    (E1M1AimSideMemset.nested_execution s f zero size aligned)).transfer program [] previous_agrees (by simp)
  have wc : (E1M1AimSideMemset.wordsCalled s).core.regs 1=2916 := by
    simp [E1M1AimSideMemset.wordsCalled,E1M1AimSideMemset.callWords,X86Routine.pushWord,put,write]
  have wz : (E1M1AimSideMemset.wordsCalled s).core.regs 2=0 := by
    simp [E1M1AimSideMemset.wordsCalled,E1M1AimSideMemset.callWords,E1M1AimSideMemset.fillCalled,X86Routine.pushWord,put,write]
  have wa : readByte (E1M1AimSideMemset.wordsCalled s).core.regs 0 &&& 3=0 := by
    simpa [readByte,byteReg,E1M1AimSideMemset.wordsCalled,E1M1AimSideMemset.callWords,
      E1M1AimSideMemset.fillCalled,X86Routine.pushWord,put,write] using aligned
  obtain ⟨h,small,⟨n,bound,g,body⟩,zeros⟩ := body_execution
    (E1M1AimSideMemset.wordsCalled s).core (.legacy none) wc wz wa (nested_body_safe s safe)
  have tail := return_six_execution (bodyCore (E1M1AimSideMemset.wordsCalled s).core h) g (s.regs 0)
    (body_return_words s h small index ret safe)
  refine ⟨h,small,⟨17+n+8,by omega,(lead.trans body).trans tail⟩,rfl,?_⟩
  simpa [completed,returned4,put,E1M1AimSideMemset.wordsCalled,E1M1AimSideMemset.callWords,
    E1M1AimSideMemset.fillCalled,X86Routine.pushWord,write] using zeros

def finished (s : X86Memory.State) (h : Nat) := completed (E1M1AimSidePublish.published s).core h

theorem entry_execution (s : X86Memory.State) (f : Option Flags) (table : Word)
    (initial : E1M1AimSideEntry.Initial s table) (v : OriginalGroupHeap.View)
    (heap : E1M1AimSideAllocate.HeapInitial s v) (frame : E1M1AimSidePublish.AllocationFrame s v)
    (aligned : (v.block+24).extractLsb' 0 8 &&& 3=0) (safe : Entry32Safe s v) :
    ∃ h<8, (∃ n≤5300, X86WordFillRoutine.Prefix program [] n
      (X86WordFillRoutine.embed ⟨s,f,0x2e3e0⟩) (finished s h)) ∧
      (finished s h).pc=0x2e437 ∧
      ∀ j<11664, (finished s h).core.memory (v.block+24+BitVec.ofNat 32 j)=0 := by
  obtain ⟨⟨n,bound,path⟩,pc,base,index,zero,size,sp,ret⟩ :=
    E1M1AimSidePublish.execution s f table initial v heap frame
  have align : readByte (E1M1AimSidePublish.published s).core.regs 0 &&& 3=0 := by
    simpa [readByte,byteReg,base] using aligned
  have stack : Saved32Safe (E1M1AimSidePublish.published s).core := by
    simpa [Saved32Safe,Entry32Safe,sp,base,BitVec.sub_eq_add_neg,BitVec.add_assoc] using safe
  obtain ⟨h,small,⟨m,mb,suffix⟩,endpc,zeros⟩ := memset_execution (E1M1AimSidePublish.published s).core
    (E1M1AimSidePublish.published s).flags zero size index ret align stack
  have seam : (⟨(E1M1AimSidePublish.published s).core,(E1M1AimSidePublish.published s).flags,
      0x3fe70⟩ : X86Control.State)=E1M1AimSidePublish.published s := by rw [←pc]
  rw [seam] at suffix
  have lead := (X86WordFillRoutine.lift_prefix ((X86FillRoutine.lift_prefix path).transfer
    E1M1AimSideMemset.program [] E1M1AimSideMemset.startup_agrees (by simp))).transfer
    program [] previous_agrees (by simp)
  exact ⟨h,small,⟨n+m,by omega,lead.trans suffix⟩,endpc,by simpa only [base,finished] using zeros⟩
theorem completed_registers (s : X86Memory.State) (h : Nat) (small : h<8) :
    (completed s h).core.regs=write (write (write s.regs 1 9) 2 0) 4 (s.regs 4+4) := by
  simp only [completed,returned4,put,body_registers _ h small]
  funext k
  by_cases h0 : k=0 <;> by_cases h1 : k=1 <;> by_cases h2 : k=2 <;> by_cases h4 : k=4 <;>
    simp [E1M1AimSideMemset.wordsCalled,E1M1AimSideMemset.callWords,E1M1AimSideMemset.fillCalled,
      X86Routine.pushWord,put,write,h0,h1,h2,h4,BitVec.sub_eq_add_neg,BitVec.add_assoc]

theorem entry_registers (s : X86Memory.State) (f : Option Flags) (table : Word)
    (initial : E1M1AimSideEntry.Initial s table) (v : OriginalGroupHeap.View)
    (heap : E1M1AimSideAllocate.HeapInitial s v) (frame : E1M1AimSidePublish.AllocationFrame s v)
    (h : Nat) (small : h<8) :
    (finished s h).core.regs 0=v.block+24 ∧ (finished s h).core.regs 1=9 ∧
    (finished s h).core.regs 2=0 ∧ (finished s h).core.regs 3=11664 ∧
    (finished s h).core.regs 4=s.regs 4-32 := by
  obtain ⟨_,pc,base,index,zero,size,sp,ret⟩ := E1M1AimSidePublish.execution s f table initial v heap frame
  simp [finished,completed_registers _ h small,write,base,size,sp,BitVec.sub_eq_add_neg,BitVec.add_assoc]

theorem entry_nested_frame (s : X86Memory.State) (f : Option Flags) (table : Word)
    (initial : E1M1AimSideEntry.Initial s table) (v : OriginalGroupHeap.View)
    (heap : E1M1AimSideAllocate.HeapInitial s v) (frame : E1M1AimSidePublish.AllocationFrame s v)
    (h : Nat) (small : h<8) (safe : Entry32Safe s v)
    (a : Word) (stack : Apart a (s.regs 4-60))
    (output : ∀ k<2916, Apart a (v.block+24+BitVec.ofNat 32 (4*k))) :
    load32 (finished s h).core.memory a=load32 (E1M1AimSideMemset.nested s).core.memory a := by
  obtain ⟨_,pc,base,index,zero,size,sp,ret⟩ := E1M1AimSidePublish.execution s f table initial v heap frame
  have ss : Saved32Safe (E1M1AimSidePublish.published s).core := by
    simpa [Saved32Safe,Entry32Safe,sp,base,BitVec.sub_eq_add_neg,BitVec.add_assoc] using safe
  apply body_frame _ h small (nested_body_safe _ ss)
  · simpa [E1M1AimSideMemset.wordsCalled,E1M1AimSideMemset.callWords,E1M1AimSideMemset.fillCalled,
      X86Routine.pushWord,put,write,sp,BitVec.sub_eq_add_neg,BitVec.add_assoc] using stack
  · simpa [E1M1AimSideMemset.wordsCalled,E1M1AimSideMemset.callWords,E1M1AimSideMemset.fillCalled,
      X86Routine.pushWord,put,write,base] using output
theorem entry_count_preserved (s : X86Memory.State) (f : Option Flags) (table : Word)
    (initial : E1M1AimSideEntry.Initial s table) (v : OriginalGroupHeap.View)
    (heap : E1M1AimSideAllocate.HeapInitial s v) (frame : E1M1AimSidePublish.AllocationFrame s v)
    (h : Nat) (small : h<8) (safe : Entry32Safe s v)
    (before : E1M1AimSideMemset.EntrySafe s 0x2c11c) (output : OutputSafe s v 0x2c11c) :
    load32 (finished s h).core.memory 0x2c11c=648 := by
  exact (entry_nested_frame s f table initial v heap frame h small safe _ output.1 output.2).trans
    (E1M1AimSideMemset.count_preserved s f table initial v heap frame before)

theorem entry_base_preserved (s : X86Memory.State) (f : Option Flags) (table : Word)
    (initial : E1M1AimSideEntry.Initial s table) (v : OriginalGroupHeap.View)
    (heap : E1M1AimSideAllocate.HeapInitial s v) (frame : E1M1AimSidePublish.AllocationFrame s v)
    (h : Nat) (small : h<8) (safe : Entry32Safe s v)
    (before : OriginalGroupHeap.Separated 0x2c118
      [s.regs 4-36,s.regs 4-40,s.regs 4-44,s.regs 4-48,s.regs 4-52,s.regs 4-56])
    (output : OutputSafe s v 0x2c118) :
    load32 (finished s h).core.memory 0x2c118=v.block+24 := by
  exact (entry_nested_frame s f table initial v heap frame h small safe _ output.1 output.2).trans
    (E1M1AimSideMemset.base_preserved s f table initial v heap before)

theorem entry_upper_preserved (s : X86Memory.State) (f : Option Flags) (table : Word)
    (initial : E1M1AimSideEntry.Initial s table) (v : OriginalGroupHeap.View)
    (heap : E1M1AimSideAllocate.HeapInitial s v) (frame : E1M1AimSidePublish.AllocationFrame s v)
    (h : Nat) (small : h<8) (safe : Entry32Safe s v)
    (a : Word) (ha : a∈E1M1AimSidePublish.upperWords s)
    (before : E1M1AimSideMemset.EntrySafe s a) (output : OutputSafe s v a) :
    load32 (finished s h).core.memory a=load32 (E1M1AimSideEntry.savedMemory s) a := by
  exact (entry_nested_frame s f table initial v heap frame h small safe a output.1 output.2).trans
    (E1M1AimSideMemset.upper_preserved s f table initial v heap frame a ha before)
end Doom.Proofs.E1M1AimWordAligned
