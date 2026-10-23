import Doom.Proofs.E1M1PspriteLight
import Doom.Proofs.WeaponActions
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace Doom.Proofs.E1M1FlashInstall
open Verification X86 X86Memory X86Control BlockSummary

def pointer (gun : Fire.Gun) : Word := BitVec.ofNat 32 (0x15a28+28*WeaponActions.flashFrame gun)
def timer : Fire.Gun → Word | .pistol => 7 | .shotgun => 4
def successor : Fire.Gun → Word | .pistol => 1 | .shotgun => 31

def location (gun : Fire.Gun) (p sp : Word) (i : Fin 11) : Word := match i.val with
  | 0 => p+(232#32) | 1 => p+(260#32) | 2 => p+(264#32)
  | 3 => sp | 4 => sp+(0xfffffffc#32) | 5 => sp+(0xfffffff8#32) | 6 => sp+(0xfffffff4#32)
  | 7 => pointer gun+(8#32) | 8 => pointer gun+(12#32) | 9 => pointer gun+(16#32)
  | _ => pointer gun+(20#32)

def Separated (gun : Fire.Gun) (p sp : Word) : Prop :=
  ∀ i j : Fin 11, i≠j → Apart (location gun p sp i) (location gun p sp j)
theorem location_0 (gun : Fire.Gun) (p sp : Word) : location gun p sp 0=p+(232#32) := rfl
theorem location_1 (gun : Fire.Gun) (p sp : Word) : location gun p sp 1=p+(260#32) := rfl
theorem location_2 (gun : Fire.Gun) (p sp : Word) : location gun p sp 2=p+(264#32) := rfl
theorem location_3 (gun : Fire.Gun) (p sp : Word) : location gun p sp 3=sp := rfl
theorem location_4 (gun : Fire.Gun) (p sp : Word) : location gun p sp 4=sp+(0xfffffffc#32) := rfl
theorem location_5 (gun : Fire.Gun) (p sp : Word) : location gun p sp 5=sp+(0xfffffff8#32) := rfl
theorem location_6 (gun : Fire.Gun) (p sp : Word) : location gun p sp 6=sp+(0xfffffff4#32) := rfl
theorem location_7 (gun : Fire.Gun) (p sp : Word) : location gun p sp 7=pointer gun+(8#32) := rfl
theorem location_8 (gun : Fire.Gun) (p sp : Word) : location gun p sp 8=pointer gun+(12#32) := rfl
theorem location_9 (gun : Fire.Gun) (p sp : Word) : location gun p sp 9=pointer gun+(16#32) := rfl
theorem location_10 (gun : Fire.Gun) (p sp : Word) : location gun p sp 10=pointer gun+(20#32) := rfl

@[local simp] theorem shift_4_5 (gun : Fire.Gun) (p sp : Word) :
    location gun p sp 4+(0xfffffffc#32)=location gun p sp 5 := by
  change (sp+(0xfffffffc#32))+(0xfffffffc#32)=sp+(0xfffffff8#32)
  simp only [BitVec.add_assoc]; rfl
@[local simp] theorem shift_4_6 (gun : Fire.Gun) (p sp : Word) :
    location gun p sp 4+(0xfffffff8#32)=location gun p sp 6 := by
  change (sp+(0xfffffffc#32))+(0xfffffff8#32)=sp+(0xfffffff4#32)
  simp only [BitVec.add_assoc]; rfl
@[local simp] theorem pop_4 (gun : Fire.Gun) (p sp : Word) :
    location gun p sp 4+(4#32)=sp := by
  change (sp+(0xfffffffc#32))+(4#32)=sp
  simp [BitVec.add_assoc]
@[local simp] theorem shift_5_4 (gun : Fire.Gun) (p sp : Word) :
    location gun p sp 5+(0x4#32)=location gun p sp 4 := by
  change (sp+(0xfffffff8#32))+(0x4#32)=sp+(0xfffffffc#32)
  simp only [BitVec.add_assoc]; rfl
@[local simp] theorem shift_5_6 (gun : Fire.Gun) (p sp : Word) :
    location gun p sp 5+(0xfffffffc#32)=location gun p sp 6 := by
  change (sp+(0xfffffff8#32))+(0xfffffffc#32)=sp+(0xfffffff4#32)
  simp only [BitVec.add_assoc]; rfl
@[local simp] theorem pop_5 (gun : Fire.Gun) (p sp : Word) :
    location gun p sp 5+(8#32)=sp := by
  change (sp+(0xfffffff8#32))+(8#32)=sp
  simp [BitVec.add_assoc]
@[local simp] theorem shift_6_4 (gun : Fire.Gun) (p sp : Word) :
    location gun p sp 6+(0x8#32)=location gun p sp 4 := by
  change (sp+(0xfffffff4#32))+(0x8#32)=sp+(0xfffffffc#32)
  simp only [BitVec.add_assoc]; rfl
@[local simp] theorem shift_6_5 (gun : Fire.Gun) (p sp : Word) :
    location gun p sp 6+(0x4#32)=location gun p sp 5 := by
  change (sp+(0xfffffff4#32))+(0x4#32)=sp+(0xfffffff8#32)
  simp only [BitVec.add_assoc]; rfl
@[local simp] theorem pop_6 (gun : Fire.Gun) (p sp : Word) :
    location gun p sp 6+(12#32)=sp := by
  change (sp+(0xfffffff4#32))+(12#32)=sp
  simp [BitVec.add_assoc]
@[local simp] theorem field_timer (gun : Fire.Gun) (p sp : Word) :
    location gun p sp 1+(4#32)=location gun p sp 2 := by
  change (p+(260#32))+(4#32)=p+(264#32)
  simp only [BitVec.add_assoc]; rfl

theorem read_store (gun : Fire.Gun) (p sp : Word) (h : Separated gun p sp)
    (m : Memory) (i j : Fin 11) (v : Word) :
    load32 (store32 m (location gun p sp i) v) (location gun p sp j) =
      if j=i then v else load32 m (location gun p sp j) := by
  by_cases eq : j=i
  · subst j; simp [load_store]
  · rw [if_neg eq]; exact load_store_apart _ _ _ _ (h j i eq)

structure Inputs (gun : Fire.Gun) (s : X86Memory.State) : Prop where
  slot : s.regs 2=1
  state : s.regs 3=BitVec.ofNat 32 (WeaponActions.flashFrame gun)
  tics : load32 s.memory (pointer gun+(8#32))=timer gun
  action : load32 s.memory (pointer gun+(12#32))=0x2db50
  next : load32 s.memory (pointer gun+(16#32))=successor gun
  misc : load32 s.memory (pointer gun+(20#32))=0
  safe : Separated gun (s.regs 0) (s.regs 4)

def memory (gun : Fire.Gun) (s : X86Memory.State) : Memory :=
  let m := store32 (store32 s.memory (s.regs 4-4) (s.regs 1)) (s.regs 4-8) (s.regs 6)
  let m := store32 (store32 m (s.regs 0+(260#32)) (pointer gun)) (s.regs 0+(264#32)) (timer gun)
  store32 (store32 m (s.regs 4-12) 0x2d095) (s.regs 0+(232#32)) 1

def result (gun : Fire.Gun) (s : X86Memory.State) : X86Control.State :=
  ⟨⟨write (write (write (write s.regs 0 (successor gun)) 2 (timer gun))
      3 (s.regs 0+(260#32))) 4 (s.regs 4+4), memory gun s⟩,
    some (logical32 (timer gun)), (load32 s.memory (s.regs 4)).toNat⟩

/-- Prove the existing original-byte chain driver succeeds from initial table
and separation facts. No evaluator-success or output hypothesis is supplied. -/
theorem summary (gun : Fire.Gun) (s : X86Memory.State) (h : Inputs gun s) :
    E1M1PspriteLight.complete 2 s = some (result gun s) := by
  have idNonzero : BitVec.ofNat 32 (WeaponActions.flashFrame gun) ≠ (0#32) := by cases gun <;> decide
  have ptrNonzero : pointer gun ≠ (0#32) := by cases gun <;> decide
  have timerNonzero : timer gun ≠ (0#32) := by cases gun <;> decide
  have ptrEq : (0x15a28#32)+BitVec.ofNat 32 (WeaponActions.flashFrame gun)*(28#32)=pointer gun := by cases gun <;> decide
  have readReturn (m : Memory) (i : Fin 11) (v : Word) :
      load32 (store32 m (location gun (s.regs 0) (s.regs 4) i) v) (s.regs 4) =
        if (3 : Fin 11)=i then v else load32 m (s.regs 4) :=
    read_store gun (s.regs 0) (s.regs 4) h.safe m i 3 v
  have ht := h.tics
  have ha := h.action
  have hn := h.next
  have hm := h.misc
  have hs := h.safe
  simp only [←location_0 gun (s.regs 0) (s.regs 4), ←location_1 gun (s.regs 0) (s.regs 4), ←location_2 gun (s.regs 0) (s.regs 4), ←location_4 gun (s.regs 0) (s.regs 4), ←location_5 gun (s.regs 0) (s.regs 4), ←location_6 gun (s.regs 0) (s.regs 4), ←location_7 gun (s.regs 0) (s.regs 4), ←location_8 gun (s.regs 0) (s.regs 4), ←location_9 gun (s.regs 0) (s.regs 4), ←location_10 gun (s.regs 0) (s.regs 4)] at ht ha hn hm
  simp [E1M1PspriteLight.complete,E1M1PspriteLight.chain,PspriteChainDriver.chain,
    E1M1PspriteLight.advance,E1M1PspriteLight.index,E1M1PspriteChain.NoAction,
    E1M1PspriteSetter.dispatched,E1M1PspriteSetter.positioned,E1M1PspriteSetter.resumed,
    PspriteSetter.entered,PspriteSetter.prepared,PspriteSetter.installed,PspriteSetter.store,
    PspriteSetter.called,PspriteSetter.actionGate,PspriteSetter.successor,PspriteSetter.next,
    PspriteSetter.returned,PspriteSetter.cleared,PspriteSetter.afterAction,PspriteLight.result,
    PspriteLight.written,PspriteLoop.popped,X86Routine.pushWord,put,write,h.slot,h.state,idNonzero,ptrNonzero,timerNonzero,ptrEq,readReturn,
    BitVec.sub_eq_add_neg,BitVec.add_assoc,BitVec.ofNat_eq_ofNat,
    ←location_0 gun (s.regs 0) (s.regs 4), ←location_1 gun (s.regs 0) (s.regs 4), ←location_2 gun (s.regs 0) (s.regs 4), ←location_4 gun (s.regs 0) (s.regs 4), ←location_5 gun (s.regs 0) (s.regs 4), ←location_6 gun (s.regs 0) (s.regs 4), ←location_7 gun (s.regs 0) (s.regs 4), ←location_8 gun (s.regs 0) (s.regs 4), ←location_9 gun (s.regs 0) (s.regs 4), ←location_10 gun (s.regs 0) (s.regs 4),read_store gun (s.regs 0) (s.regs 4) hs,ht,ha,hn,hm]
  simp [result,memory,location_0,location_1,location_2,location_4,location_5,location_6,
    BitVec.sub_eq_add_neg]
  funext r
  by_cases h0 : r=0 <;> by_cases h1 : r=1 <;> by_cases h2 : r=2 <;>
    by_cases h3 : r=3 <;> by_cases h4 : r=4 <;> by_cases h6 : r=6 <;> simp_all [write,BitVec.add_assoc]

def writes (s : X86Memory.State) : List Word :=
  [s.regs 4-4,s.regs 4-8,s.regs 0+260,s.regs 0+264,s.regs 4-12,s.regs 0+232]

theorem memory_frame (gun : Fire.Gun) (s : X86Memory.State) (a : Word)
    (safe : ∀ b, b ∈ writes s → Apart a b) :
    load32 (result gun s).core.memory a = load32 s.memory a := by
  simp only [result,memory]
  repeat rw [load_store_apart _ _ _ _ (safe _ (by simp [writes]))]

theorem observations (gun : Fire.Gun) (s : X86Memory.State)
    (h : Separated gun (s.regs 0) (s.regs 4)) :
    (load32 (result gun s).core.memory (s.regs 0+260),
     load32 (result gun s).core.memory (s.regs 0+264),
     load32 (result gun s).core.memory (s.regs 0+232)) = (pointer gun,timer gun,1) := by
  simp [result,memory,BitVec.sub_eq_add_neg,BitVec.ofNat_eq_ofNat,
    ←location_0 gun (s.regs 0) (s.regs 4), ←location_1 gun (s.regs 0) (s.regs 4),
    ←location_2 gun (s.regs 0) (s.regs 4), ←location_4 gun (s.regs 0) (s.regs 4),
    ←location_5 gun (s.regs 0) (s.regs 4), ←location_6 gun (s.regs 0) (s.regs 4),
    read_store gun (s.regs 0) (s.regs 4) h]

/-- Installation precedes the same-tic countdown. Its timers are 7/4, not 6/3. -/
theorem live_observations (gun : Fire.Gun) (s : X86Memory.State) (c : Weapon.Context)
    (h : Separated gun (s.regs 0) (s.regs 4)) :
    (load32 (result gun s).core.memory (s.regs 0+260),
     load32 (result gun s).core.memory (s.regs 0+264),
     load32 (result gun s).core.memory (s.regs 0+232)) =
      (BitVec.ofNat 32 (0x15a28+28*(Weapon.fireAction gun c).state.flash.frame),
       (Weapon.fireAction gun c).state.flash.tics.toBitVec,
       (Weapon.fireAction gun c).state.extraLight.toBitVec) := by
  rw [observations gun s h]
  cases gun <;> rfl

theorem execution (gun : Fire.Gun) (s : X86Memory.State) (f : Option Flags)
    (h : Inputs gun s) :
    ∃ n, n≤77 ∧ X86CodeMemory.Prefix FloorCaller.cm E1M1PspriteLight.program [] n
      ⟨s,f,0x2d040⟩ (result gun s) :=
  E1M1PspriteLight.complete_execution 2 s f (result gun s) (summary gun s h)

end Doom.Proofs.E1M1FlashInstall
