import Doom.Proofs.E1M1FlashUpdate
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace Doom.Proofs.E1M1FlashExpiry
open Verification X86 X86Memory X86Control BlockSummary

/-- Player observation fields, four scratch stack words, and the original
flash-table fields read by the expiring-slot path. Addresses wrap at 32 bits. -/
def location (p sp : Word) (i : Fin 19) : Word := match i.val with
  | 0 => p+(232#32)
  | 1 => p+(252#32)
  | 2 => p+(256#32)
  | 3 => p+(260#32)
  | 4 => p+(264#32)
  | 5 => sp+(0xfffffffc#32)
  | 6 => sp+(0xfffffff8#32)
  | 7 => sp+(0xfffffff4#32)
  | 8 => sp+(0xfffffff0#32)
  | 9 => (0x15a4c#32)
  | 10 => (0x15a50#32)
  | 11 => (0x15a54#32)
  | 12 => (0x15a58#32)
  | 13 => (0x15d94#32)
  | 14 => (0x15d98#32)
  | 15 => (0x15d9c#32)
  | 16 => (0x15da0#32)
  | 17 => (0x15c14#32)
  | _ => (0x15d80#32)

def Separated (p sp : Word) : Prop :=
  ∀ i j : Fin 19, i≠j → Apart (location p sp i) (location p sp j)
theorem location_0 (p sp : Word) : location p sp 0=p+(232#32) := rfl
theorem location_1 (p sp : Word) : location p sp 1=p+(252#32) := rfl
theorem location_2 (p sp : Word) : location p sp 2=p+(256#32) := rfl
theorem location_3 (p sp : Word) : location p sp 3=p+(260#32) := rfl
theorem location_4 (p sp : Word) : location p sp 4=p+(264#32) := rfl
theorem location_5 (p sp : Word) : location p sp 5=sp+(0xfffffffc#32) := rfl
theorem location_6 (p sp : Word) : location p sp 6=sp+(0xfffffff8#32) := rfl
theorem location_7 (p sp : Word) : location p sp 7=sp+(0xfffffff4#32) := rfl
theorem location_8 (p sp : Word) : location p sp 8=sp+(0xfffffff0#32) := rfl
theorem location_9 (p sp : Word) : location p sp 9=(0x15a4c#32) := rfl
theorem location_10 (p sp : Word) : location p sp 10=(0x15a50#32) := rfl
theorem location_11 (p sp : Word) : location p sp 11=(0x15a54#32) := rfl
theorem location_12 (p sp : Word) : location p sp 12=(0x15a58#32) := rfl
theorem location_13 (p sp : Word) : location p sp 13=(0x15d94#32) := rfl
theorem location_14 (p sp : Word) : location p sp 14=(0x15d98#32) := rfl
theorem location_15 (p sp : Word) : location p sp 15=(0x15d9c#32) := rfl
theorem location_16 (p sp : Word) : location p sp 16=(0x15da0#32) := rfl
theorem location_17 (p sp : Word) : location p sp 17=(0x15c14#32) := rfl
theorem location_18 (p sp : Word) : location p sp 18=(0x15d80#32) := rfl

@[local simp] theorem location_add_3_4 (p sp : Word) : location p sp 3+(4#32)=location p sp 4 := by
  change (p+(260#32))+(4#32)=p+(264#32)
  simp only [BitVec.add_assoc]
  rfl
@[local simp] theorem location_add_5_6 (p sp : Word) : location p sp 5+(0xfffffffc#32)=location p sp 6 := by
  change (sp+(0xfffffffc#32))+(0xfffffffc#32)=sp+(0xfffffff8#32)
  simp only [BitVec.add_assoc]
  rfl
@[local simp] theorem location_add_6_5 (p sp : Word) : location p sp 6+(4#32)=location p sp 5 := by
  change (sp+(0xfffffff8#32))+(4#32)=sp+(0xfffffffc#32)
  simp only [BitVec.add_assoc]
  rfl
@[local simp] theorem location_add_6_7 (p sp : Word) : location p sp 6+(0xfffffffc#32)=location p sp 7 := by
  change (sp+(0xfffffff8#32))+(0xfffffffc#32)=sp+(0xfffffff4#32)
  simp only [BitVec.add_assoc]
  rfl
@[local simp] theorem location_add_7_6 (p sp : Word) : location p sp 7+(4#32)=location p sp 6 := by
  change (sp+(0xfffffff4#32))+(4#32)=sp+(0xfffffff8#32)
  simp only [BitVec.add_assoc]
  rfl
@[local simp] theorem location_add_7_8 (p sp : Word) : location p sp 7+(0xfffffffc#32)=location p sp 8 := by
  change (sp+(0xfffffff4#32))+(0xfffffffc#32)=sp+(0xfffffff0#32)
  simp only [BitVec.add_assoc]
  rfl
@[local simp] theorem location_add_8_7 (p sp : Word) : location p sp 8+(4#32)=location p sp 7 := by
  change (sp+(0xfffffff0#32))+(4#32)=sp+(0xfffffff4#32)
  simp only [BitVec.add_assoc]
  rfl
@[local simp] theorem location_stack_5 (p sp : Word) : location p sp 5+(4#32)=sp := by
  change (sp+(0xfffffffc#32))+(4#32)=sp
  simp [BitVec.add_assoc]

@[local simp] theorem location_add_5_7 (p sp : Word) : location p sp 5+(0xfffffff8#32)=location p sp 7 := by
  change (sp+(0xfffffffc#32))+(0xfffffff8#32)=sp+(0xfffffff4#32)
  simp only [BitVec.add_assoc]
  rfl
@[local simp] theorem location_add_5_8 (p sp : Word) : location p sp 5+(0xfffffff4#32)=location p sp 8 := by
  change (sp+(0xfffffffc#32))+(0xfffffff4#32)=sp+(0xfffffff0#32)
  simp only [BitVec.add_assoc]
  rfl
@[local simp] theorem location_add_6_8 (p sp : Word) : location p sp 6+(0xfffffff8#32)=location p sp 8 := by
  change (sp+(0xfffffff8#32))+(0xfffffff8#32)=sp+(0xfffffff0#32)
  simp only [BitVec.add_assoc]
  rfl
@[local simp] theorem location_stack_6 (p sp : Word) : location p sp 6+(8#32)=sp := by
  change (sp+(0xfffffff8#32))+(8#32)=sp
  simp [BitVec.add_assoc]
@[local simp] theorem location_add_7_5 (p sp : Word) : location p sp 7+(8#32)=location p sp 5 := by
  change (sp+(0xfffffff4#32))+(8#32)=sp+(0xfffffffc#32)
  simp only [BitVec.add_assoc]
  rfl
@[local simp] theorem location_stack_7 (p sp : Word) : location p sp 7+(12#32)=sp := by
  change (sp+(0xfffffff4#32))+(12#32)=sp
  simp [BitVec.add_assoc]
@[local simp] theorem location_add_8_5 (p sp : Word) : location p sp 8+(12#32)=location p sp 5 := by
  change (sp+(0xfffffff0#32))+(12#32)=sp+(0xfffffffc#32)
  simp only [BitVec.add_assoc]
  rfl
@[local simp] theorem location_add_8_6 (p sp : Word) : location p sp 8+(8#32)=location p sp 6 := by
  change (sp+(0xfffffff0#32))+(8#32)=sp+(0xfffffff8#32)
  simp only [BitVec.add_assoc]
  rfl
@[local simp] theorem location_stack_8 (p sp : Word) : location p sp 8+(16#32)=sp := by
  change (sp+(0xfffffff0#32))+(16#32)=sp
  simp [BitVec.add_assoc]

theorem read_store (p sp : Word) (h : Separated p sp) (m : Memory) (i j : Fin 19) (v : Word) :
    load32 (store32 m (location p sp i) v) (location p sp j)=
      if j=i then v else load32 m (location p sp j) := by
  by_cases eq : j=i
  · subst j; simp [load_store]
  · rw [if_neg eq]; exact load_store_apart _ _ _ _ (h j i eq)

/-- Only initial memory contents, not evaluator-success or output assumptions. -/
structure Tables (m : Memory) : Prop where
  lightDoneTics : load32 m (0x15a4c#32)=(0#32)
  lightDoneAction : load32 m (0x15a50#32)=(0x2db40#32)
  lightDoneNext : load32 m (0x15a54#32)=(0#32)
  lightDoneMisc : load32 m (0x15a58#32)=(0#32)
  shotgun2Tics : load32 m (0x15d94#32)=(3#32)
  shotgun2Action : load32 m (0x15d98#32)=(0x2db60#32)
  shotgun2Next : load32 m (0x15d9c#32)=(1#32)
  shotgun2Misc : load32 m (0x15da0#32)=(0#32)
  pistolNext : load32 m (0x15c14#32)=(1#32)
  shotgun1Next : load32 m (0x15d80#32)=(31#32)

/-- Expiration includes the real state setter, light action, and setter RET. -/
theorem slot_summary (s : X86Memory.State) (p : Word) (v : Weapon.State)
    (h : E1M1FlashUpdate.Inputs s p v) (supported : WeaponFlash.Supported v)
    (nonempty : v.flash.frame≠0) (expires : v.flash.tics.toBitVec=(1#32))
    (tables : Tables s.memory) (sep : Separated p (s.regs 4)) :
    ∃ t, E1M1PspriteLight.slot 2 s=some t ∧ t.pc=0x2dc95 ∧
      t.core.regs 7=p ∧ t.core.regs 6=(1#32) ∧
      (load32 t.core.memory (p+260),load32 t.core.memory (p+264),load32 t.core.memory (p+232),
       load32 t.core.memory (p+252),load32 t.core.memory (p+256))=WeaponFlash.expected v := by
  rcases supported with frame|frame|frame|frame
  · exact False.elim (nonempty frame)
  all_goals
    have hs := h.state
    have ht := h.timer
    have hx := h.x
    have hy := h.y
    simp only [frame, WeaponFlash.pointer, ↓reduceIte] at hs
    rw [expires] at ht
    simp only [BitVec.ofNat_eq_ofNat, ←location_0 p (s.regs 4), ←location_1 p (s.regs 4),
      ←location_2 p (s.regs 4), ←location_3 p (s.regs 4), ←location_4 p (s.regs 4), ←location_5 p (s.regs 4),
      ←location_6 p (s.regs 4), ←location_7 p (s.regs 4), ←location_8 p (s.regs 4), ←location_9 p (s.regs 4),
      ←location_10 p (s.regs 4), ←location_11 p (s.regs 4), ←location_12 p (s.regs 4),
      ←location_13 p (s.regs 4), ←location_14 p (s.regs 4), ←location_15 p (s.regs 4),
      ←location_16 p (s.regs 4), ←location_17 p (s.regs 4), ←location_18 p (s.regs 4)]
      at hs ht hx hy
    have t9 := tables.lightDoneTics
    have t10 := tables.lightDoneAction
    have t11 := tables.lightDoneNext
    have t12 := tables.lightDoneMisc
    have t13 := tables.shotgun2Tics
    have t14 := tables.shotgun2Action
    have t15 := tables.shotgun2Next
    have t16 := tables.shotgun2Misc
    have t17 := tables.pistolNext
    have t18 := tables.shotgun1Next
    simp only [←location_9 p (s.regs 4), ←location_10 p (s.regs 4), ←location_11 p (s.regs 4),
      ←location_12 p (s.regs 4), ←location_13 p (s.regs 4), ←location_14 p (s.regs 4),
      ←location_15 p (s.regs 4), ←location_16 p (s.regs 4), ←location_17 p (s.regs 4),
      ←location_18 p (s.regs 4)] at t9 t10 t11 t12 t13 t14 t15 t16 t17 t18
    simp [E1M1PspriteLight.slot, E1M1PspriteLight.complete, E1M1PspriteLight.chain, PspriteChainDriver.chain,
      E1M1PspriteLight.advance, E1M1PspriteLight.index, E1M1PspriteChain.NoAction,
      E1M1PspriteSetter.dispatched, E1M1PspriteSetter.positioned, E1M1PspriteSetter.resumed,
      PspriteSetter.entered, PspriteSetter.prepared, PspriteSetter.installed, PspriteSetter.store,
      PspriteSetter.called, PspriteSetter.actionGate, PspriteSetter.successor, PspriteSetter.next,
      PspriteSetter.returned, PspriteSetter.cleared, PspriteSetter.afterAction, PspriteLight.result,
      PspriteLight.written, PspriteStep.result, PspriteStep.dispatch, PspriteStep.decremented,
      PspriteStep.counting, PspriteStep.stateWord, PspriteStep.tics, PspriteLoop.popped, X86Routine.pushWord,
      put, write, WeaponFlash.expected, WeaponFlash.pointer, frame, expires, h.slot, h.player, h.index,
      BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.ofNat_eq_ofNat, ←location_0 p (s.regs 4),
      ←location_1 p (s.regs 4), ←location_2 p (s.regs 4), ←location_3 p (s.regs 4), ←location_4 p (s.regs 4),
      ←location_5 p (s.regs 4), ←location_6 p (s.regs 4), ←location_7 p (s.regs 4), ←location_8 p (s.regs 4),
      ←location_9 p (s.regs 4), ←location_10 p (s.regs 4), ←location_11 p (s.regs 4),
      ←location_12 p (s.regs 4), ←location_13 p (s.regs 4), ←location_14 p (s.regs 4),
      ←location_15 p (s.regs 4), ←location_16 p (s.regs 4), ←location_17 p (s.regs 4),
      ←location_18 p (s.regs 4), read_store p (s.regs 4) sep, hs, ht, hx, hy, t9, t10, t11, t12, t13, t14,
      t15, t16, t17, t18]

/-- The expiry proof now starts with field/table/separation contracts and ends
with the production helper's observation, including the original outer RET. -/
theorem expired_correspondence (s : X86Memory.State) (f : Option Flags) (p : Word) (v : Weapon.State)
    (h : E1M1FlashUpdate.Inputs s p v) (supported : WeaponFlash.Supported v)
    (nonempty : v.flash.frame≠0) (expires : v.flash.tics.toBitVec=(1#32))
    (tables : Tables s.memory) (sep : Separated p (s.regs 4)) :
    ∃ n t, n ≤ 106 ∧ X86CodeMemory.Prefix FloorCaller.cm E1M1PspriteLight.program [] n ⟨s,f,0x2dc6f⟩ t ∧
      E1M1FlashUpdate.observe t.core.memory p=WeaponFlash.observe (Weapon.tickFlash v) := by
  obtain ⟨t,ok,pc,player,index,reads⟩ := slot_summary s p v h supported nonempty expires tables sep
  obtain ⟨n,hn,a⟩ := E1M1PspriteLight.slot_execution 2 s f t ok
  obtain ⟨m,hm,b⟩ := E1M1PspriteLight.finish_execution t pc index
  refine ⟨n+m,E1M1PspriteLight.finished t,by omega,E1M1PspriteStep.prefix_trans a b,?_⟩
  rw [E1M1FlashUpdate.finish_observation _ p player,WeaponFlash.live_expected v supported]
  exact reads

/-- All timer cases, not just non-expiring slots. Table/separation contracts
are only needed when this particular input actually expires. -/
theorem live_correspondence (s : X86Memory.State) (f : Option Flags) (p : Word) (v : Weapon.State)
    (h : E1M1FlashUpdate.Inputs s p v) (supported : WeaponFlash.Supported v)
    (expiry : ¬ E1M1FlashUpdate.NoTransition v → Tables s.memory ∧ Separated p (s.regs 4)) :
    ∃ n t, n ≤ 106 ∧ X86CodeMemory.Prefix FloorCaller.cm E1M1PspriteLight.program [] n ⟨s,f,0x2dc6f⟩ t ∧
      E1M1FlashUpdate.observe t.core.memory p=WeaponFlash.observe (Weapon.tickFlash v) := by
  by_cases quiet : E1M1FlashUpdate.NoTransition v
  · obtain ⟨n,t,bound,run,obs⟩ := E1M1FlashUpdate.live_correspondence s f p v h supported quiet
    exact ⟨n,t,by omega,run,obs⟩
  · have active : v.flash.frame≠0 := fun empty => quiet (Or.inl empty)
    have zero : v.flash.tics.toBitVec-(1#32)=(0#32) := by
      by_cases z : v.flash.tics.toBitVec-(1#32)=(0#32)
      · exact z
      · exact False.elim (quiet (Or.inr (Or.inr z)))
    have expires : v.flash.tics.toBitVec=(1#32) := by
      calc v.flash.tics.toBitVec = v.flash.tics.toBitVec-(1#32)+(1#32) := (BitVec.sub_add_cancel _ _).symm
           _ = (1#32) := by rw [zero]; rfl
    exact expired_correspondence s f p v h supported active expires (expiry quiet).1 (expiry quiet).2

/-- The isolated flash phase stays inside the supported state set. Weapon actions
that create a flash still need their own invariant when the whole tic is joined. -/
theorem supported_after (v : Weapon.State) (supported : WeaponFlash.Supported v) :
    WeaponFlash.Supported (Weapon.tickFlash v) := by
  rcases supported with frame|frame|frame|frame <;>
    by_cases forever : v.flash.tics=(-1 : Int32) <;>
    by_cases expires : v.flash.tics-1=(0 : Int32) <;>
    simp [WeaponFlash.Supported, Weapon.tickFlash, frame, forever, expires, WeaponData.frames,
      WeaponData.LIGHTDONE]

end Doom.Proofs.E1M1FlashExpiry
