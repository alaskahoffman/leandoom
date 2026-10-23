import Doom.Proofs.E1M1PspriteLight
import Doom.Proofs.WeaponFlash
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 800000
namespace Doom.Proofs.E1M1FlashUpdate
open Verification X86 X86Memory X86Control BlockSummary

/-- At the flash-slot entry, after the weapon phase has already run. -/
structure Inputs (s : X86Memory.State) (p : Word) (v : Weapon.State) : Prop where
  slot : s.regs 1=p+(260#32)
  player : s.regs 7=p
  index : s.regs 6=1
  state : load32 s.memory (p+(260#32))=WeaponFlash.pointer v.flash.frame
  timer : load32 s.memory (p+(264#32))=v.flash.tics.toBitVec
  light : load32 s.memory (p+(232#32))=v.extraLight.toBitVec
  x : load32 s.memory (p+(252#32))=v.weapon.x.raw.toBitVec
  y : load32 s.memory (p+(256#32))=v.weapon.y.raw.toBitVec

def observe (m : Memory) (p : Word) : Word × Word × Word × Word × Word :=
  (load32 m (p+(260#32)),load32 m (p+(264#32)),load32 m (p+(232#32)),load32 m (p+(268#32)),load32 m (p+(272#32)))
def NoTransition (v : Weapon.State) : Prop :=
  v.flash.frame=0 ∨ v.flash.tics.toBitVec=(0xffffffff#32) ∨ v.flash.tics.toBitVec-(1#32)≠(0#32)

def counted (m : Memory) (p : Word) (v : Weapon.State) : Memory :=
  if v.flash.frame=0 ∨ v.flash.tics.toBitVec=(0xffffffff#32) then m
  else store32 m (p+(264#32)) (v.flash.tics.toBitVec-(1#32))

private theorem apart (p : Word) (a b : Fin 64) (gap : a.val+4 ≤ b.val ∨ b.val+4 ≤ a.val) :
    Apart (p+(232#32)+BitVec.ofNat 32 a.val) (p+(232#32)+BitVec.ofNat 32 b.val) :=
  PlayerHealth.offsets_apart (p+(232#32)) ⟨a.val,by omega⟩ ⟨b.val,by omega⟩ gap

private theorem ptr (v : Weapon.State) (h : WeaponFlash.Supported v) :
    WeaponFlash.pointer v.flash.frame=(0#32) ↔ v.flash.frame=0 := by
  rcases h with h|h|h|h <;> simp [WeaponFlash.pointer,h]

theorem slot_summary (s : X86Memory.State) (p : Word) (v : Weapon.State)
    (h : Inputs s p v) (supported : WeaponFlash.Supported v) (quiet : NoTransition v) :
    (PspriteStep.result s).pc=0x2dc95 ∧
    (PspriteStep.result s).core.regs 7=p ∧ (PspriteStep.result s).core.regs 6=1 ∧
    (PspriteStep.result s).core.memory=counted s.memory p v := by
  have state : PspriteStep.stateWord s=WeaponFlash.pointer v.flash.frame := by simpa [PspriteStep.stateWord,h.slot] using h.state
  have timer : PspriteStep.tics s=v.flash.tics.toBitVec := by simpa [PspriteStep.tics,h.slot,BitVec.add_assoc] using h.timer
  have ptr := ptr v supported
  unfold PspriteStep.result
  rw [state,timer]
  simp only [BitVec.ofNat_eq_ofNat,ptr]
  rcases quiet with empty|forever|running
  · simp [empty,counted,put,write,h.player,h.index]
  · by_cases empty : v.flash.frame=0 <;>
      simp [empty,forever,counted,PspriteStep.counting,put,write,h.player,h.index]
  · by_cases empty : v.flash.frame=0 <;> by_cases forever : v.flash.tics.toBitVec=(0xffffffff#32) <;>
      simp [empty,forever,running,counted,PspriteStep.counting,PspriteStep.decremented,put,write,
        h.player,h.index,h.slot,timer,BitVec.add_assoc,BitVec.ofNat_eq_ofNat]

/-- Every observed player field is disjoint from the timer word by construction,
including unaligned and wrapping player addresses. No stack contract is needed
on this path: the stack is only read, not written. -/
theorem counted_reads (s : X86Memory.State) (p : Word) (v : Weapon.State) (h : Inputs s p v) :
    load32 (counted s.memory p v) (p+(260#32))=WeaponFlash.pointer v.flash.frame ∧
    load32 (counted s.memory p v) (p+(264#32))=
      (if v.flash.frame=0 ∨ v.flash.tics.toBitVec=(0xffffffff#32) then v.flash.tics.toBitVec else v.flash.tics.toBitVec-(1#32)) ∧
    load32 (counted s.memory p v) (p+(232#32))=v.extraLight.toBitVec ∧
    load32 (counted s.memory p v) (p+(252#32))=v.weapon.x.raw.toBitVec ∧
    load32 (counted s.memory p v) (p+(256#32))=v.weapon.y.raw.toBitVec := by
  have a : Apart (p+(260#32)) (p+(264#32)) := by
    have q := apart p 28 32 (by decide)
    change Apart (p+(232#32)+(28#32)) (p+(232#32)+(32#32)) at q
    simpa [BitVec.add_assoc] using q
  have b : Apart (p+(232#32)) (p+(264#32)) := by
    have q := apart p 0 32 (by decide)
    change Apart (p+(232#32)+(0#32)) (p+(232#32)+(32#32)) at q
    simpa [BitVec.add_assoc] using q
  have c : Apart (p+(252#32)) (p+(264#32)) := by
    have q := apart p 20 32 (by decide)
    change Apart (p+(232#32)+(20#32)) (p+(232#32)+(32#32)) at q
    simpa [BitVec.add_assoc] using q
  have d : Apart (p+(256#32)) (p+(264#32)) := by
    have q := apart p 24 32 (by decide)
    change Apart (p+(232#32)+(24#32)) (p+(232#32)+(32#32)) at q
    simpa [BitVec.add_assoc] using q
  unfold counted
  split <;> simp [*,h.state,h.timer,h.light,h.x,h.y,load_store,load_store_apart]


theorem copied_reads (s : X86Memory.State) (p : Word) (player : s.regs 7=p) :
    observe (PspriteLoop.copied s).memory p=
      (load32 s.memory (p+(260#32)),load32 s.memory (p+(264#32)),load32 s.memory (p+(232#32)),
       load32 s.memory (p+(252#32)),load32 s.memory (p+(256#32))) := by
  have h260_268 : Apart (p+(260#32)) (p+(268#32)) := by
    have q := apart p 28 36 (by decide)
    change Apart (p+(232#32)+(28#32)) (p+(232#32)+(36#32)) at q
    simpa [BitVec.add_assoc] using q
  have h260_272 : Apart (p+(260#32)) (p+(272#32)) := by
    have q := apart p 28 40 (by decide)
    change Apart (p+(232#32)+(28#32)) (p+(232#32)+(40#32)) at q
    simpa [BitVec.add_assoc] using q
  have h264_268 : Apart (p+(264#32)) (p+(268#32)) := by
    have q := apart p 32 36 (by decide)
    change Apart (p+(232#32)+(32#32)) (p+(232#32)+(36#32)) at q
    simpa [BitVec.add_assoc] using q
  have h264_272 : Apart (p+(264#32)) (p+(272#32)) := by
    have q := apart p 32 40 (by decide)
    change Apart (p+(232#32)+(32#32)) (p+(232#32)+(40#32)) at q
    simpa [BitVec.add_assoc] using q
  have h232_268 : Apart (p+(232#32)) (p+(268#32)) := by
    have q := apart p 0 36 (by decide)
    change Apart (p+(232#32)+(0#32)) (p+(232#32)+(36#32)) at q
    simpa [BitVec.add_assoc] using q
  have h232_272 : Apart (p+(232#32)) (p+(272#32)) := by
    have q := apart p 0 40 (by decide)
    change Apart (p+(232#32)+(0#32)) (p+(232#32)+(40#32)) at q
    simpa [BitVec.add_assoc] using q
  have h256_268 : Apart (p+(256#32)) (p+(268#32)) := by
    have q := apart p 24 36 (by decide)
    change Apart (p+(232#32)+(24#32)) (p+(232#32)+(36#32)) at q
    simpa [BitVec.add_assoc] using q
  have h256_272 : Apart (p+(256#32)) (p+(272#32)) := by
    have q := apart p 24 40 (by decide)
    change Apart (p+(232#32)+(24#32)) (p+(232#32)+(40#32)) at q
    simpa [BitVec.add_assoc] using q
  have h268_272 : Apart (p+(268#32)) (p+(272#32)) := by
    have q := apart p 36 40 (by decide)
    change Apart (p+(232#32)+(36#32)) (p+(232#32)+(40#32)) at q
    simpa [BitVec.add_assoc] using q
  simp [observe,PspriteLoop.copied,PspriteLoop.copyX,put,write,
    load_store,load_store_apart,BitVec.ofNat_eq_ofNat, *]

theorem finish_observation (s : X86Control.State) (p : Word) (player : s.core.regs 7=p) :
    observe (E1M1PspriteLight.finished s).core.memory p=
      (load32 s.core.memory (p+(260#32)),load32 s.core.memory (p+(264#32)),load32 s.core.memory (p+(232#32)),
       load32 s.core.memory (p+(252#32)),load32 s.core.memory (p+(256#32))) := by
  change observe (PspriteLoop.returned (PspriteLoop.copied (PspriteLoop.advanced s.core).core) (PspriteLoop.advanced s.core).flags).core.memory p=_
  rw [(PspriteLoop.return_stack _ _).2.2.1]
  rw [copied_reads _ p (by simpa [PspriteLoop.advanced,put,write] using player)]
  rfl

/-- Direct binary-to-live correspondence for empty, permanent and non-expiring
flash slots. All 32-bit timer/light/coordinate values and player addresses are
covered. The result includes the actual original coordinate copy and RET. -/
theorem live_correspondence (s : X86Memory.State) (f : Option Flags) (p : Word) (v : Weapon.State)
    (h : Inputs s p v) (supported : WeaponFlash.Supported v) (quiet : NoTransition v) :
    ∃ n t, n ≤ 29 ∧ X86CodeMemory.Prefix FloorCaller.cm E1M1PspriteLight.program [] n ⟨s,f,0x2dc6f⟩ t ∧
      observe t.core.memory p=WeaponFlash.observe (Weapon.tickFlash v) := by
  have summary := slot_summary s p v h supported quiet
  obtain ⟨n,hn,a,_⟩ := X86Routine.run_path (PspriteStep.slot_execution s f)
  have a := (X86CodeMemory.lift_success a FloorCaller.cm).transfer E1M1PspriteLight.program [] E1M1PspriteLight.contains_slot (by simp)
  obtain ⟨m,hm,b⟩ := E1M1PspriteLight.finish_execution (PspriteStep.result s) summary.1 summary.2.2.1
  refine ⟨n+m,E1M1PspriteLight.finished (PspriteStep.result s),by omega,E1M1PspriteStep.prefix_trans a b,?_⟩
  rw [finish_observation _ p summary.2.1,summary.2.2.2]
  have reads := counted_reads s p v h
  rw [reads.1,reads.2.1,reads.2.2.1,reads.2.2.2.1,reads.2.2.2.2]
  rw [WeaponFlash.live_expected v supported]
  unfold WeaponFlash.expected
  rcases quiet with empty|forever|running
  · simp [empty]
  · simp [forever,BitVec.ofNat_eq_ofNat]
  · by_cases frozen : v.flash.frame=0 ∨ v.flash.tics.toBitVec=(0xffffffff#32) <;>
      simp [frozen,running,BitVec.ofNat_eq_ofNat]

end Doom.Proofs.E1M1FlashUpdate
