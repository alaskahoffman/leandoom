import Doom.Proofs.E1M1WeaponReady
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 32768
set_option maxHeartbeats 2000000
open Doom Doom.Proofs Doom.Verification X86 X86Memory X86Control BlockSummary
namespace WeaponReadyChecks

def p : Word := 0x600101
def slot : Word := p+244
def amp : Fixed := ⟨65537⟩
def table : Word := 0x15a28+28*10
-- A ready pistol state with a nonzero timer, and the two selected trig entries.
def memory : Memory :=
  store32 (store32 (store32 (store32 (store32 (store32 (store32 (fun _ => 0)
    0x13584 0x7a84) 0x7a84 (WeaponReady.aim 0).fineCosine.raw.toBitVec)
    0x5a84 (WeaponReady.halfAim 0).fineSine.raw.toBitVec)
    (p+28) amp.raw.toBitVec) slot table) (slot+4) 1) (table+16) 10
-- Stack from entering A_WeaponReady through a setter called by A_Raise,
-- itself called by the outer weapon-slot setter.
def stacked (sp : Word) : Memory :=
  let m := store32 (store32 (store32 (store32 memory sp p) (sp+4) p) (sp+8) table) (sp+12) slot
  let m := store32 (store32 (store32 (store32 m (sp+16) 0x2d095) (sp+20) p) (sp+24) 10) (sp+28) 0x2d50d
  let m := store32 (store32 (store32 m (sp+32) (table+56)) (sp+36) slot) (sp+40) 0x2d095
  store32 (store32 (store32 m (sp+44) 0) (sp+48) slot) (sp+52) 0x2dc95

def initial (sp : Word) : X86Memory.State :=
  ⟨write (write (write (fun _ => 0) 1 p) 7 slot) 4 sp,stacked sp⟩

@[local simp] theorem loc0 : WeaponReady.location (initial 5) 0=(6291901#32) := by decide
@[local simp] theorem loc1 : WeaponReady.location (initial 5) 1=(6291965#32) := by decide
@[local simp] theorem loc2 : WeaponReady.location (initial 5) 2=(6291969#32) := by decide
@[local simp] theorem loc3 : WeaponReady.location (initial 5) 3=(184192#32) := by decide
@[local simp] theorem loc4 : WeaponReady.location (initial 5) 4=(79236#32) := by decide
@[local simp] theorem loc5 : WeaponReady.location (initial 5) 5=(31364#32) := by decide
@[local simp] theorem loc6 : WeaponReady.location (initial 5) 6=(23172#32) := by decide
@[local simp] theorem loc7 : WeaponReady.location (initial 5) 7=(6291741#32) := by decide
@[local simp] theorem loc8 : WeaponReady.location (initial 5) 8=(21#32) := by decide
theorem inputs : WeaponReady.Inputs (initial 5) amp 0 := by
  have zero (a : Word) : load32 (fun _ => (0#8)) a=(0#32) := by simp [load32]
  constructor
  · simp only [loc0,loc1,loc2,loc3,loc4,loc5,loc6,loc7,loc8]
    simp (disch := unfold Apart; decide) [initial,stacked,memory,p,slot,table,
      load_store,load_store_apart,zero]
  · simp only [loc0,loc1,loc2,loc3,loc4,loc5,loc6,loc7,loc8]
    simp (disch := unfold Apart; decide) [initial,stacked,memory,p,slot,table,
      load_store,load_store_apart,zero]
  · simp only [loc0,loc1,loc2,loc3,loc4,loc5,loc6,loc7,loc8]
    simp (disch := unfold Apart; decide) [initial,stacked,memory,p,slot,table,
      load_store,load_store_apart,zero]
  · simp only [loc0,loc1,loc2,loc3,loc4,loc5,loc6,loc7,loc8]
    simp (disch := unfold Apart; decide) [initial,stacked,memory,p,slot,table,
      load_store,load_store_apart,zero]
  · simp only [loc0,loc1,loc2,loc3,loc4,loc5,loc6,loc7,loc8]
    simp (disch := unfold Apart; decide) [initial,stacked,memory,p,slot,table,
      load_store,load_store_apart,zero]
  · intro i j ne
    have ci : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 ∨ i=7 ∨ i=8 := by omega
    have cj : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 := by omega
    rcases ci with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
      rcases cj with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
      (first | exact False.elim (ne rfl) | simp only [loc0,loc1,loc2,loc3,loc4,loc5,loc6,loc7,loc8]; unfold Apart; decide)
example : ¬ WeaponReady.Inputs (initial (p+172)) amp 0 := by
  intro h
  exact h.separate 0 8 (by decide) 0 0 (by decide)
example : (Weapon.readyIdle {} amp 0).attackDown=false := rfl

macro "check_stack" : tactic => `(tactic| (
  simp (disch := unfold Apart; decide) [E1M1WeaponReady.raisedIdleReturn,E1M1WeaponReady.finishSetter,
    E1M1PspriteSetter.resumed,PspriteSetter.afterAction,PspriteSetter.successor,PspriteSetter.next,
    PspriteSetter.returned,WeaponRaise.returned,WeaponReady.result,WeaponReady.returned,
    WeaponReady.bobbed,WeaponReady.horizontal,WeaponReady.cleared,PspriteLoop.popped,
    initial,stacked,memory,p,slot,table,put,write,BitVec.add_assoc,load_store,load_store_apart]))

def final := (E1M1WeaponReady.raisedIdleReturn (initial 5)).getD ⟨initial 5,none,0⟩
example : E1M1WeaponReady.raisedIdleReturn (initial 5)=some final := by
  unfold final
  check_stack
example : final.pc=0x2dc95 ∧ final.core.regs 4=61 := by
  unfold final
  check_stack
example : ∃ n, n ≤ 52 ∧ X86CodeMemory.Prefix FloorCaller.cm E1M1WeaponReady.program [] n
    ⟨initial 5,none,0x2d392⟩ final :=
  E1M1WeaponReady.raised_idle_return_execution _ _ _ (by unfold final; check_stack)

-- A wrong callback return is rejected, rather than assuming the setter ran.
example : E1M1WeaponReady.raisedIdleReturn
    {initial 5 with memory := store32 (stacked 5) 21 0x2d096}=none := by check_stack

end WeaponReadyChecks
