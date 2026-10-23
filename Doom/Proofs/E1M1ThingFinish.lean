import Doom.Proofs.E1M1ThingReturn
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1800000
namespace Doom.Proofs.E1M1ThingFinish
open Verification X86 X86Memory X86Control BlockSummary
open E1M1ScanGeometry (path)
open E1M1ScanContracts (LineData)
open OriginalLineMixedInvariant (ArraySafe)
open OriginalThingSecondSide (firstSide lastSide)

def AllLines (r : Collision.PathResult) : Prop := ∀ hit∈r.collected, hit.isLine=true

theorem step_lines (c : OriginalLineMixedInvariant.Candidate) (s : X86Memory.State)
    (r : Collision.PathResult) (h : AllLines r) : AllLines (OriginalLineMixedInvariant.step c s r).2 := by
  have push : AllLines {r with collected:=r.collected.push c.hit} := by
    intro hit mem
    simp only [Array.mem_push] at mem
    rcases mem with mem|rfl
    · exact h hit mem
    · rfl
  unfold OriginalLineMixedInvariant.step
  split
  · exact h
  · split
    · split
      · exact h
      · split
        · exact h
        · exact push
    · exact h

theorem run_lines (candidates : Nat → OriginalLineMixedInvariant.Candidate) (k i : Nat)
    (s : X86Control.State) (r : Collision.PathResult) (h : AllLines r) :
    AllLines (OriginalLineMixedInvariant.run candidates k i s r).2 := by
  induction k generalizing i s r with
  | zero => exact h
  | succ k ih => exact ih (i+1) _ _ (step_lines _ _ r h)

theorem finished_lines (initial : X86Memory.State) (n : Nat) (base : Word)
    (resolve : Collision.Intercept → Word) (h : OriginalLineMixedInvariant.Initial initial n base resolve)
    (f : Option Flags) (trace : Collision.Divline) :
    AllLines (OriginalLineMixedInvariant.finished initial n base resolve h f {trace:=trace}).2 := by
  exact run_lines h.candidates n 0 ⟨initial,f,0x2c57f⟩ {trace:=trace} (by intro hit mem; simpa using mem)

def resolve (lines : Word) (objects : Nat → Word) (hit : Collision.Intercept) : Word :=
  if hit.isLine then E1M1PathMap.resolve lines hit else objects hit.id

theorem relabel (s : X86Memory.State) (base lines : Word) (objects : Nat → Word)
    (r : Collision.PathResult) (h : AllLines r)
    (tracked : OriginalLineCollection.Tracks s base (E1M1PathMap.resolve lines) r.collected 0) :
    OriginalLineCollection.Tracks s base (resolve lines objects) r.collected 0 := by
  refine ⟨?_,tracked.cursor,tracked.room⟩
  intro i hi
  have kind := h r.collected[i] (Array.getElem_mem hi)
  simpa only [resolve,kind,if_true] using tracked.encoded i hi

/-- The existing 128 twelve-byte slots end before the cursor global. -/
theorem metadata (i : Nat) (hi : i<128) (off : Word) (ho : off∈[(0#32),4,8]) :
    Apart (OriginalLineCollection.slot 0x2ba20 i off) (0x2c028#32) := by
  intro x y eq
  have value (k off : Nat) (hk : k<128) (ho : off≤8) (z : Fin 4) :
      (OriginalLineCollection.slot (0x2ba20 : Word) k (BitVec.ofNat 32 off)+BitVec.ofNat 32 z.val).toNat=178720+12*k+off+z.val := by
    change (BitVec.ofNat 32 178720+BitVec.ofNat 32 (12*k)+BitVec.ofNat 32 off+BitVec.ofNat 32 z.val).toNat=_
    rw [←BitVec.ofNat_add,←BitVec.ofNat_add,←BitVec.ofNat_add,BitVec.toNat_ofNat,Nat.mod_eq_of_lt]
    have hz := z.isLt
    omega
  have right : ((0x2c028#32)+BitVec.ofNat 32 y.val).toNat=180264+y.val := by
    change (BitVec.ofNat 32 180264+BitVec.ofNat 32 y.val).toNat=_
    rw [←BitVec.ofNat_add,BitVec.toNat_ofNat,Nat.mod_eq_of_lt]
    have hy := y.isLt
    omega
  have num := congrArg BitVec.toNat eq
  rw [right] at num
  simp only [List.mem_cons,List.not_mem_nil,or_false] at ho
  rcases ho with rfl|rfl|rfl
  · rw [value i 0 hi (by decide) x] at num
    have hx := x.isLt
    omega
  · change (OriginalLineCollection.slot (0x2ba20 : Word) i (BitVec.ofNat 32 4)+BitVec.ofNat 32 x.val).toNat=_ at num
    rw [value i 4 hi (by decide) x] at num
    have hx := x.isLt
    omega
  · change (OriginalLineCollection.slot (0x2ba20 : Word) i (BitVec.ofNat 32 8)+BitVec.ofNat 32 x.val).toNat=_ at num
    rw [value i 8 hi (by decide) x] at num
    have hx := x.isLt
    omega

/-- This is the object-loop fragment using the two actual production functions. -/
def collect (trace : Collision.Divline) (target : Collision.SolidThing) (id : Nat) (r : Collision.PathResult) : Except String Collision.PathResult := do
  let hit ← Collision.thingIntercept trace target
  match hit with
  | none => pure r
  | some frac => Collision.appendIntercept r ⟨frac,false,id⟩

theorem finish_collect (s : X86Control.State) (trace : Collision.Divline) (target : Collision.SolidThing)
    (id : Nat) (r : Collision.PathResult) (resolve : Collision.Intercept → Word) (object : Word)
    (h : E1M1ThingFraction.Outcome s trace target)
    (arg : s.core.regs 1=object) (pointer : ∀ frac, resolve ⟨frac,false,id⟩=object)
    (tracked : OriginalLineCollection.Tracks s.core 0x2ba20 resolve r.collected 0)
    (capacity : r.collected.size<128) :
    ∃ next, collect trace target id r=.ok next ∧
      OriginalLineCollection.Tracks (OriginalThingFinish.result s).core 0x2ba20 resolve next.collected 0 := by
  obtain ⟨hit,computed,pc,value⟩ := h
  cases hit with
  | none =>
    change s.pc=(if firstSide trace target=lastSide trace target then 0x2c805 else 0x2c7da) at pc
    have noInsert : s.pc≠0x2c7e4 := by rw [pc]; split <;> decide
    have memory := OriginalThingFinish.result_memory s
    rw [if_neg noInsert] at memory
    refine ⟨r,by unfold collect; rw [computed]; rfl,?_,?_,tracked.room⟩
    · simpa only [memory] using tracked.encoded
    · simpa only [OriginalLineFinish.cursor,memory] using tracked.cursor
  | some frac =>
    have app := OriginalThingFinish.append_tracks s 0x2ba20 resolve r frac id pc tracked capacity value
      (arg.trans (pointer frac).symm) metadata
    exact ⟨{r with collected:=r.collected.push ⟨frac,false,id⟩},by unfold collect; rw [computed]; exact app.1,app.2⟩

set_option backward.isDefEq.respectTransparency true
attribute [local irreducible] Collision.SolidThing.attackEndpoint
section Firing
variable (gun : Fire.Gun) (s : X86Memory.State) (weapon : Weapon.Context)
    (actor : Word) (thing : Collision.SolidThing) (angle : Angle) (ox oy : Fixed)
    (xout yout : Int32 × Fixed × Fixed) (base lines : Word) (words : Array Nat)
    (c : E1M1PathMap.Cell) (w h : Nat) (data : Nat → LineData)
    (input : E1M1FiringScan.Inputs gun s weapon actor thing angle ox oy xout yout base lines words c w h data)
include input

def result := E1M1ThingReturn.resumed (E1M1ThingCallback.result gun s weapon actor thing angle ox oy xout yout base lines words c w h data input).core

variable (returns : E1M1ScanReturn.ReturnSafe (s.regs 4) lines)
    (flag : E1M1ThingGate.FlagSafe (s.regs 4) lines)
    (links object : Word)
    (lookupSafe : ∀ a∈E1M1ThingEntry.reads thing angle ox oy w links, E1M1ThingEntry.ReadSafe gun s lines a)
    (global : load32 s.memory (0x2c0f8#32)=links)
    (selected : load32 s.memory (links+(BitVec.ofNat 32 (Collision.pathCellIndex
      (path thing angle ox oy).startBlockX (path thing angle ox oy).startBlockY w) <<< 2))=object)
    (present : object≠(0#32))
    (stack : E1M1ThingCallback.StackSafe (s.regs 4-(120#32)) 0x2ba20)
include returns flag lookupSafe global selected present stack


attribute [local irreducible] load32 OriginalDivlineSide.result OriginalThingSecondSide.result OriginalThingFraction.result
set_option maxHeartbeats 200000 in
theorem firing_finish (target : Collision.SolidThing) (d : E1M1ThingGeometry.Data gun s lines object target)
    (sideStack : E1M1ThingFirstSide.StackSafe (s.regs 4-(172#32)) 0x2ba20)
    (secondStack : E1M1ThingCrossing.StackSafe (s.regs 4-(172#32)) 0x2ba20)
    (traceScratch : ∀ a∈E1M1ThingGeometry.traceReads, Apart a (s.regs 4-(172#32)+(16#32)))
    (fractionStack : E1M1ThingFraction.StackSafe (s.regs 4-(172#32)) 0x2ba20)
    (traceSafe : ∀ a∈OriginalThingFraction.traceReads, OriginalThingFraction.Safe (s.regs 4-(172#32)) a)
    (computed : firstSide (path thing angle ox oy).trace target≠lastSide (path thing angle ox oy).trace target →
      ∃ frac, Collision.interceptVector (path thing angle ox oy).trace (OriginalThingFraction.diagonal (path thing angle ox oy).trace target)=.ok frac)
    (id : Nat) (objects : Nat → Word) (objectId : objects id=object)
    (capacity : (E1M1ScanReturn.finished gun s weapon actor thing angle ox oy xout yout base lines words c w h data input).2.collected.size<128)
    (returnStack : ∀ off∈[(36#32),48], ArraySafe 0x2ba20 (s.regs 4-(172#32)+off))
    (f : Option Flags) :
    let out := result gun s weapon actor thing angle ox oy xout yout base lines words c w h data input
    let before := (E1M1ScanReturn.finished gun s weapon actor thing angle ox oy xout yout base lines words c w h data input).2
    (∃ steps≤633+281*c.ids.length, X86CodeMemory.Prefix FloorCaller.cm E1M1ThingReturn.program [] steps
      ⟨s,f,OriginalWeaponDischarge.afterSound gun⟩ out) ∧
    out.core.regs 4=s.regs 4-(120#32) ∧
    out.core.regs 2=load32 out.core.memory (object+(44#32)) ∧
    out.pc=(if out.core.regs 2=(0#32) then 0x2c5e2 else 0x2c5d2) ∧
    (∃ next, collect (path thing angle ox oy).trace target id before=.ok next ∧
      OriginalLineCollection.Tracks out.core 0x2ba20 (resolve lines objects) next.collected 0) := by
  let entry := E1M1ThingCallback.result gun s weapon actor thing angle ox oy xout yout base lines words c w h data input
  let before := (E1M1ScanReturn.finished gun s weapon actor thing angle ox oy xout yout base lines words c w h data input).2
  have started := E1M1ThingCallback.firing_enter gun s weapon actor thing angle ox oy xout yout base lines words c w h data input returns flag links object lookupSafe global selected present stack f
  have sp : entry.core.regs 4=s.regs 4-(172#32) := started.2.2.2.2.1
  obtain ⟨⟨n,hn,prior⟩,outcome,tracked⟩ := E1M1ThingFraction.firing_fraction gun s weapon actor thing angle ox oy xout yout base lines words c w h data input returns flag links object lookupSafe global selected present stack target d sideStack secondStack traceScratch fractionStack traceSafe computed f
  have cursor : OriginalThingFinish.cursor (E1M1ThingReturn.view entry.core).core=0x2ba20+BitVec.ofNat 32 (12*before.collected.size) := tracked.cursor
  have safe : E1M1ThingReturn.ReturnSafe entry.core := by
    intro off ho w hw
    rw [cursor] at hw
    rw [sp]
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hw
    rcases hw with rfl|rfl|rfl|rfl
    · simpa only [OriginalLineCollection.slot,BitVec.add_zero] using (returnStack off ho).1 before.collected.size capacity (0#32) (by simp)
    · exact (returnStack off ho).1 before.collected.size capacity (4#32) (by simp)
    · exact (returnStack off ho).1 before.collected.size capacity (8#32) (by simp)
    · exact (returnStack off ho).2
  have ret : load32 entry.core.memory (entry.core.regs 4+(48#32))=(0x2c5d7#32) := by
    rw [sp]
    have eq : s.regs 4-(172#32)+(48#32)=s.regs 4-(124#32) := by simp [BitVec.sub_eq_add_neg,BitVec.add_assoc]
    rw [eq]
    exact started.2.2.2.2.2.2.1
  have savedObject : load32 entry.core.memory (entry.core.regs 4+(36#32))=object := by
    rw [sp]
    have eq : s.regs 4-(172#32)+(36#32)=s.regs 4-(136#32) := by simp [BitVec.sub_eq_add_neg,BitVec.add_assoc]
    rw [eq]
    exact started.2.2.2.2.2.1
  obtain ⟨⟨m,hm,tail⟩,memory,stackOut,next,pc⟩ := E1M1ThingReturn.execution entry.core (path thing angle ox oy).trace target outcome safe ret
  have allLines : AllLines before := finished_lines (E1M1ScanMemory.firstScan gun s).core c.ids.length 0x2ba20 (E1M1PathMap.resolve lines)
    (E1M1FiringScan.initial gun s weapon actor thing angle ox oy xout yout base lines words c w h data input)
    (E1M1ScanMemory.firstScan gun s).flags (path thing angle ox oy).trace
  have converted := relabel (E1M1ThingReturn.view entry.core).core 0x2ba20 lines objects before allLines tracked
  have arg : (E1M1ThingReturn.view entry.core).core.regs 1=object :=
    (E1M1ThingReturn.view_regs entry.core).2.trans started.2.2.1
  obtain ⟨after,production,collection⟩ := finish_collect (E1M1ThingReturn.view entry.core) (path thing angle ox oy).trace target
    id before (resolve lines objects) object outcome arg (by intro frac; simpa [resolve] using objectId) converted capacity
  refine ⟨⟨n+m,by omega,E1M1PspriteStep.prefix_trans
    (prior.transfer E1M1ThingReturn.program [] E1M1ThingReturn.contains_prior (by simp))
    (X86CodeMemory.lift_success tail FloorCaller.cm)⟩,?_,?_,pc,after,production,?_⟩
  · exact stackOut.trans (by rw [sp]; simp [BitVec.sub_eq_add_neg,BitVec.add_assoc])
  · rw [savedObject] at next
    apply next.trans
    change load32 (E1M1ThingReturn.finished entry.core).core.memory (object+(44#32))=
      load32 (E1M1ThingReturn.resumed entry.core).core.memory (object+(44#32))
    rw [memory]
  · refine ⟨?_,?_,collection.room⟩
    · change OriginalLineFinish.Encodes (E1M1ThingReturn.resumed entry.core).core.memory 0x2ba20 (resolve lines objects) after.collected
      rw [memory]
      exact collection.encoded
    · change load32 (E1M1ThingReturn.resumed entry.core).core.memory (0x2c028#32)=_
      rw [memory]
      exact collection.cursor
end Firing
end Doom.Proofs.E1M1ThingFinish
