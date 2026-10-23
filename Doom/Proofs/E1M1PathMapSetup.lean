import Doom.Proofs.E1M1PathMapCaller
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
namespace Doom.Proofs.E1M1PathMapSetup
open Verification X86 X86Memory X86Control BlockSummary E1M1PathMap E1M1PathMapLookup

def afterInit (s : X86Memory.State) := E1M1PathGridSetup.after
  (OriginalPathIntercept.result (OriginalPathXStep.result s).core).core
def grid (s : X86Memory.State) := afterInit (OriginalPathInit.result s).core

/-- Potential writes during both axis setups, their helpers and intercept setup.
The later iterator CALL/prologue slots are already included. -/
def offsets : List Word := [0,32,-4,-8,-12,-16,4,40,44,28,36]
def StackSafe (sp a : Word) : Prop := ∀ off∈offsets, Apart a (sp+off)
def Safe (s : X86Memory.State) (a : Word) : Prop :=
  (∀ b∈(OriginalPathInit.writes s).toList, Apart a b) ∧ StackSafe (s.regs 4-(60#32)) a

theorem x_safe (s : X86Memory.State) (a : Word) (safe : StackSafe (s.regs 4) a) :
    ∀ b∈PathXStepFrame.writes s, Apart a b := by
  intro b hb
  simp only [PathXStepFrame.writes,List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with rfl|rfl|rfl|rfl|rfl|rfl
  · simpa using safe 0 (by simp [offsets])
  · exact safe 32 (by simp [offsets])
  · simpa [BitVec.sub_eq_add_neg] using safe (-4) (by simp [offsets])
  · simpa [BitVec.sub_eq_add_neg] using safe (-8) (by simp [offsets])
  · simpa [BitVec.sub_eq_add_neg] using safe (-12) (by simp [offsets])
  · simpa [BitVec.sub_eq_add_neg] using safe (-16) (by simp [offsets])

theorem y_safe (s : X86Memory.State) (a : Word) (safe : StackSafe (s.regs 4) a) :
    ∀ b∈OriginalPathYStep.writes s, Apart a b := by
  intro b hb
  simp only [OriginalPathYStep.writes,List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with rfl|rfl|rfl|rfl|rfl
  · exact safe 28 (by simp [offsets])
  · simpa [BitVec.sub_eq_add_neg] using safe (-4) (by simp [offsets])
  · simpa [BitVec.sub_eq_add_neg] using safe (-8) (by simp [offsets])
  · simpa [BitVec.sub_eq_add_neg] using safe (-12) (by simp [offsets])
  · simpa [BitVec.sub_eq_add_neg] using safe (-16) (by simp [offsets])

theorem after_stack (s : X86Memory.State) : (afterInit s).core.regs 4=s.regs 4 := by
  change (OriginalPathYStep.result (OriginalPathIntercept.result (OriginalPathXStep.result s).core).core).core.regs 4=_
  rw [(OriginalPathYStep.preserved _).1]
  exact PathXStepFrame.stack s

/-- A single protected-word contract composes every setup block, including both
helper branches. It does not require interior memory-image assumptions. -/
theorem after_frame (s : X86Memory.State) (a : Word) (safe : StackSafe (s.regs 4) a) :
    load32 (afterInit s).core.memory a=load32 s.memory a := by
  let x := (OriginalPathXStep.result s).core
  let i := (OriginalPathIntercept.result x).core
  let y := (OriginalPathYStep.result i).core
  have xs : x.regs 4=s.regs 4 := PathXStepFrame.stack s
  have isp : i.regs 4=s.regs 4 := xs
  have ys : y.regs 4=s.regs 4 := (OriginalPathYStep.preserved i).1.trans isp
  calc
    _ = load32 y.memory a := OriginalPathSecondIntercept.frame y a (by rw [ys]; exact safe 36 (by simp [offsets]))
    _ = load32 i.memory a := OriginalPathYStep.frame i a (y_safe i a (by rw [isp]; exact safe))
    _ = load32 x.memory a := OriginalPathIntercept.frame x a (by
      intro off ho
      rw [xs]
      apply safe
      simp only [List.mem_cons,List.not_mem_nil,or_false] at ho
      rcases ho with rfl|rfl|rfl <;> simp [offsets])
    _ = load32 s.memory a := PathXStepFrame.frame s a (x_safe s a safe)

theorem grid_stack (s : X86Memory.State) (ox oy sx sy ex ey : Fixed)
    (geometry : OriginalPathInit.Inputs s ox oy sx sy ex ey) :
    (grid s).core.regs 4=s.regs 4-(60#32) :=
  (after_stack (OriginalPathInit.result s).core).trans (OriginalPathInit.ready s ox oy sx sy ex ey geometry).stack

theorem grid_frame (s : X86Memory.State) (ox oy sx sy ex ey : Fixed)
    (geometry : OriginalPathInit.Inputs s ox oy sx sy ex ey) (a : Word) (safe : Safe s a) :
    load32 (grid s).core.memory a=load32 s.memory a := by
  have keep := after_frame (OriginalPathInit.result s).core a (by
    rw [(OriginalPathInit.ready s ox oy sx sy ex ey geometry).stack]
    exact safe.2)
  exact keep.trans (OriginalPathInit.frame15 s a safe.1)

theorem caller_safe (s : X86Memory.State) (ox oy sx sy ex ey : Fixed)
    (geometry : OriginalPathInit.Inputs s ox oy sx sy ex ey) (a : Word) (safe : Safe s a) :
    E1M1PathMapCaller.Safe (grid s).core a := by
  unfold E1M1PathMapCaller.Safe
  rw [grid_stack s ox oy sx sy ex ey geometry]
  exact ⟨by simpa [BitVec.sub_eq_add_neg] using safe.2 (-4) (by simp [offsets]),
    by simpa [BitVec.sub_eq_add_neg] using safe.2 (-8) (by simp [offsets]),
    by simpa [BitVec.sub_eq_add_neg] using safe.2 (-12) (by simp [offsets])⟩

/-- The map contract is now stated at P_PathTraverse entry, before initialization
changes the valid count, intercept cursor, trace globals and stack locals. -/
structure MapInputs (s : X86Memory.State) (base lines : Word) (words : Array Nat) (w h : Nat) : Prop where
  width : load32 s.memory 0x2c0fc=BitVec.ofNat 32 w
  height : load32 s.memory 0x2c110=BitVec.ofNat 32 h
  widthBound : w<2^31
  heightBound : h<2^31
  table : load32 s.memory 0x2c100=base+(8#32)
  lists : load32 s.memory 0x2c10c=base
  lines : load32 s.memory 0x2c120=lines
  globalsSafe : ∀ a∈[(0x2c0fc#32),0x2c110,0x2c100,0x2c10c,0x2c120], Safe s a
  image : WordImage s.memory base words
  imageSafe : ∀ i<words.size, Safe s (base+BitVec.ofNat 32 (2*i))

theorem map_at_grid (s : X86Memory.State) (ox oy sx sy ex ey : Fixed)
    (geometry : OriginalPathInit.Inputs s ox oy sx sy ex ey)
    (base lines : Word) (words : Array Nat) (w h : Nat) (map : MapInputs s base lines words w h) :
    E1M1PathMapCaller.Dimensions (grid s).core w h ∧
    E1M1PathMapCaller.Globals (grid s).core base lines ∧
    WordImage (grid s).core.memory base words ∧ E1M1PathMapCaller.ImageSafe (grid s).core base words := by
  have keep (a : Word) (ha : a∈[(0x2c0fc#32),0x2c110,0x2c100,0x2c10c,0x2c120]) :=
    grid_frame s ox oy sx sy ex ey geometry a (map.globalsSafe a ha)
  have safe (a : Word) (ha : a∈[(0x2c0fc#32),0x2c110,0x2c100,0x2c10c,0x2c120]) :=
    caller_safe s ox oy sx sy ex ey geometry a (map.globalsSafe a ha)
  refine ⟨⟨(keep _ (by simp)).trans map.width,(keep _ (by simp)).trans map.height,map.widthBound,map.heightBound,?_⟩,
    ⟨(keep _ (by simp)).trans map.table,(keep _ (by simp)).trans map.lists,(keep _ (by simp)).trans map.lines,?_⟩,?_,?_⟩
  · intro a ha
    apply safe
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl|rfl <;> simp
  · intro a ha
    apply safe
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl|rfl|rfl <;> simp
  · intro i v hv
    obtain ⟨hi,_⟩ := Array.getElem?_eq_some_iff.mp hv
    have eq := congrArg (fun v : Word => v.extractLsb' 0 16)
      (grid_frame s ox oy sx sy ex ey geometry _ (map.imageSafe i hi))
    rw [SectorDispatch.load_half,SectorDispatch.load_half] at eq
    exact eq.trans (map.image i v hv)
  · intro i hi
    exact caller_safe s ox oy sx sy ex ey geometry _ (map.imageSafe i hi)

/-- Initialization supplies the empty collection. Only its cursor must survive
axis setup; initialization intentionally changes it and cannot preserve it. -/
theorem initial_collection_at_scan (s : X86Memory.State) (ox oy sx sy ex ey : Fixed)
    (geometry : OriginalPathInit.Inputs s ox oy sx sy ex ey) (words : Array Nat) (c : Cell)
    (valid : c.Valid words) (resolver : Collision.Intercept → Word)
    (cursorSafe : StackSafe (s.regs 4-(60#32)) (0x2c028#32)) :
    OriginalLineCollection.Tracks (E1M1PathMapCaller.scan (grid s).core).core 0x2ba20 resolver #[] c.ids.length := by
  have initial := initialized_collection s ox oy sx sy ex ey geometry words c valid resolver
  have sp := (OriginalPathInit.ready s ox oy sx sy ex ey geometry).stack
  have atGrid : OriginalLineCollection.Tracks (grid s).core 0x2ba20 resolver #[] c.ids.length := by
    refine ⟨?_,?_,initial.room⟩
    · intro i hi; simp at hi
    · change load32 (afterInit (OriginalPathInit.result s).core).core.memory (0x2c028#32)=_
      rw [after_frame _ _ (by rw [sp]; exact cursorSafe)]
      exact initial.cursor
  apply E1M1PathMapCaller.collection_preserved _ _ _ _ _ atGrid
  · unfold E1M1PathMapCaller.Safe
    rw [grid_stack s ox oy sx sy ex ey geometry]
    exact ⟨by simpa [BitVec.sub_eq_add_neg] using cursorSafe (-4) (by simp [offsets]),
      by simpa [BitVec.sub_eq_add_neg] using cursorSafe (-8) (by simp [offsets]),
      by simpa [BitVec.sub_eq_add_neg] using cursorSafe (-12) (by simp [offsets])⟩
  · intro i hi; simp at hi
/-- Both weapons reuse the earlier memory contract and actual initialized
collection. No first-grid map image, globals, empty cursor or reserve is assumed. -/
theorem first_scan_execution (gun : Fire.Gun) (s : X86Memory.State) (f : Option Flags)
    (weapon : Weapon.Context) (input : E1M1DischargeSetters.Inputs gun s weapon)
    (ox oy sx sy ex ey : Fixed)
    (geometry : OriginalPathInit.Inputs (E1M1AimSetup.firstTraversal gun s).core ox oy sx sy ex ey)
    (layout : OriginalAimSetup.Separated (E1M1AimQuery.firstRay gun s).core)
    (xout yout : Int32 × Fixed × Fixed)
    (okX : (Collision.pathStart ox oy sx sy ex ey).xStep=.ok xout)
    (okY : (Collision.pathStart ox oy sx sy ex ey).yStep=.ok yout)
    (base lines : Word) (words : Array Nat) (c : Cell) (w h : Nat)
    (map : MapInputs (E1M1AimSetup.firstTraversal gun s).core base lines words w h)
    (cursorSafe : StackSafe ((E1M1AimSetup.firstTraversal gun s).core.regs 4-(60#32)) (0x2c028#32))
    (inside : Collision.pathCellInside (Collision.pathStart ox oy sx sy ex ey).startBlockX
      (Collision.pathStart ox oy sx sy ex ey).startBlockY w h=true)
    (valid : c.Valid words)
    (selected : words[4+Collision.pathCellIndex (Collision.pathStart ox oy sx sy ex ey).startBlockX
      (Collision.pathStart ox oy sx sy ex ey).startBlockY w]?=some c.offset) :
    (∃ n≤368, X86CodeMemory.Prefix FloorCaller.cm E1M1PathMapCaller.firingProgram [] n
      ⟨s,f,OriginalWeaponDischarge.afterSound gun⟩
      (E1M1PathMapCaller.scan (E1M1PathGridSetup.firstGrid gun s).core)) ∧
    ScanWords (E1M1PathMapCaller.scan (E1M1PathGridSetup.firstGrid gun s).core).core lines c ∧
    OriginalLineCollection.Tracks (E1M1PathMapCaller.scan (E1M1PathGridSetup.firstGrid gun s).core).core
      0x2ba20 (resolve lines) #[] c.ids.length := by
  have retained := map_at_grid _ ox oy sx sy ex ey geometry base lines words w h map
  have run := E1M1PathMapCaller.first_scan_execution gun s f weapon input ox oy sx sy ex ey geometry
    layout xout yout okX okY base lines words c w h retained.1 retained.2.1 inside valid
    retained.2.2.1 retained.2.2.2 selected
  exact ⟨run.1,run.2,initial_collection_at_scan _ ox oy sx sy ex ey geometry words c valid
    (resolve lines) cursorSafe⟩
end Doom.Proofs.E1M1PathMapSetup
