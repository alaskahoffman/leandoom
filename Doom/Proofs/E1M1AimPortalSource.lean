import Doom.Proofs.E1M1AimOpening
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1600000
namespace Doom.Proofs.E1M1AimPortalSource
open Collision E1M1AimSource

/-- The live aim loop stops at a first two-sided line whose sector opening is
closed, before division, slope clipping, or examining a subsequent hit. -/
theorem first_closed (scene : Scene) (shooter : Nat) (thing : SolidThing)
    (path : PathResult) (distance : Fixed) (hit : Intercept) (back : Heights)
    (nonempty : 0<path.visited.size) (first : path.visited[0]! = hit)
    (isLine : hit.isLine=true) (two : scene.lines[hit.id]!.twoSided=true)
    (backSector : scene.lines[hit.id]!.back=some back)
    (closed : min scene.lines[hit.id]!.front.ceiling.raw back.ceiling.raw ≤
      max scene.lines[hit.id]!.front.floor.raw back.floor.raw) :
    afterPath scene shooter thing path distance=.ok {path:=stopped path 1} := by
  have first' : path.visited[0]=hit := by simpa only [getElem!_pos path.visited 0 nonempty] using first
  obtain ⟨n,size⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : path.visited.size≠0)
  simp [afterPath,Std.Legacy.Range.forIn_eq_forIn_range',Std.Legacy.Range.size,size,
    List.range'_succ,List.forIn_cons,first',isLine,two,backSector,closed]
  rfl

theorem blocked_query (scene : Scene) (shooter : Nat) (angle : Angle) (distance : Fixed)
    (thing : SolidThing) (path : PathResult) (hit : Intercept) (back : Heights)
    (traced : attackPath scene shooter angle distance=.ok (thing,path))
    (nonempty : 0<path.visited.size) (first : path.visited[0]! = hit)
    (isLine : hit.isLine=true) (two : scene.lines[hit.id]!.twoSided=true)
    (backSector : scene.lines[hit.id]!.back=some back)
    (closed : min scene.lines[hit.id]!.front.ceiling.raw back.ceiling.raw ≤
      max scene.lines[hit.id]!.front.floor.raw back.floor.raw) :
    scene.aimLineAttack shooter angle distance=.ok {path:=stopped path 1} := by
  rw [live,traced]
  exact first_closed scene shooter thing path distance hit back nonempty first isLine two backSector closed

/-- The DOS signed-word choice is the same predicate used by the live Fixed
height comparison, including negative and extreme 32-bit heights. -/
theorem signed_bounds (ff fc bf bc : Fixed) :
    ((if bc.raw.toBitVec.toInt≤fc.raw.toBitVec.toInt then bc.raw.toBitVec else fc.raw.toBitVec).toInt ≤
      (if ff.raw.toBitVec.toInt≤bf.raw.toBitVec.toInt then bf.raw.toBitVec else ff.raw.toBitVec).toInt) ↔
      min fc.raw bc.raw ≤ max ff.raw bf.raw := by
  simp only [Int32.toInt_toBitVec]
  by_cases ceiling : bc.raw≤fc.raw <;> by_cases floor : ff.raw≤bf.raw
  all_goals
    simp only [Int32.le_iff_toInt_le] at ceiling floor
    simp [min,max,minOfLe,maxOfLe,Int32.le_iff_toInt_le,ceiling,floor,Int32.toInt_toBitVec,apply_ite] <;> omega

open Verification X86 X86Memory X86Control
/-- The original call reaches its closed-opening exit and the live Lean query
stops on the same first line. Ordered-path and helper-entry map representations
are explicit interfaces; the callback RET and full query return are later work. -/
theorem closed_correspondence (s : X86Memory.State) (f : Option Flags)
    (scene : Scene) (shooter : Nat) (angle : Angle) (distance : Fixed)
    (thing : SolidThing) (path : PathResult) (hit : Intercept) (back : Heights)
    (frontPtr backPtr : Word)
    (safe : E1M1AimOpening.Safe s)
    (mapSafe : E1M1OpeningHeights.Safe (OriginalAimOpening.called s) frontPtr backPtr)
    (side : load16 (OriginalAimOpening.called s).memory (s.regs 1+(24#32))≠0xffff)
    (front : load32 (OriginalAimOpening.called s).memory (s.regs 1+(46#32))=frontPtr)
    (backAddress : load32 (OriginalAimOpening.called s).memory (s.regs 1+(50#32))=backPtr)
    (ff : load32 (OriginalAimOpening.called s).memory frontPtr=scene.lines[hit.id]!.front.floor.raw.toBitVec)
    (fc : load32 (OriginalAimOpening.called s).memory (frontPtr+(4#32))=scene.lines[hit.id]!.front.ceiling.raw.toBitVec)
    (bf : load32 (OriginalAimOpening.called s).memory backPtr=back.floor.raw.toBitVec)
    (bc : load32 (OriginalAimOpening.called s).memory (backPtr+(4#32))=back.ceiling.raw.toBitVec)
    (traced : attackPath scene shooter angle distance=.ok (thing,path))
    (nonempty : 0<path.visited.size) (first : path.visited[0]! = hit)
    (isLine : hit.isLine=true) (two : scene.lines[hit.id]!.twoSided=true)
    (backSector : scene.lines[hit.id]!.back=some back)
    (closed : min scene.lines[hit.id]!.front.ceiling.raw back.ceiling.raw ≤
      max scene.lines[hit.id]!.front.floor.raw back.floor.raw) :
    (∃ n, n≤36 ∧ X86CodeMemory.Prefix FloorCaller.cm E1M1AimOpening.program [] n
      ⟨s,f,0x2b77f⟩ (E1M1AimOpening.result s)) ∧
    (E1M1AimOpening.result s).pc=0x2b8d2 ∧
    scene.aimLineAttack shooter angle distance=.ok {path:=stopped path 1} := by
  refine ⟨E1M1AimOpening.execution s f safe,?_,
    blocked_query scene shooter angle distance thing path hit back traced nonempty first isLine two backSector closed⟩
  rw [E1M1AimOpening.height_decision s frontPtr backPtr _ _ _ _ mapSafe side front backAddress ff fc bf bc]
  exact if_pos ((signed_bounds _ _ _ _).mpr closed)
end Doom.Proofs.E1M1AimPortalSource
