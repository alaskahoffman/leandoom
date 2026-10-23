import Doom.Proofs.E1M1AimOpeningFrame
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1800000
namespace Doom.Proofs.E1M1AimMapped
open Verification X86 X86Memory X86Control BlockSummary Collision E1M1AimOpeningFrame

/-- All representations and static separation are stated at callback entry.
The reached helper's memory, output bounds and branch are derived. -/
structure Inputs (s : X86Memory.State) (hit : Intercept)
    (line front back ff fc bf bc : Word) : Prop where
  record : OriginalLineFinish.RecordAt s.memory (s.regs 0) hit line
  isLine : hit.isLine=true
  tagSafe : E1M1AimWall.Safe (s.regs 4) (s.regs 0+4)
  pointerSafe : E1M1AimWall.Safe (s.regs 4) (s.regs 0+8)
  flagsSafe : E1M1AimWall.Safe (s.regs 4) (line+16)
  two : s.memory (line+16) &&& (4#8)≠0
  helperSafe : E1M1AimOpening.CallerSafe s
  mapSafe : MapSafe s line front back
  image : Image s.memory line front back ff fc bf bc

theorem execution (s : X86Memory.State) (f : Option Flags) (hit : Intercept)
    (line front back ff fc bf bc : Word) (h : Inputs s hit line front back ff fc bf bc) :
    (∃ n, n≤48 ∧ X86CodeMemory.Prefix FloorCaller.cm E1M1AimOpening.program [] n
      ⟨s,f,0x2b760⟩ (result s)) ∧
    (result s).pc=if (if bc.toInt≤fc.toInt then bc else fc).toInt ≤
      (if ff.toInt≤bf.toInt then bf else ff).toInt then 0x2b8d2 else 0x2b797 := by
  exact ⟨E1M1AimOpening.from_callback s f hit line h.record h.isLine h.tagSafe h.pointerSafe
    h.flagsSafe h.two h.helperSafe,decision s hit line front back ff fc bf bc h.record h.pointerSafe h.mapSafe h.image⟩

/-- The first closed two-sided opening is now connected from callback entry.
The source's ordered first-hit relation is still a separate interface. -/
theorem closed_correspondence (s : X86Memory.State) (f : Option Flags)
    (scene : Scene) (shooter : Nat) (angle : Angle) (distance : Fixed)
    (thing : SolidThing) (path : PathResult) (hit : Intercept) (back : Heights)
    (line frontPtr backPtr : Word)
    (h : Inputs s hit line frontPtr backPtr scene.lines[hit.id]!.front.floor.raw.toBitVec
      scene.lines[hit.id]!.front.ceiling.raw.toBitVec back.floor.raw.toBitVec back.ceiling.raw.toBitVec)
    (traced : E1M1AimSource.attackPath scene shooter angle distance=.ok (thing,path))
    (nonempty : 0<path.visited.size) (first : path.visited[0]! = hit)
    (two : scene.lines[hit.id]!.twoSided=true) (backSector : scene.lines[hit.id]!.back=some back)
    (closed : min scene.lines[hit.id]!.front.ceiling.raw back.ceiling.raw ≤
      max scene.lines[hit.id]!.front.floor.raw back.floor.raw) :
    (∃ n, n≤48 ∧ X86CodeMemory.Prefix FloorCaller.cm E1M1AimOpening.program [] n
      ⟨s,f,0x2b760⟩ (result s)) ∧ (result s).pc=0x2b8d2 ∧
    scene.aimLineAttack shooter angle distance=.ok {path:=E1M1AimSource.stopped path 1} := by
  have run := execution s f hit line frontPtr backPtr _ _ _ _ h
  refine ⟨run.1,?_,E1M1AimPortalSource.blocked_query scene shooter angle distance thing path hit back
    traced nonempty first h.isLine two backSector closed⟩
  rw [run.2]
  exact if_pos ((E1M1AimPortalSource.signed_bounds _ _ _ _).mpr closed)
end Doom.Proofs.E1M1AimMapped
