import Doom.Proofs.E1M1AimOrderedLoop
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 2400000
namespace Doom.Proofs.E1M1AimOrderedResult
open Verification X86 X86Memory X86Control BlockSummary Collision E1M1SelectionHistory
open E1M1AimCatalog (Portal)
open E1M1AimSourceCatalog (Represents)
open E1M1AimActorCatalog (Catalog)
open E1M1AimSynchronizedCycle (AlignedNext)
open E1M1AimPortalPrefix (Position)
open E1M1AimActorSelect (program)
open E1M1AimHitOutcome (Exit)
open E1M1AimOrderedLoop (Available)
attribute [local irreducible] load32 store32 SolidThing.shootHeight

/-- The whole production post-path aiming loop, from its already-established
initial callback/exit boundary. Branches and termination are derived. Ray setup,
collection, arithmetic availability, initial memory and enclosing returns remain
outside this theorem. No-target memory clearing is not included in Exit. -/
theorem execution (scene : Scene) (shooter : Nat) (thing : SolidThing) (path original : PathResult)
    (distance : Fixed) (resolve : Intercept → Word) (portals : Nat → Option Portal) (walls : Nat → Prop) (who : Word)
    (represented : Represents scene original.collected portals)
    (wallMap : E1M1AimWallCatalog.Represents scene original.collected walls)
    (covered : E1M1AimLineCoverage.Coverage original.collected walls portals)
    (empty : original.visited=#[]) (query : E1M1QuerySource.visitHits original (fun _ _ => true)=.ok path)
    (available : Available scene shooter original.collected portals distance thing.shootHeight)
    (origin : X86Memory.State) (s : X86Control.State)
    (aligned : AlignedNext origin scene shooter thing path original distance original.collected [] resolve portals aimBottomSlope aimTopSlope #[] s)
    (bottom : load32 s.core.memory (0x2c1e4#32)=aimBottomSlope.raw.toBitVec)
    (top : load32 s.core.memory (0x2c1e8#32)=aimTopSlope.raw.toBitVec)
    (actors : Catalog s.core scene shooter original.collected resolve who)
    (wallCatalog : E1M1AimWallCatalog.Catalog s.core original.collected resolve walls) :
    ∃ n≤original.collected.size*(157+7*original.collected.size), ∃ out answer,
      X86CodeMemory.Prefix FloorCaller.cm program [] n s out ∧ Exit original.collected resolve out answer ∧
      E1M1AimSource.afterPath scene shooter thing path distance=.ok answer := by
  let a : Position := ⟨original.collected,aimBottomSlope,aimTopSlope,#[]⟩
  have history : History original.collected a.work [] #[] := .nil
  have boundary := E1M1AimMixedBoundary.from_line origin scene shooter thing path original distance a [] #[]
    resolve portals s history empty query aligned
  obtain ⟨n,hn,out,answer,run,exit,source⟩ := E1M1AimOrderedLoop.execution scene shooter thing path original distance resolve
    portals walls who represented wallMap covered empty query available original.collected.size a origin s [] #[]
    (by simp) history boundary bottom top (by intro fraction j chosen within; exact ⟨actors,wallCatalog⟩)
  refine ⟨n,hn,out,answer,run,exit,?_⟩
  rw [E1M1AimIteration.live]
  simpa only [List.length_nil,Nat.sub_zero] using source
end Doom.Proofs.E1M1AimOrderedResult
