import Doom.Proofs.E1M1AimMixedPrefix
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 2400000
namespace Doom.Proofs.E1M1AimMixedSelected
open Verification X86 X86Memory X86Control BlockSummary Collision E1M1SelectionHistory
open E1M1HistoryDispatch (Selection)
open E1M1InterceptMinimum (minimum)
open E1M1AimCatalog (Portal)
open E1M1AimSourceCatalog (Represents)
open E1M1AimActorCatalog (Catalog)
open E1M1AimIteration
open E1M1AimSynchronizedCycle (AlignedNext)
open E1M1AimPortalPrefix (Position)
open E1M1AimMixedPrefix (Sequence)
open E1M1AimActorSelect (program)
attribute [local irreducible] load32 store32 SolidThing.shootHeight

/-- A whole proved mixed portal/actor prefix followed by successful selection. The
actor catalog is supplied only before the prefix, then transported through every
callback to derive the final actor inputs and real return/parent stop. -/
theorem selected (scene : Scene) (shooter : Nat) (thing : SolidThing) (path original : PathResult)
    (distance : Fixed) (resolve : Intercept → Word) (portals : Nat → Option Portal) (who : Word)
    (represented : Represents scene original.collected portals) (empty : original.visited=#[])
    (query : E1M1QuerySource.visitHits original (fun _ _ => true)=.ok path)
    (a final : Position) (count : Nat) (sequence : Sequence scene shooter portals distance thing.shootHeight a final count)
    (origin : X86Memory.State) (s : X86Control.State) (seen : List Nat) (visits : Array Intercept)
    (history : History original.collected a.work seen visits)
    (aligned : AlignedNext origin scene shooter thing path original distance a.work seen resolve portals a.lower a.upper a.log s)
    (bottom : load32 s.core.memory (0x2c1e4#32)=a.lower.raw.toBitVec)
    (top : load32 s.core.memory (0x2c1e8#32)=a.upper.raw.toBitVec)
    (catalog : Catalog s.core scene shooter original.collected resolve who)
    (fraction : Int32) (j : Nat) (chosen : minimum final.work=.ok (fraction,some j)) (within : ¬fraction>65536)
    (isThing : (final.work[j]!).isLine=false)
    (different : (final.work[j]!).id≠shooter) (shootable : scene.things[final.work[j]!.id]!.shootable=true)
    (topSlope bottomSlope : Fixed)
    (topOk : checkedPathDiv (scene.things[final.work[j]!.id]!.z+scene.things[final.work[j]!.id]!.height-thing.shootHeight)
      (distance*final.work[j]!.frac)=.ok topSlope) (admitted : ¬topSlope.raw<final.lower.raw)
    (bottomOk : checkedPathDiv (scene.things[final.work[j]!.id]!.z-thing.shootHeight)
      (distance*final.work[j]!.frac)=.ok bottomSlope) (bottomAdmitted : ¬final.upper.raw<bottomSlope.raw) :
    ∃ n≤count*(157+7*original.collected.size)+115, ∃ out finalSeen finalVisits,
      X86CodeMemory.Prefix FloorCaller.cm program [] n s out ∧
      out.pc=0x2c88c ∧ out.core.regs 0=0 ∧
      History original.collected final.work finalSeen finalVisits ∧ finalSeen.length=seen.length+count ∧
      OriginalLineFinish.Encodes out.core.memory 0x2ba20 resolve final.work ∧
      load32 out.core.memory (0x2c1e4#32)=final.lower.raw.toBitVec ∧
      load32 out.core.memory (0x2c1e8#32)=final.upper.raw.toBitVec ∧
      load32 out.core.memory (0x2b9f8#32)=resolve original.collected[j]! ∧
      load32 out.core.memory (0x2b9b4#32)=
        (E1M1AimActorSelectEntry.answer scene thing path distance final.lower final.upper topSlope bottomSlope final.log (seen.length+count) final.work[j]!).slope.raw.toBitVec ∧
      remaining scene shooter thing path distance
        (List.range' seen.length (path.visited.size-seen.length)) a.lower a.upper a.log =
        .ok (E1M1AimActorSelectEntry.answer scene thing path distance final.lower final.upper topSlope bottomSlope final.log (seen.length+count) final.work[j]!) := by
  obtain ⟨n,hn,middle,finalOrigin,finalSeen,finalVisits,run,finalHistory,length,finalAligned,low,high,carried,selection,persistent,source⟩ :=
    E1M1AimMixedPrefix.execution scene shooter thing path original distance resolve portals who represented empty query
      a final count sequence origin s seen visits history aligned bottom top catalog fraction j chosen within
  have atCallback : middle=⟨middle.core,middle.flags,0x2b760⟩ := by
    cases middle
    simp_all only [X86Control.State.mk.injEq,true_and]
    exact selection.ready.pc
  have selected : Selection original.collected final.work finalSeen resolve 0x2b760 (finalOrigin.regs 4+4)
      ⟨middle.core,middle.flags,0x2b760⟩ fraction j := by rw [← atCallback]; exact selection
  have entry := E1M1AimActorCatalog.inputs ⟨middle.core,middle.flags,0x2b760⟩ scene shooter thing original.collected final.work finalSeen finalVisits
    resolve portals distance 0x2b760 (finalOrigin.regs 4+4) who fraction j finalHistory selected persistent carried isThing
  obtain ⟨m,hm,out,tail,pc,zero,_,records,targetOut,slopeOut,lo,hi,sourceStop⟩ := E1M1AimActorStop.execution
    middle.core middle.flags scene shooter thing path original distance final.lower final.upper topSlope bottomSlope final.log
    final.work finalSeen finalVisits resolve 0x2b760 (finalOrigin.regs 4+4) who fraction j finalHistory selected portals persistent
    empty query low high isThing entry.shooterSafe entry.flagsSafe entry.shooterWord entry.identity entry.flags different shootable
    entry.topSafe entry.bottomSafe entry.z entry.height topOk admitted bottomOk bottomAdmitted entry.saveSafe
  rw [← atCallback] at tail
  refine ⟨n+m,by omega,out,finalSeen,finalVisits,E1M1PspriteStep.prefix_trans run tail,
    pc,zero,finalHistory,length,records,lo,hi,targetOut,?_,?_⟩
  · simpa only [length] using slopeOut
  · exact source.trans (by simpa only [length] using sourceStop)
end Doom.Proofs.E1M1AimMixedSelected
