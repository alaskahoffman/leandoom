import Doom.Proofs.E1M1AimSavedWords
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 2400000
namespace Doom.Proofs.E1M1AimActorSavedCycle
open Verification X86 X86Memory X86Control BlockSummary Collision E1M1SelectionHistory
open E1M1HistoryDispatch (Selection)
open E1M1InterceptMark (consume)
open E1M1AimCatalog (Portal)
open E1M1AimTraversalInvariant (Persistent)
open E1M1AimHistoryCycle (Frame)
open E1M1AimActorCatalog (Catalog)
open E1M1AimActorSelect (program)
open E1M1AimActorDispatch (dispatch)
open E1M1AimActorCycle (Outcome)
attribute [local irreducible] load32 store32 SolidThing.shootHeight

/-- Every actor outcome preserves protected caller words, including selection. -/
theorem execution (s : X86Memory.State) (f : Option Flags)
    (scene : Scene) (shooter : Nat) (thing : SolidThing) (path original : PathResult)
    (distance lower upper topSlope bottomSlope : Fixed) (log : Array AutoAim.Portal)
    (work : Array Intercept) (seen : List Nat) (visits : Array Intercept)
    (resolve : Intercept → Word) (target sp who : Word) (fraction : Int32) (j : Nat)
    (history : History original.collected work seen visits)
    (selection : Selection original.collected work seen resolve target sp ⟨s,f,0x2b760⟩ fraction j)
    (portals : Nat → Option Portal)
    (before : Persistent s original.collected work resolve portals distance thing.shootHeight)
    (empty : original.visited=#[])
    (query : E1M1QuerySource.visitHits original (fun _ _ => true)=.ok path)
    (bottom : load32 s.memory (0x2c1e4#32)=lower.raw.toBitVec)
    (top : load32 s.memory (0x2c1e8#32)=upper.raw.toBitVec)
    (isThing : (work[j]!).isLine=false)
    (catalog : Catalog s scene shooter original.collected resolve who)
    (topOk : (work[j]!).id≠shooter → scene.things[work[j]!.id]!.shootable=true →
      checkedPathDiv (scene.things[work[j]!.id]!.z+scene.things[work[j]!.id]!.height-thing.shootHeight)
      (distance*(work[j]!).frac)=.ok topSlope)
    (bottomOk : (work[j]!).id≠shooter → scene.things[work[j]!.id]!.shootable=true →
      ¬topSlope.raw<lower.raw → checkedPathDiv (scene.things[work[j]!.id]!.z-thing.shootHeight)
      (distance*(work[j]!).frac)=.ok bottomSlope)
    :
    ∃ n≤115+7*work.size, ∃ out,
      E1M1AimSavedWords.Preserved s out ∧
      X86CodeMemory.Prefix FloorCaller.cm program [] n ⟨s,f,0x2b760⟩ out ∧
      Outcome (dispatch scene shooter work[j]! lower upper topSlope bottomSlope) s
        scene shooter thing path original distance lower upper topSlope bottomSlope log work seen visits j resolve portals out := by
  by_cases picked : dispatch scene shooter work[j]! lower upper topSlope bottomSlope=.selected
  · have different : work[j]!.id≠shooter := by
      intro same; simp [dispatch,same] at picked
    have shootable : scene.things[work[j]!.id]!.shootable=true := by
      cases eq : scene.things[work[j]!.id]!.shootable
      · simp [dispatch,eq] at picked
      · rfl
    have admitted : ¬topSlope.raw<lower.raw := by
      intro below; simp [dispatch,different,shootable,below] at picked
    have bottomAdmitted : ¬upper.raw<bottomSlope.raw := by
      intro above; simp [dispatch,different,shootable,admitted,above] at picked
    have entry := E1M1AimActorCatalog.inputs ⟨s,f,0x2b760⟩ scene shooter thing original.collected work seen visits
      resolve portals distance target sp who fraction j history selection before catalog isThing
    obtain ⟨n,hn,out,frame,run,pc,zero,stack,records,targetOut,slopeOut,lo,hi,source⟩ := E1M1AimSavedWords.selected
      s f scene shooter thing path original distance lower upper topSlope bottomSlope log work seen visits resolve target sp who fraction j
      history selection portals before empty query bottom top isThing entry.shooterSafe entry.flagsSafe entry.shooterWord
      entry.identity entry.flags different shootable entry.topSafe entry.bottomSafe entry.z entry.height
      (topOk different shootable) admitted (bottomOk different shootable admitted) bottomAdmitted entry.saveSafe
    refine ⟨n,by omega,out,frame,run,?_⟩
    simp only [picked,Outcome]
    exact ⟨lo,hi,pc,zero,stack,records,targetOut,slopeOut,source⟩
  · obtain ⟨n,hn,out,run,outcome,_⟩ := E1M1AimActorCatalogCycle.execution
      s f scene shooter thing path original distance lower upper topSlope bottomSlope log work seen visits resolve target sp who fraction j
      history selection portals before empty query bottom top isThing catalog topOk bottomOk
    have frame : Frame s out := by
      cases decision : dispatch scene shooter work[j]! lower upper topSlope bottomSlope <;>
        simp only [decision,Outcome] at outcome
      · exact outcome.2.2.2.2.1
      · exact outcome.2.2.2.2.1
      · exact outcome.2.2.2.2.1
      · exact False.elim (picked decision)
    exact ⟨n,hn,out,E1M1AimSavedWords.from_cycle s out j frame
      (selection.ready.pointer.trans selection.argument) (by have := selection.inside; have := before.bounded; omega),run,outcome⟩
end Doom.Proofs.E1M1AimActorSavedCycle
