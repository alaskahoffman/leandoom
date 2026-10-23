import Doom.Proofs.E1M1AimActorCatalog
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 2400000
namespace Doom.Proofs.E1M1AimActorCatalogCycle
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

/-- Derive every actor-specific machine premise from the incoming catalog, and
carry the entire catalog to any next callback produced by this actor cycle. -/
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
      X86CodeMemory.Prefix FloorCaller.cm program [] n ⟨s,f,0x2b760⟩ out ∧
      Outcome (dispatch scene shooter work[j]! lower upper topSlope bottomSlope) s
        scene shooter thing path original distance lower upper topSlope bottomSlope log work seen visits j resolve portals out ∧
      (dispatch scene shooter work[j]! lower upper topSlope bottomSlope≠.selected →
        ∀ nextFraction k, Selection original.collected (consume work j) (j::seen) resolve 0x2b760
          (s.regs 4+4) out nextFraction k → Catalog out.core scene shooter original.collected resolve who) := by
  have entry := E1M1AimActorCatalog.inputs ⟨s,f,0x2b760⟩ scene shooter thing original.collected work seen visits
    resolve portals distance target sp who fraction j history selection before catalog isThing
  obtain ⟨n,hn,out,run,outcome⟩ := E1M1AimActorCycle.execution
    s f scene shooter thing path original distance lower upper topSlope bottomSlope log work seen visits resolve target sp who fraction j
    history selection portals before empty query bottom top isThing entry.shooterSafe entry.flagsSafe entry.shooterWord
    entry.identity entry.flags entry.topSafe entry.bottomSafe entry.z entry.height topOk bottomOk entry.saveSafe
  refine ⟨n,hn,out,run,outcome,?_⟩
  intro continuing nextFraction k nextSelection
  have frame : Frame s out := by
    cases decision : dispatch scene shooter work[j]! lower upper topSlope bottomSlope <;>
      simp only [decision,Outcome] at outcome
    · exact outcome.2.2.2.2.1
    · exact outcome.2.2.2.2.1
    · exact outcome.2.2.2.2.1
    · exact False.elim (continuing decision)
  exact E1M1AimActorCatalog.preserved s out j scene shooter original.collected resolve who frame
    (E1M1AimCycleInvariant.stack s original.collected (consume work j) (j::seen) resolve 0x2b760 out nextFraction k nextSelection)
    (selection.ready.pointer.trans selection.argument) (by have := selection.inside; have := before.bounded; omega) catalog
end Doom.Proofs.E1M1AimActorCatalogCycle
