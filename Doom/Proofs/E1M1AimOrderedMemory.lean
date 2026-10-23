import Doom.Proofs.E1M1AimHitMemory
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 2400000
namespace Doom.Proofs.E1M1AimOrderedMemory
open Verification X86 X86Memory X86Control BlockSummary Collision E1M1SelectionHistory
open E1M1HistoryDispatch (Selection)
open E1M1InterceptMinimum (minimum)
open E1M1AimCatalog (Portal)
open E1M1AimSourceCatalog (Represents)
open E1M1AimIteration
open E1M1AimActorBoundary (Boundary)
open E1M1AimSynchronizedCycle (AlignedNext)
open E1M1AimActorCatalog (Catalog)
open E1M1AimPortalPrefix (Position)
open E1M1AimActorSelect (program)
open E1M1AimHitOutcome (Arithmetic)
open E1M1AimHitMemory (Exit Outcome)
open E1M1AimOrderedLoop (Available)
open E1M1AimMapFrame (StableWord)
open E1M1AimMixedExit (Ready)
attribute [local irreducible] load32 store32 SolidThing.shootHeight

/-- Add null-target preservation to exhaustive correspondence from an established callback/exit
boundary. Each continuing callback consumes one distinct record. There is no
source Sequence, final branch, selected target, or future machine state premise. -/
theorem execution (scene : Scene) (shooter : Nat) (thing : SolidThing) (path original : PathResult)
    (distance : Fixed) (resolve : Intercept → Word) (portals : Nat → Option Portal) (walls : Nat → Prop) (who : Word)
    (represented : Represents scene original.collected portals)
    (wallMap : E1M1AimWallCatalog.Represents scene original.collected walls)
    (covered : E1M1AimLineCoverage.Coverage original.collected walls portals)
    (empty : original.visited=#[]) (query : E1M1QuerySource.visitHits original (fun _ _ => true)=.ok path)
    (available : Available scene shooter original.collected portals distance thing.shootHeight)
    (fuel : Nat) (a : Position) (origin : X86Memory.State) (s : X86Control.State)
    (seen : List Nat) (visits : Array Intercept)
    (budget : fuel=original.collected.size-seen.length)
    (history : History original.collected a.work seen visits)
    (boundary : Boundary origin scene shooter thing path original distance a.work seen resolve portals a.lower a.upper a.log s)
    (bottom : load32 s.core.memory (0x2c1e4#32)=a.lower.raw.toBitVec)
    (top : load32 s.core.memory (0x2c1e8#32)=a.upper.raw.toBitVec)
    (ready : Ready s.core scene shooter original.collected a.work resolve who
      (fun state => E1M1AimWallCatalog.Catalog state original.collected resolve walls ∧ StableWord state 0x2b9f8))
    (null : load32 s.core.memory (0x2b9f8#32)=0) :
    ∃ n≤fuel*(157+7*original.collected.size), ∃ out answer,
      X86CodeMemory.Prefix FloorCaller.cm program [] n s out ∧ Exit original.collected resolve out answer ∧
      remaining scene shooter thing path distance
        (List.range' seen.length (path.visited.size-seen.length)) a.lower a.upper a.log=.ok answer := by
  induction fuel using Nat.strongRecOn generalizing a origin s seen visits with
  | ind fuel ih =>
    rcases boundary with terminal|⟨fraction,j,selection,persistent,inside,hit⟩
    · exact ⟨0,by omega,s,{path},.nil _,⟨⟨Or.inl terminal.1,by intro id h; cases h⟩,by intro _; exact ⟨null,rfl⟩⟩,terminal.2.2⟩
    · obtain ⟨arithmetic⟩ := available a seen visits history fraction j selection.chosen selection.within
      obtain ⟨actors,wallsBefore,targetSafe⟩ := ready fraction j selection.chosen selection.within
      have pc : s.pc=0x2b760 := selection.ready.pc
      have atCallback : s=⟨s.core,s.flags,0x2b760⟩ := by cases s; simp_all
      have selected : Selection original.collected a.work seen resolve 0x2b760 (origin.regs 4+4)
          ⟨s.core,s.flags,0x2b760⟩ fraction j := by rw [← atCallback]; exact selection
      obtain ⟨n,hn,middle,run,outcome⟩ := E1M1AimHitMemory.execution scene shooter thing path original distance resolve
        portals walls who represented wallMap covered empty query a s.core s.flags seen visits (origin.regs 4+4) fraction j
        history selected persistent bottom top actors wallsBefore arithmetic null targetSafe
      rw [← atCallback] at run
      have size := (E1M1SelectionHistory.image history).size
      have positive := E1M1TraversalBudget.remaining_step history fraction j selection.chosen selection.within
      rcases outcome with ⟨answer,exit,source⟩|⟨b,work,advanced,nextBoundary,low,high,frame,source⟩
      · have bound : 157+7*original.collected.size≤fuel*(157+7*original.collected.size) := by
          calc
            _ = 1*(157+7*original.collected.size) := by omega
            _ ≤ _ := Nat.mul_le_mul_right _ (by omega)
        exact ⟨n,by omega,middle,answer,run,exit,source⟩
      · have nextReady : Ready middle.core scene shooter original.collected b.work resolve who
            (fun state => E1M1AimWallCatalog.Catalog state original.collected resolve walls ∧ StableWord state 0x2b9f8) := by
          intro nextFraction k chosen within
          have next := E1M1AimActorBoundary.next_callback s.core scene shooter thing path original distance b.work (j::seen)
            (visits.push a.work[j]!) resolve portals b.lower b.upper b.log middle advanced empty query nextBoundary nextFraction k chosen within
          have stack := E1M1AimCycleInvariant.stack s.core original.collected b.work (j::seen) resolve 0x2b760 middle nextFraction k next.1
          have bound : j<128 := by have := selection.inside; have := persistent.bounded; omega
          have pointer := selection.ready.pointer.trans selection.argument
          exact ⟨E1M1AimActorCatalog.preserved s.core middle j scene shooter original.collected resolve who
            frame stack pointer bound actors,E1M1AimWallCatalog.preserved s.core middle j original.collected resolve walls
            frame stack pointer bound wallsBefore,E1M1AimMapFrame.stable_word s.core middle.core 0x2b9f8 stack targetSafe⟩
        have zero := (E1M1AimMapFrame.word s.core middle j 0x2b9f8 frame
          (selection.ready.pointer.trans selection.argument) (by have := selection.inside; have := persistent.bounded; omega) targetSafe).trans null
        have decrease : original.collected.size-(j::seen).length<fuel := by omega
        obtain ⟨m,hm,out,answer,tail,exit,sourceTail⟩ := ih _ decrease b s.core middle (j::seen) (visits.push a.work[j]!)
          rfl advanced nextBoundary low high nextReady zero
        refine ⟨n+m,?_,out,answer,E1M1PspriteStep.prefix_trans run tail,exit,?_⟩
        · have eq : fuel=(original.collected.size-(j::seen).length)+1 := by omega
          rw [eq,Nat.add_mul,Nat.one_mul]; omega
        · exact source.trans (by simpa only [List.length_cons] using sourceTail)


/-- Production post-path result with the null-target case now represented in
memory. Initial clearing and protection are entry premises; collection and the
enclosing return are not silently included. -/
theorem initial (scene : Scene) (shooter : Nat) (thing : SolidThing) (path original : PathResult)
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
    (wallCatalog : E1M1AimWallCatalog.Catalog s.core original.collected resolve walls)
    (targetSafe : StableWord s.core 0x2b9f8) (null : load32 s.core.memory (0x2b9f8#32)=0) :
    ∃ n≤original.collected.size*(157+7*original.collected.size), ∃ out answer,
      X86CodeMemory.Prefix FloorCaller.cm program [] n s out ∧ Exit original.collected resolve out answer ∧
      E1M1AimSource.afterPath scene shooter thing path distance=.ok answer := by
  let a : Position := ⟨original.collected,aimBottomSlope,aimTopSlope,#[]⟩
  have history : History original.collected a.work [] #[] := .nil
  have boundary := E1M1AimMixedBoundary.from_line origin scene shooter thing path original distance a [] #[]
    resolve portals s history empty query aligned
  obtain ⟨n,hn,out,answer,run,exit,source⟩ := execution scene shooter thing path original distance resolve
    portals walls who represented wallMap covered empty query available original.collected.size a origin s [] #[]
    (by simp) history boundary bottom top (by intro fraction j chosen within; exact ⟨actors,wallCatalog,targetSafe⟩) null
  refine ⟨n,hn,out,answer,run,exit,?_⟩
  rw [E1M1AimIteration.live]
  simpa only [List.length_nil,Nat.sub_zero] using source
end Doom.Proofs.E1M1AimOrderedMemory
