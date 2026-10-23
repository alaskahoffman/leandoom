import Doom.Proofs.E1M1CollectionLog
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1800000
namespace Doom.Proofs.E1M1LoggedCell
open Verification X86 X86Memory X86Control BlockSummary
open E1M1CellWalkInvariant (Context Cell Common State)
open E1M1MixedCellWalk (inside Admitted Images cost instructions visits)
open E1M1CollectionLog (log state_log)
attribute [local irreducible] load32

/-- Both enabled block visits are logged, even outside the map. -/
def prepare (c : Cell) (r : Collision.PathResult) := log (false,c.x,c.y) (log (true,c.x,c.y) r)
def next (q : Context) (c : Cell) (s : X86Control.State) (r : Collision.PathResult) :=
  E1M1MixedCellWalk.next q c s (prepare c r)

/-- The aiming cell's source operations in their actual order: line log, line
lookup/scan, object log, object lookup/scan. Outer stepping is separate. -/
def collect (trace : Collision.Divline) (world : Collision.Scene) (x y : Int32)
    (seen : Array Bool) (r : Collision.PathResult) : Except String (Array Bool × Collision.PathResult) := do
  let r := log (true,x,y) r
  if Collision.pathCellInside x y world.grid.width world.grid.height then
    let some ids := world.grid.cells[Collision.pathCellIndex x y world.grid.width]? |
      throw "path: missing line cell"
    let (seen,r) ← E1M1LineSourceLoop.lineCell trace world.lines (#[0] ++ ids) seen r
    let after ← E1M1FiringThings.sceneCell trace world x y (log (false,x,y) r)
    return (seen,after)
  else return (seen,log (false,x,y) r)

/-- The two logs can be carried as ghost data through the machine scan. The
source result logs them in the original order, and the same instruction prefix,
record budget, numeric step and final PC apply to that complete result. -/
theorem one (q : Context) (c : Cell) (s : X86Control.State) (r : Collision.PathResult) (seen : Array Bool)
    (common : Common q) (height : q.world.grid.height=q.height)
    (static : Admitted q c) (scene : inside q c=true → E1M1CellLineSource.SceneLines q c)
    (state : State q s r seen) (images : Images q [c] s.core.memory) (pc : s.pc=0x2ca7f)
    (x : (E1M1PathAdvance.observe s.core).mapX=c.x.toBitVec)
    (y : (E1M1PathAdvance.observe s.core).mapY=c.y.toBitVec)
    (room : r.collected.size+cost q c≤128) :
    let out := next q c s r
    ∃ after, collect q.trace q.world c.x c.y seen r=.ok (visits q c seen,after) ∧
      (∃ n≤instructions q c, X86CodeMemory.Prefix FloorCaller.cm E1M1FiringAdvance.program [] n s out) ∧
      State q out after (visits q c seen) ∧
      after.collected.size≤r.collected.size+cost q c ∧
      E1M1PathAdvance.observe out.core=E1M1PathAdvance.step (E1M1PathAdvance.observe s.core) ∧
      out.pc=E1M1PathAdvance.nextPc (E1M1PathAdvance.observe s.core) ∧
      E1M1CellMapInvariant.Frame q.sp q.lines s.core.memory out.core.memory := by
  have lineState := state_log q s r seen (true,c.x,c.y) state
  have bothState := state_log q s _ seen (false,c.x,c.y) lineState
  obtain ⟨after,production,run,outState,used,obs,outPC,frame⟩ :=
    E1M1MixedCellWalk.one q c s (prepare c r) seen common static bothState images pc x y room
  refine ⟨after,?_,run,outState,used,obs,outPC,frame⟩
  cases yes : inside q c with
  | false =>
    have eq : after=prepare c r := by simpa [E1M1MixedCellWalk.CellResult,yes] using production
    simp only [collect,common.dimension,height,show Collision.pathCellInside c.x c.y q.width q.height=false from yes,
      Bool.false_eq_true,ite_false,visits,yes]
    rw [eq]
    rfl
  | true =>
    have st := static yes
    have lineRoom : r.collected.size+c.cell.ids.length≤128 := by
      have total : r.collected.size+(c.cell.ids.length+c.nodes.length)≤128 := by
        simpa only [cost,yes,ite_true,E1M1CellWalkInvariant.cost] using room
      omega
    have linesOne := E1M1CellLineSource.lines q c s _ seen common st lineState
      (images c (by simp) yes) pc x y lineRoom (scene yes)
    have linesBoth := E1M1CellLineSource.lines q c s (prepare c r) seen common st bothState
      (images c (by simp) yes) pc x y lineRoom (scene yes)
    have commute := E1M1CollectionLog.line_log (false,c.x,c.y) q.trace q.world.lines c.cell.ids.toArray seen (log (true,c.x,c.y) r)
    change E1M1LineSourceLoop.lineCell q.trace q.world.lines c.cell.ids.toArray seen (prepare c r)=_ at commute
    rw [linesBoth,linesOne] at commute
    have logged : E1M1CellWalk.lineResult q c s (prepare c r)=
        log (false,c.x,c.y) (E1M1CellWalk.lineResult q c s (log (true,c.x,c.y) r)) :=
      congrArg Prod.snd (Except.ok.inj commute)
    have objects : E1M1FiringThings.sceneCell q.trace q.world c.x c.y
        (log (false,c.x,c.y) (E1M1CellWalk.lineResult q c s (log (true,c.x,c.y) r)))=.ok after := by
      rw [← logged]
      simpa [E1M1MixedCellWalk.CellResult,yes] using production
    simp only [collect,common.dimension,height,show Collision.pathCellInside c.x c.y q.width q.height=true from yes,
      ite_true,(scene yes).ids,E1M1PathMap.live_visits q.words c.cell st.valid,linesOne,Bind.bind,Except.bind,objects,
      visits,yes]
    rfl
end Doom.Proofs.E1M1LoggedCell
