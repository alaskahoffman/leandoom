import Doom.Proofs.E1M1AimControllerInputs
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1200000
namespace Doom.Proofs.E1M1AimControllerSetup
open Verification X86 X86Memory X86Control BlockSummary Collision
open E1M1CellWalkInvariant (Context)
open E1M1AimControllerEntry (entry)
open E1M1AimControllerInputs (layout SafeReads kept)
attribute [local irreducible] load32 store32

/-- Actual geometry/map reads plus the counter and each current traversal stamp. -/
def reads (q : Context) (s : X86Memory.State) (angle : Angle) : List Word :=
  E1M1AimRetryGeometry.reads (layout s angle) angle ++
    E1M1AimRetryData.mapReads q.base q.words ++ E1M1AimStampQuery.stampWords q.lines q.world.lines.size

/-- Transport the complete first-query setup contract from original memory.
The future register layout is explicit; current counter and freshness are
transported together, including wraparound, rather than assumed after entry. -/
theorem setup (q : Context) (s : X86Memory.State) (f : Option Flags)
    (thing : SolidThing) (angle : Angle)
    (regs : (entry s f).core.regs=(layout s angle).regs)
    (before : E1M1AimSetupEntry.Inputs q (layout s angle) thing angle (Fixed.ofInt 1024))
    (tables : ThrustTables s.memory) (safe : SafeReads s (reads q s angle)) :
    E1M1AimSetupEntry.Inputs q (entry s f).core thing angle (Fixed.ofInt 1024) := by
  have stack := congrFun regs 4
  have geoSafe : SafeReads s (E1M1AimRetryGeometry.reads (layout s angle) angle) := by
    intro a ha; exact safe a (List.mem_append_left _ (List.mem_append_left _ ha))
  have mapSafe : SafeReads s (E1M1AimRetryData.mapReads q.base q.words) := by
    intro a ha; exact safe a (List.mem_append_left _ (List.mem_append_right _ ha))
  have stamps : SafeReads s (E1M1AimStampQuery.stampWords q.lines q.world.lines.size) := by
    intro a ha; exact safe a (List.mem_append_right _ ha)
  have counter := kept s f angle _ stamps 0x13580 (by simp [E1M1AimStampQuery.stampWords])
  have stamp (j : Nat) (hj : j<q.world.lines.size) :=
    kept s f angle _ stamps (OriginalLineVisits.stamp q.lines j) (by
      apply List.mem_cons_of_mem
      exact List.mem_map.mpr ⟨j,List.mem_range.mpr hj,rfl⟩)
  refine ⟨E1M1AimRetryGeometry.geometry (layout s angle) (entry s f).core thing angle angle
    (Fixed.ofInt 1024) (Fixed.ofInt 1024) _ _ before.geometry tables
    (congrFun regs 0) stack ((congrFun regs 2).trans before.geometry.ray.angleReg)
    ((congrFun regs 3).trans before.geometry.ray.rangeReg) (kept s f angle _ geoSafe)
    before.geometry.ray.safe,
    stack.trans before.stack,?_,before.trace,before.lineCount,?_,
    E1M1AimControllerInputs.map s f angle _ _ _ _ _ regs before.map mapSafe,?_,
    E1M1AimRetryData.safe _ _ _ stack before.epochSafe,
    fun j hj => E1M1AimRetryData.safe _ _ _ stack (before.stampSafe j hj),?_,?_,?_⟩
  · rw [counter]; exact before.epoch
  · simpa only [E1M1PathMapSetup.Safe,OriginalPathInit.writes,E1M1PathMapQuery.withStack,
      write,ite_true,stack] using before.flagSafe
  · simpa only [stack] using before.cursorSafe
  · intro j hj; rw [stamp j hj,counter]; exact before.fresh j hj
  · simpa only [stack] using before.traceSafe
  · simpa only [stack] using before.activeSafe
end Doom.Proofs.E1M1AimControllerSetup
