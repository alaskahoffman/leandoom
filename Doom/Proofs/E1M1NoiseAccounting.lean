import Doom.Proofs.E1M1NoiseLedger
import Doom.Proofs.E1M1NoiseTraceFuel
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1600000
namespace Doom.Proofs.E1M1NoiseAccounting
open Verification X86 X86Memory X86Control BlockSummary E1M1NoiseRecursive E1M1NoiseFootprint
open E1M1NoisePreservation E1M1NoiseLedger

/-- The existing original-machine traversal with local address/count guards and
an admission count. Children carry their own derivation, not an assumed ledger
postcondition. This is a finite execution relation, not yet a termination proof. -/
inductive CheckedTrace (layout : List Word) :
    Phase → X86Control.State → X86Control.State → List Word → Nat → Prop
  | sectorDone (s) (done : (sector s).pc=0x27011)
      (safe : E1M1NoiseLedger.SectorSafe layout s.core) :
      CheckedTrace layout .sector s (finish (sector s)) (sectorWrites s.core) (charge s.core)
  | sectorMore (s t w n) (more : (sector s).pc=0x26fa6)
      (safe : E1M1NoiseLedger.SectorSafe layout s.core)
      (body : CheckedTrace layout .lines (startLines s) t w n) :
      CheckedTrace layout .sector s t (sectorWrites s.core++w) (n+charge s.core)
  | lineDone (s) (opening : OpeningReturns s.core) (skip : (dispatch s).pc=0x27006)
      (done : (advance (dispatch s)).pc=0x27011) (safe : LineSafe layout s.core) :
      CheckedTrace layout .lines s (finish (advance (dispatch s))) (lineWrites s.core) 0
  | lineMore (s t w n) (opening : OpeningReturns s.core) (skip : (dispatch s).pc=0x27006)
      (more : (advance (dispatch s)).pc=0x26fa8) (safe : LineSafe layout s.core)
      (body : CheckedTrace layout .lines (advance (dispatch s)) t w n) :
      CheckedTrace layout .lines s t (lineWrites s.core++w) n
  | childDone (s u w n) (opening : OpeningReturns s.core) (call : (dispatch s).pc=0x26f60)
      (safe : LineSafe layout s.core) (child : CheckedTrace layout .sector (dispatch s) u w n)
      (ret : u.pc=0x27006) (done : (advance u).pc=0x27011) :
      CheckedTrace layout .lines s (finish (advance u)) (lineWrites s.core++w) n
  | childMore (s u t w v n m) (opening : OpeningReturns s.core) (call : (dispatch s).pc=0x26f60)
      (safe : LineSafe layout s.core) (child : CheckedTrace layout .sector (dispatch s) u w n)
      (ret : u.pc=0x27006) (more : (advance u).pc=0x26fa8)
      (body : CheckedTrace layout .lines (advance u) t v m) :
      CheckedTrace layout .lines s t (lineWrites s.core++w++v) (n+m)

/-- Forgetting the guards/count gives precisely the previous machine trace. -/
theorem CheckedTrace.trace {layout phase s t w n} (h : CheckedTrace layout phase s t w n) :
    Trace phase s t w := by
  induction h with
  | sectorDone s done _ => exact .sectorDone s done
  | sectorMore s t w n more _ _ ih => exact .sectorMore s t w more ih
  | lineDone s opening skip done _ => exact .lineDone s opening skip done
  | lineMore s t w n opening skip more _ _ ih => exact .lineMore s t w opening skip more ih
  | childDone s u w n opening call _ _ ret done ih => exact .childDone s u w opening call ih ret done
  | childMore s u t w v n m opening call _ _ ret more _ child body =>
    exact .childMore s u t w v opening call child ret more body

/-- A ledger at entry is enough: local machine writes and recursive induction
construct the ledger at exit, with every admission paid from its credit. -/
theorem CheckedTrace.accounting {layout phase s t w n} (h : CheckedTrace layout phase s t w n)
    (generation : Word) (xs : Ledger) (shape : addresses xs=layout)
    (rep : Represents generation s.core.memory xs) :
    ∃ ys, addresses ys=layout ∧ Represents generation t.core.memory ys ∧ n+credit ys≤credit xs := by
  induction h generalizing xs with
  | sectorDone s done safe =>
    obtain ⟨ys,shape',rep',bound⟩ := sector_step layout generation s.core xs shape rep safe
    exact ⟨ys,shape',rep',by omega⟩
  | sectorMore s t w n more safe body ih =>
    obtain ⟨ys,shape',rep',bound⟩ := sector_step layout generation s.core xs shape rep safe
    obtain ⟨zs,shape'',rep'',bound'⟩ := ih ys shape' rep'
    exact ⟨zs,shape'',rep'',by omega⟩
  | lineDone s opening skip done safe =>
    exact ⟨xs,shape,line_step layout generation s.core xs shape rep safe,by omega⟩
  | lineMore s t w n opening skip more safe body ih =>
    exact ih xs shape (line_step layout generation s.core xs shape rep safe)
  | childDone s u w n opening call safe child ret done ih =>
    exact ih xs shape (line_step layout generation s.core xs shape rep safe)
  | childMore s u t w v n m opening call safe child ret more body childIH bodyIH =>
    obtain ⟨ys,shape',rep',bound⟩ := childIH xs shape (line_step layout generation s.core xs shape rep safe)
    obtain ⟨zs,shape'',rep'',bound'⟩ := bodyIH ys shape' rep'
    exact ⟨zs,shape'',rep'',by omega⟩

theorem CheckedTrace.admission_bound {layout phase s t w n} (h : CheckedTrace layout phase s t w n)
    (generation : Word) (xs : Ledger) (shape : addresses xs=layout)
    (rep : Represents generation s.core.memory xs) : n≤2*layout.length := by
  obtain ⟨ys,_,_,bound⟩ := h.accounting generation xs shape rep
  have initial := E1M1NoiseVisits.potential_bound (xs.map Prod.snd)
  have length : xs.length=layout.length := by simpa [addresses] using congrArg List.length shape
  simp only [List.length_map] at initial
  change n+credit ys≤E1M1NoiseVisits.potential (xs.map Prod.snd) at bound
  omega

/-- The same execution still has the exact write footprint and return behavior
proved earlier; adding the ledger does not replace the machine semantics. -/
theorem CheckedTrace.frame {layout phase s t w n} (h : CheckedTrace layout phase s t w n) :
    PlayerHeight.Frame s.core.memory t.core.memory w := h.trace.frame

theorem CheckedTrace.restores_sector {layout s t w n} (h : CheckedTrace layout .sector s t w n)
    (safe : E1M1NoisePreservation.SectorSafe s.core w) : Restored s.core t :=
  h.trace.restores_sector safe
theorem CheckedTrace.evaluates {layout phase s t w n} (h : CheckedTrace layout phase s t w n) :
    ∃ k, eval k phase s=some t := E1M1NoiseTraceFuel.trace_evaluates h.trace

theorem CheckedTrace.execution {layout phase s t w n} (h : CheckedTrace layout phase s t w n)
    (pc : s.pc=phase.pc) : ∃ k, Runs (bound k) s t := by
  obtain ⟨k,run⟩ := h.evaluates
  exact ⟨k,E1M1NoiseRecursive.execution k phase s t pc run⟩
end Doom.Proofs.E1M1NoiseAccounting
