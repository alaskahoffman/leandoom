import Doom.Proofs.E1M1NoiseMap
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1600000
namespace Doom.Proofs.E1M1NoiseMapGuards
open Verification X86 X86Memory X86Control E1M1NoisePreservation E1M1NoiseFootprint
open E1M1NoiseAccounting E1M1NoiseLedger E1M1NoiseLineProgress E1M1NoiseFuelBound E1M1NoiseMap

def layout (table : List SectorLines) := table.map SectorLines.address

/-- Memory-separation annotations only. No line counts, successor cursors,
remaining-line decreases or post-child map relations are premises here.
The existing finite checked trace is still supplied. -/
inductive MemoryGuards (table : List SectorLines) : {phase : E1M1NoiseRecursive.Phase} →
    {s t : X86Control.State} → {w : List Word} → {n : Nat} →
    CheckedTrace (layout table) phase s t w n → Prop
  | sectorDone (s done safe) (mapSafe : Protect (mapReads table) (sectorWrites s.core)) :
      MemoryGuards table (CheckedTrace.sectorDone s done safe)
  | sectorMore (s t w n more safe) (body : CheckedTrace (layout table) .lines (startLines s) t w n)
      (mapSafe : Protect (mapReads table) (sectorWrites s.core)) (rest : MemoryGuards table body) :
      MemoryGuards table (CheckedTrace.sectorMore s t w n more safe body)
  | lineDone (s opening skip done safe) (mapSafe : Protect (mapReads table) (lineWrites s.core)) :
      MemoryGuards table (CheckedTrace.lineDone s opening skip done safe)
  | lineMore (s t w n opening skip more safe)
      (body : CheckedTrace (layout table) .lines (advance (dispatch s)) t w n)
      (mapSafe : Protect (mapReads table) (lineWrites s.core)) (regs : DispatchSafe s.core)
      (rest : MemoryGuards table body) :
      MemoryGuards table (CheckedTrace.lineMore s t w n opening skip more safe body)
  | childDone (s u w n opening call safe)
      (child : CheckedTrace (layout table) .sector (dispatch s) u w n) (ret done)
      (mapSafe : Protect (mapReads table) (lineWrites s.core)) (rest : MemoryGuards table child) :
      MemoryGuards table (CheckedTrace.childDone s u w n opening call safe child ret done)
  | childMore (s u t w v n m opening call safe)
      (child : CheckedTrace (layout table) .sector (dispatch s) u w n) (ret more)
      (body : CheckedTrace (layout table) .lines (advance u) t v m)
      (mapSafe : Protect (mapReads table) (lineWrites s.core)) (regs : DispatchSafe s.core)
      (frame : E1M1NoisePreservation.SectorSafe (dispatch s).core w)
      (childGuards : MemoryGuards table child) (bodyGuards : MemoryGuards table body) :
      MemoryGuards table (CheckedTrace.childMore s u t w v n m opening call safe child ret more body)

theorem protect_append {reads a b} (ha : Protect reads a) (hb : Protect reads b) : Protect reads (a++b) := by
  intro x hx y hy
  rcases List.mem_append.mp hy with h|h
  · exact ha x hx y h
  · exact hb x hx y h

theorem MemoryGuards.protected {table phase s t w n} {h : CheckedTrace (layout table) phase s t w n}
    (guards : MemoryGuards table h) : Protect (mapReads table) w := by
  induction guards with
  | sectorDone s done safe mapSafe => exact mapSafe
  | sectorMore s t w n more safe body mapSafe rest ih => exact protect_append mapSafe ih
  | lineDone s opening skip done safe mapSafe => exact mapSafe
  | lineMore s t w n opening skip more safe body mapSafe regs rest ih => exact protect_append mapSafe ih
  | childDone s u w n opening call safe child ret done mapSafe rest ih => exact protect_append mapSafe ih
  | childMore s u t w v n m opening call safe child ret more body mapSafe regs frame cg bg ci bi =>
    exact protect_append (protect_append mapSafe ci) bi

def Entry (table : List SectorLines) : E1M1NoiseRecursive.Phase → X86Control.State → Prop
  | .sector,_ => True
  | .lines,s => ∃ e, e ∈ table ∧ Cursor e s.core

/-- All numeric loop guards follow from a shared map representation, a live
entry cursor and local memory protection. Recursive outputs are derived. -/
theorem MemoryGuards.loops {table phase s t w n} {h : CheckedTrace (layout table) phase s t w n}
    (guards : MemoryGuards table h) (limit : Nat) (bounds : Bounded table limit)
    (rep : MapRep table s.core.memory) (entry : Entry table phase s) : LoopGuards limit h := by
  induction guards with
  | sectorDone s done safe mapSafe => exact .sectorDone s done safe
  | sectorMore s t w n more safe body mapSafe rest ih =>
    obtain ⟨e,member,address⟩ := List.mem_map.mp safe.member
    have started := start_step member rep address.symm bounds mapSafe more
    exact .sectorMore s t w n more safe body started.2.2 (ih started.1 ⟨e,member,started.2.1⟩)
  | lineDone s opening skip done safe mapSafe => exact .lineDone s opening skip done safe
  | lineMore s t w n opening skip more safe body mapSafe regs rest ih =>
    obtain ⟨e,member,cursor⟩ := entry
    have step := skip_step member rep cursor (bounds e member).2 regs mapSafe more
    exact .lineMore s t w n opening skip more safe body (by omega) (ih step.1 ⟨e,member,step.2.1⟩)
  | childDone s u w n opening call safe child ret done mapSafe rest ih =>
    obtain ⟨e,member,cursor⟩ := entry
    have active : 0<remaining s := by
      rw [cursor.remaining_eq (rep e member) (bounds e member).2]
      have := cursor.live
      omega
    exact .childDone s u w n opening call safe child ret done active (ih (rep.dispatch_step mapSafe) trivial)
  | childMore s u t w v n m opening call safe child ret more body mapSafe regs frame cg bg ci bi =>
    obtain ⟨e,member,cursor⟩ := entry
    have step := child_step member rep cursor (bounds e member).2 regs child frame
      (protect_append mapSafe cg.protected) more
    exact .childMore s u t w v n m opening call safe child ret more body (by omega)
      (ci (rep.dispatch_step mapSafe) trivial) (bi step.1 ⟨e,member,step.2.1⟩)

/-- The complete table, including every line-array entry, survives all nesting. -/
theorem MemoryGuards.preserves_map {table phase s t w n} {h : CheckedTrace (layout table) phase s t w n}
    (guards : MemoryGuards table h) (rep : MapRep table s.core.memory) : MapRep table t.core.memory :=
  rep.traversal h.trace guards.protected

/-- No separately supplied numeric LoopGuards or per-node remaining-line bounds. -/
theorem sector_budget {table s t w n} (h : CheckedTrace (layout table) .sector s t w n)
    (guards : MemoryGuards table h) (limit : Nat) (bounds : Bounded table limit)
    (map : MapRep table s.core.memory) (generation : Word) (xs : Ledger)
    (shape : addresses xs=layout table) (rep : Represents generation s.core.memory xs) :
    E1M1NoiseRecursive.eval (2*table.length*(limit+1)+1) .sector s=some t := by
  have result := E1M1NoiseFuelBound.sector_budget h (guards.loops limit bounds map trivial) generation xs shape rep
  simpa only [layout,List.length_map] using result
end Doom.Proofs.E1M1NoiseMapGuards
