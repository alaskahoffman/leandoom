import Doom.Proofs.E1M1NoiseGraph
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1600000
set_option linter.unusedSimpArgs false
namespace Doom.Proofs.E1M1NoiseGraphAllocation
open Verification X86 X86Memory X86Control BlockSummary
open E1M1NoiseLedger E1M1NoiseFootprint E1M1NoisePreservation E1M1NoiseAccounting
open E1M1NoiseAllocation E1M1NoiseMap E1M1NoiseMapGuards E1M1NoiseStack E1M1NoiseGraph

/-- Static placement of the graph's read-only words: line metadata, side-sector
pointers and the global side-table pointer. Regions may overlap each other;
they must be separate from every kind of storage this traversal can write.
This describes an allocation, not a proof that DOS startup produced it. -/
structure Storage (table : List SectorLines) (stack : Region) (base : Word)
    (edges : List Edge) (regions : List Region) : Prop where
  placed : ∀ address∈graphReads base edges, ∃ r∈regions, r.Contains address
  stack : ∀ r∈regions, r.Disjoint stack
  sectors : ∀ r∈regions, ∀ e∈table, r.Disjoint (sectorRegion e.address)
  globals : ∀ r∈regions, r.Disjoint E1M1NoiseAllocation.globals

private theorem Storage.stack_word {table stack base edges regions} (g : Storage table stack base edges regions)
    {a b : Word} (read : a∈graphReads base edges) (write : stack.Contains b) : Apart a b := by
  obtain ⟨r,hr,inside⟩ := g.placed a read
  exact Region.apart inside write (g.stack r hr)

private theorem Storage.sector_word {table stack base edges regions} (g : Storage table stack base edges regions)
    {a b : Word} {e : SectorLines} (read : a∈graphReads base edges) (member : e∈table)
    (write : (sectorRegion e.address).Contains b) : Apart a b := by
  obtain ⟨r,hr,inside⟩ := g.placed a read
  exact Region.apart inside write (g.sectors r hr e member)

private theorem Storage.global_word {table stack base edges regions} (g : Storage table stack base edges regions)
    {a b : Word} (read : a∈graphReads base edges) (write : b∈E1M1NoiseLineProgress.openingGlobals) : Apart a b := by
  obtain ⟨r,hr,inside⟩ := g.placed a read
  exact Region.apart inside (globals_contains write) (g.globals r hr)

/-- Sector visit stamps, costs and targets cannot overwrite any represented
line/side data, including another sector's edge records. -/
theorem Storage.protect_sector {table stack base edges regions s}
    (g : Storage table stack base edges regions) (a : Allocation table stack)
    (room : StackRoom stack s) (member : s.regs 0∈layout table) :
    Protect (graphReads base edges) (sectorWrites s) := by
  obtain ⟨e,he,input⟩ := List.mem_map.mp member
  intro x hx y hy
  change y∈stackWrites s++markWrites s at hy
  rcases List.mem_append.mp hy with hs|hm
  · apply g.stack_word hx (room y ?_)
    simpa [stackWrites,E1M1NoiseFrame.slots] using Or.inr hs
  · apply g.sector_word hx he
    simp only [markWrites,←input,List.mem_cons,List.not_mem_nil,or_false] at hm
    rcases hm with rfl|rfl|rfl
    · exact sector_contains (a.sectorBound e he) 66 (by decide)
    · exact sector_contains (a.sectorBound e he) 18 (by decide)
    · exact sector_contains (a.sectorBound e he) 22 (by decide)

/-- This includes the neighbor's scratch store at ESP and the recursive CALL's
return word, as well as the opening helper's stack and global stores. -/
theorem Storage.protect_line {table stack base edges regions s}
    (g : Storage table stack base edges regions) (room : StackRoom stack s) :
    Protect (graphReads base edges) (lineWrites s) := by
  intro x hx y hy
  simp only [lineWrites,List.mem_cons,List.not_mem_nil,or_false] at hy
  rcases hy with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals first
  | { apply g.stack_word hx; apply room; simp [E1M1NoiseFrame.slots] }
  | { apply g.global_word hx; simp [E1M1NoiseLineProgress.openingGlobals] }

private theorem skipped_sp {s : X86Control.State} (skip : (dispatch s).pc=0x27006) :
    (advance (dispatch s)).core.regs 4=s.core.regs 4 := by
  rw [advance_sp,dispatch,dispatch_sp]
  have no : (dispatch s).pc≠0x26f60 := by omega
  exact if_neg no

/-- One static placement certificate and the existing entry reserve protect
all graph words over the complete checked recursive trace. No per-node or
post-child graph protection is supplied. -/
theorem Storage.protect_trace {table stack base edges regions phase s t w n}
    (g : Storage table stack base edges regions) (a : Allocation table stack)
    (h : CheckedTrace (layout table) phase s t w n) (reserve : Reserve stack phase n s) :
    Protect (graphReads base edges) w := by
  induction h with
  | sectorDone s done safe => exact g.protect_sector a reserve.room safe.member
  | sectorMore s t w n more safe body ih =>
    have charge := sector_more_charge s.core more
    have parent : Reserve stack .sector (n+1) s := by simpa only [charge] using reserve
    exact protect_append (g.protect_sector a reserve.room safe.member) (ih parent.start)
  | lineDone s opening skip done safe => exact g.protect_line reserve.room
  | lineMore s t w n opening skip more safe body ih =>
    have next : Reserve stack .lines n (advance (dispatch s)) := by
      simpa only [Reserve,skipped_sp skip] using reserve
    exact protect_append (g.protect_line reserve.room) (ih next)
  | childDone s u w n opening call safe child ret done ih =>
    exact protect_append (g.protect_line reserve.room) (ih (reserve.child call))
  | childMore s u t w v n m opening call safe child ret more body ci bi =>
    have cr := (reserve.mono (Nat.le_add_right n m)).child call
    have br : Reserve stack .lines m (advance u) := by
      simpa only [Reserve,advance_sp,child_stack child call] using reserve.mono (Nat.le_add_left m n)
    exact protect_append (protect_append (g.protect_line reserve.room) (ci cr)) (bi br)

theorem Storage.preserves_graph {table stack base edges regions phase s t w n}
    (g : Storage table stack base edges regions) (a : Allocation table stack)
    (h : CheckedTrace (layout table) phase s t w n) (reserve : Reserve stack phase n s)
    (graph : GraphRep base edges s.core.memory) : GraphRep base edges t.core.memory :=
  graph.traversal h.trace (g.protect_trace a h reserve)

/-- The child-entry theorem no longer asks for graph-word separation. -/
theorem Storage.child_entry {table stack base edges regions sector s n}
    (g : Storage table stack base edges regions) (a : Allocation table stack)
    (reserve : Reserve stack .lines n s)
    (covered : Covered table edges) (closed : Closed table edges) (member : sector∈table)
    (map : MapRep table s.core.memory) (cursor : Cursor sector s.core)
    (graph : GraphRep base edges s.core.memory)
    (count : s.core.regs 1=0 ∨ s.core.regs 1=1) (call : (dispatch s).pc=0x26f60) :
    E1M1NoiseLedger.SectorSafe (layout table) (dispatch s).core ∧
    GraphRep base edges (dispatch s).core.memory ∧ MapRep table (dispatch s).core.memory :=
  E1M1NoiseGraph.child_entry a reserve covered closed member map cursor graph
    (g.protect_line reserve.room) count call

/-- Joined frame, map, graph and evaluator result. The caller supplies a static
layout, initial relations and entry space, not graph write-protection facts.
The existing finite CheckedTrace and its ledger guards still remain premises. -/
theorem Storage.sector_budget {table stack base edges regions s t w n}
    (g : Storage table stack base edges regions) (a : Allocation table stack)
    (h : CheckedTrace (layout table) .sector s t w n)
    (generation : Word) (xs : Ledger) (shape : addresses xs=layout table)
    (ledger : Represents generation s.core.memory xs)
    (low : stack.lo+56*table.length+20 ≤ (s.core.regs 4).toNat)
    (high : (s.core.regs 4).toNat+4 ≤ stack.hi) (bound : stack.hi≤2^32)
    (limit : Nat) (bounds : Bounded table limit) (map : MapRep table s.core.memory)
    (graph : GraphRep base edges s.core.memory) :
    Restored s.core t ∧ MapRep table t.core.memory ∧ GraphRep base edges t.core.memory ∧
    E1M1NoiseRecursive.eval (2*table.length*(limit+1)+1) .sector s=some t := by
  obtain ⟨restored,map',run⟩ := E1M1NoiseStack.sector_budget a h generation xs shape ledger low high bound limit bounds map
  have reserve := sector_reserve h generation xs shape ledger low high bound
  exact ⟨restored,map',g.preserves_graph a h reserve graph,run⟩

end Doom.Proofs.E1M1NoiseGraphAllocation
