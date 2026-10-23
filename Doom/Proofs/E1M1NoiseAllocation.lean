import Doom.Proofs.E1M1NoiseMapGuards
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1600000
set_option linter.unusedSimpArgs false
namespace Doom.Proofs.E1M1NoiseAllocation
open Verification X86 X86Memory X86Control BlockSummary
open E1M1NoiseLedger E1M1NoiseFootprint E1M1NoiseLineProgress E1M1NoiseMap

/-- Half-open byte region. Containment checks all four bytes and excludes address
wraparound. Earlier word-level proofs still support wrapping stacks. -/
structure Region where
  lo : Nat
  hi : Nat
  deriving DecidableEq, Repr

def Region.Contains (r : Region) (a : Word) : Prop :=
  r.lo ≤ a.toNat ∧ a.toNat+4 ≤ r.hi ∧ r.hi ≤ 2^32

def Region.Disjoint (r q : Region) : Prop := r.hi ≤ q.lo ∨ q.hi ≤ r.lo

instance (r : Region) (a : Word) : Decidable (r.Contains a) := by
  unfold Region.Contains; infer_instance
instance (r q : Region) : Decidable (r.Disjoint q) := by
  unfold Region.Disjoint; infer_instance

theorem Region.Disjoint.symm {r q : Region} (h : r.Disjoint q) : q.Disjoint r := Or.symm h

/-- Geometric separation implies the byte-level relation used by store32. -/
theorem Region.apart {r q : Region} {a b : Word} (ha : r.Contains a)
    (hb : q.Contains b) (separate : r.Disjoint q) : Apart a b := by
  intro i j eq
  have ii := i.isLt; have jj := j.isLt
  have same := congrArg BitVec.toNat eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at same
  unfold Region.Contains at ha hb
  unfold Region.Disjoint at separate
  omega

def sectorRegion (a : Word) : Region := ⟨a.toNat,a.toNat+86⟩
def arrayRegion (e : SectorLines) : Region := ⟨e.base.toNat,e.base.toNat+4*e.lines.length⟩
def globals : Region := ⟨0x2c02c,0x2c03c⟩
def counter : Region := ⟨0x13580,0x13584⟩

theorem sector_contains {a : Word} (bound : a.toNat+86 ≤ 2^32)
    (offset : Nat) (fits : offset+4 ≤ 86) :
    (sectorRegion a).Contains (a+BitVec.ofNat 32 offset) := by
  simp only [Region.Contains,sectorRegion,BitVec.toNat_add,BitVec.toNat_ofNat]
  have := a.isLt
  omega

theorem array_contains {e : SectorLines} (bound : e.base.toNat+4*e.lines.length ≤ 2^32)
    (i : Fin e.lines.length) : (arrayRegion e).Contains (entryAddress e i.val) := by
  simp only [Region.Contains,arrayRegion,entryAddress,BitVec.toNat_add,BitVec.toNat_ofNat]
  have := i.isLt; have := e.base.isLt
  omega

theorem globals_contains {a : Word} (h : a ∈ openingGlobals) : globals.Contains a := by
  simp only [openingGlobals,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at h
  rcases h with rfl|rfl|rfl|rfl <;> simp [globals,Region.Contains]

/-- Static allocation conditions, shared by every invocation. Each 86-byte
sector object, its line-pointer buffer, the stack arena and opening globals
must occupy separate storage. Duplicate descriptors for one sector are allowed.
This is a reusable layout certificate, not yet a certificate of DOS startup. -/
structure Allocation (table : List SectorLines) (stack : Region) : Prop where
  sectorBound : ∀ e ∈ table, e.address.toNat+86 ≤ 2^32
  arrayBound : ∀ e ∈ table, e.base.toNat+4*e.lines.length ≤ 2^32
  sectors : ∀ e ∈ table, ∀ f ∈ table, e.address≠f.address →
    (sectorRegion e.address).Disjoint (sectorRegion f.address)
  arraysSectors : ∀ e ∈ table, ∀ f ∈ table, (arrayRegion e).Disjoint (sectorRegion f.address)
  sectorsStack : ∀ e ∈ table, (sectorRegion e.address).Disjoint stack
  arraysStack : ∀ e ∈ table, (arrayRegion e).Disjoint stack
  sectorsGlobals : ∀ e ∈ table, (sectorRegion e.address).Disjoint globals
  arraysGlobals : ∀ e ∈ table, (arrayRegion e).Disjoint globals
  stackGlobals : stack.Disjoint globals
  counterSectors : ∀ e ∈ table, counter.Disjoint (sectorRegion e.address)
  counterStack : counter.Disjoint stack

/-- A local stack-range check, with room for the helper's five pushes and the
incoming word. No pairwise byte-separation tests occur in this condition. -/
def StackRoom (stack : Region) (s : X86Memory.State) : Prop :=
  ∀ a ∈ E1M1NoiseFrame.slots s, stack.Contains a

private theorem stack_mem {s : X86Memory.State} {a : Word} (h : a ∈ stackWrites s) :
    a ∈ E1M1NoiseFrame.slots s := by simpa [stackWrites,E1M1NoiseFrame.slots] using Or.inr h

private theorem sector_split (s : X86Memory.State) : sectorWrites s=stackWrites s++markWrites s := rfl
private theorem mark_contains {table stack} (a : Allocation table stack)
    {e : SectorLines} (he : e ∈ table) {s : X86Memory.State} (input : s.regs 0=e.address)
    {b : Word} (hb : b ∈ markWrites s) : (sectorRegion e.address).Contains b := by
  simp only [markWrites,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false,input] at hb
  rcases hb with rfl|rfl|rfl
  · exact sector_contains (a.sectorBound e he) 66 (by decide)
  · exact sector_contains (a.sectorBound e he) 18 (by decide)
  · exact sector_contains (a.sectorBound e he) 22 (by decide)

private theorem read_contains {table stack} (a : Allocation table stack)
    {e : SectorLines} (he : e ∈ table) {b : Word} (hb : b ∈ markReads e.address) :
    (sectorRegion e.address).Contains b := by
  simp only [markReads,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hb
  rcases hb with rfl|rfl
  · exact sector_contains (a.sectorBound e he) 66 (by decide)
  · exact sector_contains (a.sectorBound e he) 18 (by decide)

/-- Read-only map words are either metadata inside their sector or line-array
entries. Keeping this distinction allows fields in the same sector to coexist. -/
private theorem map_location {table stack} (a : Allocation table stack) {b : Word}
    (hb : b ∈ mapReads table) : ∃ e ∈ table,
      (b=e.address+78 ∨ b=e.address+82) ∨ (arrayRegion e).Contains b := by
  obtain ⟨e,he,hb⟩ := List.mem_flatMap.mp hb
  refine ⟨e,he,?_⟩
  simp only [reads,List.mem_append,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hb
  rcases hb with metadata|arr
  · exact Or.inl metadata
  · obtain ⟨i,hi,rfl⟩ := List.mem_map.mp arr
    exact Or.inr (array_contains (a.arrayBound e he) ⟨i,List.mem_range.mp hi⟩)

private theorem metadata_contains {table stack} (a : Allocation table stack)
    {e : SectorLines} (he : e∈table) {b : Word} (hb : b=e.address+78 ∨ b=e.address+82) :
    (sectorRegion e.address).Contains b := by
  rcases hb with rfl|rfl
  · exact sector_contains (a.sectorBound e he) 78 (by decide)
  · exact sector_contains (a.sectorBound e he) 82 (by decide)

private theorem map_apart_stack {table stack} (a : Allocation table stack)
    {b c : Word} (hb : b∈mapReads table) (hc : stack.Contains c) : Apart b c := by
  obtain ⟨e,he,metadata|arr⟩ := (map_location a) hb
  · exact Region.apart ((metadata_contains a) he metadata) hc (a.sectorsStack e he)
  · exact Region.apart arr hc (a.arraysStack e he)

private theorem map_apart_globals {table stack} (a : Allocation table stack)
    {b c : Word} (hb : b∈mapReads table) (hc : c∈openingGlobals) : Apart b c := by
  obtain ⟨e,he,metadata|arr⟩ := (map_location a) hb
  · exact Region.apart ((metadata_contains a) he metadata) (globals_contains hc) (a.sectorsGlobals e he)
  · exact Region.apart arr (globals_contains hc) (a.arraysGlobals e he)

private theorem metadata_apart_marks (address : Word) {b c : Word}
    (hb : b=address+78 ∨ b=address+82)
    (hc : c=address+66 ∨ c=address+18 ∨ c=address+22) : Apart b c := by
  rcases hb with rfl|rfl <;> rcases hc with rfl|rfl|rfl <;>
    intro i j same <;>
    rw [BitVec.add_assoc,BitVec.add_assoc] at same <;>
    have eq := congrArg BitVec.toNat ((BitVec.add_right_inj address).mp same) <;>
    simp [BitVec.toNat_add,BitVec.toNat_ofNat] at eq <;>
    have ii := i.isLt <;> have jj := j.isLt <;> omega

/-- Every sector update protects the whole table, including its own metadata. -/
theorem Allocation.map_sector {table stack} (a : Allocation table stack) {s : X86Memory.State}
    (room : StackRoom stack s) (member : s.regs 0 ∈ E1M1NoiseMapGuards.layout table) :
    Protect (mapReads table) (sectorWrites s) := by
  obtain ⟨e,he,input⟩ := List.mem_map.mp member
  intro b hb c hc
  rw [sector_split] at hc
  rcases List.mem_append.mp hc with hs|hm
  · exact (map_apart_stack a) hb (room c (stack_mem hs))
  · obtain ⟨f,hf,metadata|arr⟩ := (map_location a) hb
    · by_cases eq : f.address=e.address
      · apply metadata_apart_marks e.address (by simpa [eq] using metadata)
        simpa [markWrites,←input] using hm
      · exact Region.apart ((metadata_contains a) hf metadata) ((mark_contains a) he input.symm hm)
          (a.sectors f hf e he eq)
    · exact Region.apart arr ((mark_contains a) he input.symm hm) (a.arraysSectors f hf e he)

private theorem line_location {s : X86Memory.State} {b : Word} (hb : b∈lineWrites s) :
    b∈E1M1NoiseFrame.slots s ∨ b∈openingGlobals := by
  simp only [lineWrites,E1M1NoiseFrame.slots,openingGlobals,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at *
  rcases hb with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> simp

theorem Allocation.map_line {table stack} (a : Allocation table stack) {s : X86Memory.State}
    (room : StackRoom stack s) : Protect (mapReads table) (lineWrites s) := by
  intro b hb c hc
  rcases line_location hc with hs|hg
  · exact (map_apart_stack a) hb (room c hs)
  · exact (map_apart_globals a) hb hg

theorem Allocation.dispatch_safe {table stack} (a : Allocation table stack) {s : X86Memory.State}
    (room : StackRoom stack s) : DispatchSafe s := by
  intro b hb c hc
  apply Region.apart (room b ?_) (globals_contains hc) a.stackGlobals
  simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hb
  rcases hb with rfl|rfl <;> simp [E1M1NoiseFrame.slots]

/-- An ordinary downward-growing stack needs one lower and one upper bound. -/
theorem stack_room {stack : Region} {s : X86Memory.State}
    (low : stack.lo+20 ≤ (s.regs 4).toNat)
    (high : (s.regs 4).toNat+4 ≤ stack.hi) (bound : stack.hi ≤ 2^32) : StackRoom stack s := by
  intro b hb
  simp only [E1M1NoiseFrame.slots,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hb
  rcases hb with rfl|rfl|rfl|rfl|rfl|rfl <;>
    simp [Region.Contains,BitVec.toNat_sub] <;> omega

private theorem counter_contains : counter.Contains (0x13580#32) := by
  simp [counter,Region.Contains]
private theorem counter_globals : counter.Disjoint globals := by
  simp [counter,globals,Region.Disjoint]

theorem Allocation.ledger_sector {table stack} (a : Allocation table stack) {s : X86Memory.State}
    (room : StackRoom stack s) (member : s.regs 0 ∈ E1M1NoiseMapGuards.layout table)
    (count : s.regs 2=(0#32) ∨ s.regs 2=(1#32)) :
    E1M1NoiseLedger.SectorSafe (E1M1NoiseMapGuards.layout table) s := by
  obtain ⟨e,he,input⟩ := List.mem_map.mp member
  refine ⟨member,count,?_,?_,?_⟩
  · intro address ha b hb c hc
    obtain ⟨f,hf,rfl⟩ := List.mem_map.mp ha
    exact Region.apart (read_contains a hf hb) (room c (stack_mem hc)) (a.sectorsStack f hf)
  · intro b hb
    rw [sector_split] at hb
    rcases List.mem_append.mp hb with hs|hm
    · exact Region.apart counter_contains (room b (stack_mem hs)) a.counterStack
    · exact Region.apart counter_contains (mark_contains a he input.symm hm) (a.counterSectors e he)
  · intro address ha different b hb c hc
    obtain ⟨f,hf,rfl⟩ := List.mem_map.mp ha
    exact Region.apart (read_contains a hf hb) (mark_contains a he input.symm hc)
      (a.sectors f hf e he (by simpa [input] using different))

theorem Allocation.ledger_line {table stack} (a : Allocation table stack) {s : X86Memory.State}
    (room : StackRoom stack s) : LineSafe (E1M1NoiseMapGuards.layout table) s := by
  constructor
  · intro b hb
    rcases line_location hb with hs|hg
    · exact Region.apart counter_contains (room b hs) a.counterStack
    · exact Region.apart counter_contains (globals_contains hg) counter_globals
  · intro address ha b hb c hc
    obtain ⟨e,he,rfl⟩ := List.mem_map.mp ha
    rcases line_location hc with hs|hg
    · exact Region.apart (read_contains a he hb) (room c hs) (a.sectorsStack e he)
    · exact Region.apart (read_contains a he hb) (globals_contains hg) (a.sectorsGlobals e he)

/-- After the five prologue stores, writes may use a lower stack region,
sector storage or opening globals. The current frame is deliberately excluded.
Establishing this footprint for all recursive executions remains a separate
stack-depth invariant; it is not assumed to follow from allocation alone. -/
def BelowFrame (table : List SectorLines) (entry : X86Memory.State) (w : List Word) : Prop :=
  ∀ b ∈ w.drop 5,
    (Region.mk 0 ((entry.regs 4).toNat-20)).Contains b ∨
    (∃ e ∈ table, (sectorRegion e.address).Contains b) ∨ globals.Contains b

/-- A child's complete footprint restores its incoming frame using region
bounds, without pairwise separation assumptions for every nested write. -/
theorem Allocation.frame_safe {table stack} (a : Allocation table stack) {entry : X86Memory.State}
    (room : StackRoom stack entry) (low : 20 ≤ (entry.regs 4).toNat)
    (footprint : BelowFrame table entry w) : E1M1NoisePreservation.SectorSafe entry w := by
  intro b hb c hc
  rcases footprint c hc with below|⟨e,he,inside⟩|inside
  · have placed : (Region.mk ((entry.regs 4).toNat-20) stack.hi).Contains b := by
      have inStack := room b hb
      simp only [E1M1NoiseFrame.slots,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hb
      rcases hb with rfl|rfl|rfl|rfl|rfl|rfl <;>
        simp [Region.Contains,BitVec.toNat_sub] at inStack ⊢ <;> omega
    exact Region.apart placed below (Or.inr (Nat.le_refl _))
  · exact Region.apart (room b hb) inside (a.sectorsStack e he).symm
  · exact Region.apart (room b hb) inside a.stackGlobals

theorem Allocation.restores {table stack s t w n} (a : Allocation table stack)
    (trace : E1M1NoiseAccounting.CheckedTrace (E1M1NoiseMapGuards.layout table) .sector s t w n)
    (room : StackRoom stack s.core) (low : 20 ≤ (s.core.regs 4).toNat)
    (footprint : BelowFrame table s.core w) : E1M1NoisePreservation.Restored s.core t :=
  trace.restores_sector (a.frame_safe room low footprint)

/-- Allocation-derived guards feed the existing original-instruction progress
proof directly. The resulting cursor is not an assumed postcondition. -/
theorem Allocation.skip_step {table stack e s} (a : Allocation table stack)
    (room : StackRoom stack s.core) (member : e∈table) (rep : MapRep table s.core.memory)
    (cursor : Cursor e s.core) (small : e.lines.length≤2147483647)
    (more : (E1M1NoisePreservation.advance (E1M1NoisePreservation.dispatch s)).pc=0x26fa8) :
    MapRep table (E1M1NoisePreservation.advance (E1M1NoisePreservation.dispatch s)).core.memory ∧
    Cursor e (E1M1NoisePreservation.advance (E1M1NoisePreservation.dispatch s)).core ∧
    remaining (E1M1NoisePreservation.advance (E1M1NoisePreservation.dispatch s))+1=remaining s :=
  E1M1NoiseMap.skip_step member rep cursor small (a.dispatch_safe room) (a.map_line room) more

/-- Resume a checked child using allocation-derived saved-frame protection.
Child map preservation and a below-frame footprint are still explicit inputs. -/
theorem Allocation.child_step {table stack e s u w n} (a : Allocation table stack)
    (room : StackRoom stack s.core) (member : e∈table) (rep : MapRep table s.core.memory)
    (cursor : Cursor e s.core) (small : e.lines.length≤2147483647)
    (child : E1M1NoiseAccounting.CheckedTrace (E1M1NoiseMapGuards.layout table) .sector
      (E1M1NoisePreservation.dispatch s) u w n)
    (childRoom : StackRoom stack (E1M1NoisePreservation.dispatch s).core)
    (low : 20 ≤ ((E1M1NoisePreservation.dispatch s).core.regs 4).toNat)
    (footprint : BelowFrame table (E1M1NoisePreservation.dispatch s).core w)
    (mapSafe : Protect (mapReads table) w)
    (more : (E1M1NoisePreservation.advance u).pc=0x26fa8) :
    MapRep table (E1M1NoisePreservation.advance u).core.memory ∧
    Cursor e (E1M1NoisePreservation.advance u).core ∧
    remaining (E1M1NoisePreservation.advance u)+1=remaining s :=
  E1M1NoiseMap.child_step member rep cursor small (a.dispatch_safe room) child
    (a.frame_safe childRoom low footprint)
    (E1M1NoiseMapGuards.protect_append (a.map_line room) mapSafe) more

end Doom.Proofs.E1M1NoiseAllocation
