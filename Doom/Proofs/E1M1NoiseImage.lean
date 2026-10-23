import Doom.Proofs.E1M1NoiseTopology
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 2400000
set_option linter.unusedSimpArgs false
namespace Doom.Proofs.E1M1NoiseImage
open Verification X86 X86Memory X86Control BlockSummary
open E1M1NoiseMap E1M1NoiseGraph E1M1NoiseMapGuards E1M1NoiseTopology
open E1M1NoiseAllocation E1M1NoiseGraphAllocation E1M1NoiseLedger E1M1NoisePreservation E1M1NoiseRecursive

abbrev Patch := List (Word × BitVec 8)
def putByte (m : Memory) (p : Word × BitVec 8) : Memory := fun x => if x=p.1 then p.2 else m x
def applyPatch (p : Patch) (m : Memory) : Memory := p.foldl putByte m
/-- Shared side pointers may be written repeatedly, but overlapping writes must
agree byte for byte. This is a finite condition on the emitted write plan. -/
def Consistent (p : Patch) : Prop := ∀ x∈p, ∀ y∈p, x.1=y.1 → x.2=y.2
def Realizes (p : Patch) (m : Memory) : Prop := ∀ x∈p, m x.1=x.2
instance (p : Patch) : Decidable (Consistent p) := by unfold Consistent; infer_instance

private theorem retains {p : Patch} {m : Memory} {a : Word} {v : BitVec 8}
    (initial : m a=v) (agree : ∀ x∈p, x.1=a → x.2=v) : applyPatch p m a=v := by
  induction p generalizing m with
  | nil => exact initial
  | cons x xs ih =>
    apply ih (m:=putByte m x)
    · by_cases same : a=x.1
      · simp [putByte,same,agree x (by simp) same.symm]
      · simpa [putByte,same] using initial
    · intro y hy; exact agree y (by simp [hy])

theorem realizes {p : Patch} (consistent : Consistent p) (m : Memory) : Realizes p (applyPatch p m) := by
  induction p generalizing m with
  | nil => simp [Realizes]
  | cons x xs ih =>
    have tail : Consistent xs := fun a ha b hb => consistent a (by simp [ha]) b (by simp [hb])
    intro y hy
    rcases List.mem_cons.mp hy with eq|hy
    · subst y
      exact retains (m:=putByte m x) (a:=x.1) (v:=x.2) (by simp [putByte]) (fun y hy same => consistent y (by simp [hy]) x (by simp) same)
    · exact ih tail (putByte m x) y hy

/-- Bytes outside the initializer's sparse footprint retain their original
values; no unspecified payload byte is silently filled with zero. -/
theorem frame (p : Patch) (m : Memory) (a : Word) (outside : ∀ x∈p, x.1≠a) :
    applyPatch p m a=m a :=
  retains rfl (fun x hx eq => False.elim (outside x hx eq))

def half (a : Word) (v : BitVec 16) : Patch := [(a,v.extractLsb' 0 8),(a+1,v.extractLsb' 8 8)]
def word (a v : Word) : Patch :=
  [(a,v.extractLsb' 0 8),(a+1,v.extractLsb' 8 8),(a+2,v.extractLsb' 16 8),(a+3,v.extractLsb' 24 8)]

theorem read_half {m a v} (h : Realizes (half a v) m) : load16 m a=v := by
  have lo := h _ (by simp [half] : (a,v.extractLsb' 0 8)∈half a v)
  have hi := h _ (by simp [half] : (a+1,v.extractLsb' 8 8)∈half a v)
  simp only [load16,lo,hi,BitVec.extractLsb'_append_extractLsb']

theorem read_word {m a v} (h : Realizes (word a v) m) : load32 m a=v := by
  have b0 := h _ (by simp [word] : (a,v.extractLsb' 0 8)∈word a v)
  have b1 := h _ (by simp [word] : (a+1,v.extractLsb' 8 8)∈word a v)
  have b2 := h _ (by simp [word] : (a+2,v.extractLsb' 16 8)∈word a v)
  have b3 := h _ (by simp [word] : (a+3,v.extractLsb' 24 8)∈word a v)
  simp only [load32,b0,b1,b2,b3]
  rw [BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (by decide : 24=16+8),
    BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (by decide : 8=0+8)]
  exact BitVec.extractLsb'_append_extractLsb'

/-- The word emitter has the same effect as the existing x86 store32 model,
including unaligned and wrapping addresses. -/
theorem apply_word (m : Memory) (a v : Word) : applyPatch (word a v) m=store32 m a v := by
  funext x
  have distinct (i j : Fin 4) (ne : i≠j) : a+BitVec.ofNat 32 i.val≠a+BitVec.ofNat 32 j.val := by
    intro eq
    have h := congrArg BitVec.toNat ((BitVec.add_right_inj a).mp eq)
    have ii := i.isLt; have jj := j.isLt
    simp only [BitVec.toNat_ofNat] at h
    apply ne; apply Fin.ext; omega
  have h01 := distinct 0 1 (by decide)
  have h02 := distinct 0 2 (by decide)
  have h03 := distinct 0 3 (by decide)
  have h12 := distinct 1 2 (by decide)
  have h13 := distinct 1 3 (by decide)
  have h23 := distinct 2 3 (by decide)
  simp only [applyPatch,word,List.foldl,putByte,store32]
  by_cases e0 : x=a <;> by_cases e1 : x=a+1 <;> by_cases e2 : x=a+2 <;> by_cases e3 : x=a+3 <;> simp_all

private theorem Realizes.subset {p q m} (h : Realizes p m) (sub : ∀ x∈q, x∈p) : Realizes q m :=
  fun x hx => h x (sub x hx)
private theorem Realizes.left {p q m} (h : Realizes (p++q) m) : Realizes p m := h.subset (by simp_all)
private theorem Realizes.right {p q m} (h : Realizes (p++q) m) : Realizes q m := h.subset (by simp_all)

def sectorPatch (e : SectorLines) : Patch :=
  word (e.address+78) (BitVec.ofNat 32 e.lines.length) ++ word (e.address+82) e.base ++
  (List.finRange e.lines.length).flatMap (fun i => word (entryAddress e i.val) e.lines[i.val])
def mapPatch (table : List SectorLines) : Patch := table.flatMap sectorPatch

local instance (e : Edge) : Decidable e.two := by unfold Edge.two; infer_instance

def edgePatch (base : Word) (e : Edge) : Patch :=
  [(e.line+16,e.flags)] ++ half (e.line+22) e.frontIndex ++ half (e.line+24) e.backIndex ++
  word (sideAddress base e.frontIndex) e.front ++
  (if e.two then word (sideAddress base e.backIndex) e.back else [])
def graphPatch (base : Word) (edges : List Edge) : Patch := word 0x2c118 base ++ edges.flatMap (edgePatch base)
/-- Relevant-field initializer specification, not a claim about the DOS loader's
control flow or unmodeled sector heights/textures. Side writes can be shared. -/
def image (table : List SectorLines) (base : Word) (edges : List Edge) : Patch :=
  mapPatch table ++ graphPatch base edges

theorem map_rep {table m} (h : Realizes (mapPatch table) m) : MapRep table m := by
  intro e he
  have one : Realizes (sectorPatch e) m := h.subset (fun x hx => List.mem_flatMap.mpr ⟨e,he,hx⟩)
  change Realizes ((word _ _ ++ word _ _) ++ _) m at one
  refine ⟨read_word one.left.left,read_word one.left.right,?_⟩
  intro i
  apply read_word
  exact one.right.subset (fun x hx => List.mem_flatMap.mpr ⟨i,by simp,hx⟩)

theorem graph_rep {base edges m} (h : Realizes (graphPatch base edges) m) : GraphRep base edges m := by
  refine ⟨read_word h.left,?_⟩
  intro e he
  have one : Realizes (edgePatch base e) m := h.right.subset (fun x hx => List.mem_flatMap.mpr ⟨e,he,hx⟩)
  change Realizes (((([(e.line+16,e.flags)] ++ half _ _) ++ half _ _) ++ word _ _) ++ _) m at one
  refine ⟨one.left.left.left.left (e.line+16,e.flags) (by simp),read_half one.left.left.left.right,
    read_half one.left.left.right,read_word one.left.right,?_⟩
  intro two
  have last := one.right
  simp only [if_pos two] at last
  exact read_word last

/-- Actual byte writes produce both original traversal memory relations. No
MapRep or GraphRep is assumed about the output or about the arbitrary input. -/
theorem initializes (table : List SectorLines) (base : Word) (edges : List Edge)
    (consistent : Consistent (image table base edges)) (before : Memory) :
    MapRep table (applyPatch (image table base edges) before) ∧
    GraphRep base edges (applyPatch (image table base edges) before) := by
  have h := realizes consistent before
  exact ⟨map_rep h.left,graph_rep h.right⟩
/-- Fresh visitation stamps require only that the old stamp differ from the
incoming generation. Old cost words are deliberately left unspecified. -/
def freshPatch (table : List SectorLines) (generation old : Word) : Patch :=
  word 0x13580 generation ++ table.flatMap (fun e => word (e.address+66) old)
def freshLedger (table : List SectorLines) : Ledger := table.map (fun e => (e.address,.unseen))
def freshImage (table : List SectorLines) (base : Word) (edges : List Edge) (generation old : Word) : Patch :=
  image table base edges ++ freshPatch table generation old

theorem fresh_shape (table : List SectorLines) : addresses (freshLedger table)=layout table := by
  simp [addresses,freshLedger,layout,List.map_map]

theorem fresh_rep {table generation old m} (h : Realizes (freshPatch table generation old) m)
    (different : old≠generation) : Represents generation m (freshLedger table) := by
  refine ⟨read_word h.left,?_⟩
  intro p hp
  obtain ⟨e,he,rfl⟩ := List.mem_map.mp hp
  change load32 m (e.address+66)≠generation
  have value : load32 m (e.address+66)=old := read_word (h.right.subset
    (fun x hx => List.mem_flatMap.mpr ⟨e,he,hx⟩))
  exact value ▸ different

/-- Build all three required memory relations from sparse writes on arbitrary
prior memory. This is a specification of initialization, not DOS loader execution. -/
theorem initializes_fresh (table : List SectorLines) (base : Word) (edges : List Edge)
    (generation old : Word) (different : old≠generation)
    (consistent : Consistent (freshImage table base edges generation old)) (before : Memory) :
    MapRep table (applyPatch (freshImage table base edges generation old) before) ∧
    GraphRep base edges (applyPatch (freshImage table base edges generation old) before) ∧
    Represents generation (applyPatch (freshImage table base edges generation old) before) (freshLedger table) := by
  have h := realizes consistent before
  exact ⟨map_rep h.left.left,graph_rep h.left.right,fresh_rep h.right different⟩

/-- This changes only the specified bytes, preserving registers and all other
payload bytes. A loader-refinement proof must still relate DOS startup to it. -/
def initialized (table : List SectorLines) (base : Word) (edges : List Edge)
    (generation old : Word) (s : X86Control.State) : X86Control.State :=
  { s with core := { s.core with memory := applyPatch (freshImage table base edges generation old) s.core.memory } }

theorem completes {t limit stack base regions generation old s} (h : Certified t limit) (a : Addresses)
    (allocation : Allocation (t.table a) stack) (storage : Storage (t.table a) stack base (t.edges a) regions)
    (different : old≠generation) (consistent : Consistent (freshImage (t.table a) base (t.edges a) generation old))
    (index : Nat) (inside : index<t.sectors.length) (sector : s.core.regs 0=a.sector index)
    (count : s.core.regs 2=0 ∨ s.core.regs 2=1)
    (low : stack.lo+56*t.sectors.length+20≤(s.core.regs 4).toNat)
    (high : (s.core.regs 4).toNat+4≤stack.hi) (bound : stack.hi≤2^32) :
    ∃ out, eval (2*t.sectors.length*(limit+1)+1) .sector
        (initialized (t.table a) base (t.edges a) generation old s)=some out ∧
      Restored (initialized (t.table a) base (t.edges a) generation old s).core out ∧
      MapRep (t.table a) out.core.memory ∧ GraphRep base (t.edges a) out.core.memory := by
  have result := initializes_fresh (t.table a) base (t.edges a) generation old different consistent s.core.memory
  -- The return word belongs to the initialized entry memory. Relating it to
  -- the pre-initialization caller is separate from register preservation.
  have run := E1M1NoiseTopology.completes (s:=initialized (t.table a) base (t.edges a) generation old s)
    h a allocation storage (fresh_shape _) result.2.2 result.1 result.2.1 index inside sector count low high bound
  exact run
end Doom.Proofs.E1M1NoiseImage
