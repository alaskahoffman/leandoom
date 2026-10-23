import Doom.Proofs.E1M1AimSideLookup
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1600000
set_option linter.unusedSimpArgs false
namespace Doom.Proofs.E1M1AimTextureCatalog
open Verification X86 X86Memory X86Control BlockSummary

abbrev Name := Nat → BitVec 8
/-- Explicit conditional catalog representation, not DOS initialization. -/
structure Catalog where
  count : Nat
  table : Word
  pointer : Nat → Word
  name : Nat → Name
  query : Word
  queryName : Name

def compareName : Nat → Name → Name → Word
  | 0,_,_ => 0
  | n+1,a,b =>
    let x := OriginalTextureFold.lower (a 0)
    let y := OriginalTextureFold.lower (b 0)
    if x≠y then x.zeroExtend 32-y.zeroExtend 32
    else if y=0 then 0 else compareName n (fun j => a (j+1)) (fun j => b (j+1))

def Reads (c : Catalog) (a : Word) : Prop :=
  a=0x300e0 ∨ a=0x300e4 ∨
  (∃ i<c.count, a=c.table+4*BitVec.ofNat 32 i) ∨
  (∃ i<c.count, ∃ j<8, a=c.pointer i+BitVec.ofNat 32 j) ∨
  (∃ j<8, a=c.query+BitVec.ofNat 32 j)

structure Image (c : Catalog) (m : Memory) : Prop where
  table : load32 m 0x300e0=c.table
  count : load32 m 0x300e4=BitVec.ofNat 32 c.count
  pointers : ∀ i<c.count, load32 m (c.table+4*BitVec.ofNat 32 i)=c.pointer i
  names : ∀ i<c.count, ∀ j<8, m (c.pointer i+BitVec.ofNat 32 j)=c.name i j
  query : ∀ j<8, m (c.query+BitVec.ofNat 32 j)=c.queryName j

def SearchSafe (c : Catalog) (sp : Word) : Prop :=
  ∀ a, Reads c a → Apart a (sp-4) ∧ Apart a (sp-8)

structure Cursor (c : Catalog) (s : X86Memory.State) (i : Nat) : Prop where
  index : s.regs 1=BitVec.ofNat 32 i
  offset : s.regs 6=4*BitVec.ofNat 32 i
  query : s.regs 7=c.query

structure FirstMatch (c : Catalog) (j : Nat) : Prop where
  bound : c.count≤2147483647
  member : j<c.count
  equal : compareName 8 (c.name j) c.queryName=0
  earlier : ∀ i<j, compareName 8 (c.name i) c.queryName≠0

theorem image_frame (c : Catalog) (m m' : Memory) (image : Image c m)
    (frame : ∀ a, Reads c a → load32 m' a=load32 m a) : Image c m' := by
  refine ⟨(frame _ (Or.inl rfl)).trans image.table,
    (frame _ (Or.inr (Or.inl rfl))).trans image.count,?_,?_,?_⟩
  · intro i hi
    exact (frame _ (Or.inr (Or.inr (Or.inl ⟨i,hi,rfl⟩)))).trans (image.pointers i hi)
  · intro i hi j hj
    exact (E1M1NoiseGraph.byte_of_word (frame _ (Or.inr (Or.inr (Or.inr (Or.inl ⟨i,hi,j,hj,rfl⟩)))))).trans (image.names i hi j hj)
  · intro j hj
    exact (E1M1NoiseGraph.byte_of_word (frame _ (Or.inr (Or.inr (Or.inr (Or.inr ⟨j,hj,rfl⟩)))))).trans (image.query j hj)

theorem compare_image (n : Nat) (m : Memory) (a b : Word) (x y : Name)
    (left : ∀ j<n, m (a+BitVec.ofNat 32 j)=x j)
    (right : ∀ j<n, m (b+BitVec.ofNat 32 j)=y j) :
    OriginalTextureComparator.compareBytes n m a b=compareName n x y := by
  induction n generalizing a b x y with
  | zero => rfl
  | succ n ih =>
    have l := left 0 (by omega)
    have r := right 0 (by omega)
    simp only [show BitVec.ofNat 32 0=(0#32) from rfl,BitVec.add_zero] at l r
    simp only [OriginalTextureComparator.compareBytes,compareName,l,r]
    split
    · rfl
    · split
      · rfl
      · apply ih
        · intro j hj
          simpa [BitVec.ofNat_add,BitVec.add_assoc,BitVec.add_comm (1#32)] using left (j+1) (by omega)
        · intro j hj
          simpa [BitVec.ofNat_add,BitVec.add_assoc,BitVec.add_comm (1#32)] using right (j+1) (by omega)

theorem comparison_image (c : Catalog) (s : X86Memory.State)
    (image : Image c s.memory) (safe : SearchSafe c (s.regs 4)) :
    Image c (OriginalTextureSearch.comparisonMemory s) := by
  apply image_frame c _ _ image
  intro a ha
  exact (load_store_apart _ _ _ _ (safe a ha).2).trans (load_store_apart _ _ _ _ (safe a ha).1)

/-- Uses the proved original comparator result in actual post-CALL/PUSH memory. -/
theorem comparison_value (c : Catalog) (s : X86Memory.State) (i : Nat)
    (image : Image c s.memory) (safe : SearchSafe c (s.regs 4))
    (regs : Cursor c s i) (member : i<c.count) :
    (OriginalTextureSearch.compared s).core.regs 0=compareName 8 (c.name i) c.queryName := by
  rw [OriginalTextureSearch.comparison_result]
  have ptr : OriginalTextureSearch.texture s=c.pointer i := by
    simp only [OriginalTextureSearch.texture,image.table,regs.offset]
    rw [BitVec.add_comm]
    exact image.pointers i member
  rw [ptr,regs.query]
  have post := comparison_image c s image safe
  exact compare_image 8 _ _ _ _ _ (post.names i member) post.query

theorem comparison_query (s : X86Memory.State) :
    (OriginalTextureSearch.compared s).core.regs 7=s.regs 7 := by
  simpa [OriginalTextureSearch.compared,OriginalTextureSearch.comparison,X86Routine.pushWord,put,write] using
    (OriginalTextureComparator.complete_frame (OriginalTextureSearch.comparison s).core).2 7 (by decide) (by decide) (by decide) (by decide) (by decide)

theorem round_image (c : Catalog) (s : X86Memory.State)
    (image : Image c s.memory) (safe : SearchSafe c (s.regs 4)) :
    Image c (OriginalTextureSearch.round s).core.memory := by
  rw [OriginalTextureSearch.round_memory]
  exact comparison_image c s image safe

private theorem signed_nat (i : Nat) (hi : i<2147483648) :
    (BitVec.ofNat 32 i).toInt=(i : Int) := by
  rw [BitVec.toInt_eq_toNat_cond]
  simp only [BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega),if_pos (by omega)]

private theorem index_next (i : Nat) : BitVec.ofNat 32 i+1=BitVec.ofNat 32 (i+1) := by
  simp [BitVec.ofNat_add]

theorem before_match_continues (c : Catalog) (s : X86Memory.State) (i j : Nat)
    (image : Image c s.memory) (safe : SearchSafe c (s.regs 4))
    (regs : Cursor c s i) (first : FirstMatch c j) (before : i<j) :
    OriginalTextureSearch.continues s := by
  have v := comparison_value c s i image safe regs (by have := first.member; omega)
  have post := comparison_image c s image safe
  refine ⟨by rw [v]; exact first.earlier i before,?_⟩
  have lt : (s.regs 1+1).toInt<(BitVec.ofNat 32 c.count).toInt := by
    rw [regs.index,index_next,signed_nat (i+1) (by have := first.bound; have := first.member; omega),
      signed_nat c.count (by have := first.bound; omega)]
    have := first.member
    omega
  simp only [OriginalTextureSearch.advanced,(OriginalTextureSearch.comparison_registers s).2.1,
    OriginalTextureSearch.comparison_memory,post.count,if_pos lt]

theorem next_cursor (c : Catalog) (s : X86Memory.State) (i : Nat)
    (regs : Cursor c s i) (go : OriginalTextureSearch.continues s) :
    Cursor c (OriginalTextureSearch.round s).core (i+1) := by
  have next := OriginalTextureSearch.continuing_round s go
  refine ⟨?_,?_,?_⟩
  · rw [next.2.2.1,regs.index,index_next]
  · rw [next.2.2.2.2,regs.offset,BitVec.ofNat_add,BitVec.mul_add]
    simp
  · rw [next.1]
    simpa [OriginalTextureSearch.advanced,OriginalTextureSearch.advancedCore,put,write] using
      (comparison_query s).trans regs.query

/-- First-match exactness for the executed search; duplicate later names are allowed.
Only catalog bytes/addresses and separation are assumed, never helper success. -/
theorem search_first_match (c : Catalog) (s : X86Memory.State) (f : Option Flags) (n i j : Nat)
    (image : Image c s.memory) (safe : SearchSafe c (s.regs 4))
    (regs : Cursor c s i) (first : FirstMatch c j)
    (before : i≤j) (fuel : j-i<n) :
    (OriginalTextureSearch.search n s f).core.regs 0=BitVec.ofNat 32 j := by
  induction n generalizing s f i with
  | zero => omega
  | succ n ih =>
    by_cases same : i=j
    · subst i
      have value : (OriginalTextureSearch.compared s).core.regs 0=(0#32) :=
        (comparison_value c s j image safe regs first.member).trans first.equal
      have stop : ¬OriginalTextureSearch.continues s := by
        intro h; exact h.1 value
      simp only [OriginalTextureSearch.search,if_neg stop,OriginalTextureSearch.round,value,↓reduceIte]
      simpa [OriginalTextureSearch.matched,OriginalTextureDash.result,OriginalTextureDash.restored,put,write,
        (OriginalTextureSearch.comparison_registers s).2.1] using regs.index
    · have go := before_match_continues c s i j image safe regs first (by omega)
      have sp := (OriginalTextureSearch.continuing_round s go).2.2.2.1
      simp only [OriginalTextureSearch.search,if_pos go]
      exact ih _ _ (i+1) (round_image c s image safe) (by rwa [sp])
        (next_cursor c s i regs go) (by omega) (by omega)
def LookupSafe (c : Catalog) (sp : Word) : Prop :=
  ∀ a, Reads c a → ∀ off∈[(4#32),8,12,16,20,24,28], Apart a (sp-off)
def WrapperSafe (c : Catalog) (sp : Word) : Prop :=
  ∀ a, Reads c a → ∀ off∈[(4#32),8,12,16,20,24,28,32,36,40], Apart a (sp-off)
def CallSafe (c : Catalog) (sp : Word) : Prop :=
  ∀ a, Reads c a → ∀ off∈[(4#32),8,12,16,20,24,28,32,36,40,44], Apart a (sp-off)
def Resolved (c : Catalog) (j : Nat) : Prop :=
  (c.queryName 0=0x2d ∧ j=0) ∨ (c.queryName 0≠0x2d ∧ FirstMatch c j)

theorem prepared_image (c : Catalog) (s : X86Memory.State)
    (image : Image c s.memory) (safe : LookupSafe c (s.regs 4)) :
    Image c (OriginalTextureDash.prepared s).memory := by
  apply image_frame c _ _ image
  intro a ha
  apply OriginalTextureDash.stack_frame
  intro off member
  apply safe a ha off
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl|rfl|rfl|rfl|rfl <;> simp

theorem named_value (c : Catalog) (s : X86Memory.State) (j : Nat)
    (image : Image c s.memory) (safe : LookupSafe c (s.regs 4))
    (query : s.regs 0=c.query) (first : FirstMatch c j) :
    (E1M1AimTextureSearch.namedResult s).core.regs 0=BitVec.ofNat 32 j := by
  apply search_first_match c _ _ _ 0 j
  · exact prepared_image c s image safe
  · intro a ha
    constructor
    · simpa [E1M1AimTextureSearch.namedStart,OriginalTextureTable.tested,OriginalTextureDash.prepared,put,write,BitVec.sub_sub] using safe a ha 24 (by simp)
    · simpa [E1M1AimTextureSearch.namedStart,OriginalTextureTable.tested,OriginalTextureDash.prepared,put,write,BitVec.sub_sub] using safe a ha 28 (by simp)
  · constructor <;> simp [E1M1AimTextureSearch.namedStart,OriginalTextureTable.tested,OriginalTextureDash.prepared,put,write,query]
  · exact first
  · omega
  · have := first.bound; have := first.member; omega

theorem lookup_value (c : Catalog) (s : X86Memory.State) (j : Nat)
    (image : Image c s.memory) (safe : LookupSafe c (s.regs 4))
    (query : s.regs 0=c.query) (resolved : Resolved c j) :
    (E1M1AimTextureLookup.lookup s).core.regs 0=BitVec.ofNat 32 j := by
  have post := prepared_image c s image safe
  have byte : OriginalTextureDash.nameByte s=c.queryName 0 := by
    simpa [OriginalTextureDash.nameByte,OriginalTextureDash.prepared,query] using post.query 0 (by decide)
  rcases resolved with ⟨dash,rfl⟩|⟨named,first⟩
  · simp [E1M1AimTextureLookup.lookup,byte,dash,OriginalTextureDash.returned,put,write]
  · have named : c.queryName 0≠(0x2d#8) := named
    have positive : 0<(OriginalTextureTable.count (OriginalTextureDash.prepared s)).toInt := by
      change 0<(load32 (OriginalTextureDash.prepared s).memory 0x300e4).toInt
      rw [post.count,signed_nat c.count (by have := first.bound; omega)]
      have := first.member
      omega
    simp only [E1M1AimTextureLookup.lookup,byte,if_neg named,if_neg (by omega : ¬(OriginalTextureTable.count (OriginalTextureDash.prepared s)).toInt≤0)]
    exact named_value c s j image safe query first

theorem resolved_bound (c : Catalog) (j : Nat) (resolved : Resolved c j) : j<2147483647 := by
  rcases resolved with ⟨_,rfl⟩|⟨_,first⟩
  · decide
  · have := first.bound; have := first.member; omega

theorem wrapper_inner_value (c : Catalog) (s : X86Memory.State) (f : Option Flags) (j : Nat)
    (image : Image c s.memory) (safe : WrapperSafe c (s.regs 4))
    (query : s.regs 0=c.query) (resolved : Resolved c j) :
    (E1M1AimTextureLookup.inner s f).core.regs 0=BitVec.ofNat 32 j := by
  apply lookup_value c _ j
  · apply image_frame c _ _ image
    intro a ha
    exact OriginalTextureWrapper.entry_frame s f a (safe a ha 4 (by simp)) (safe a ha 8 (by simp)) (safe a ha 12 (by simp))
  · intro a ha off member
    have mem : 12+off∈[(4#32),8,12,16,20,24,28,32,36,40] := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
    simpa [(OriginalTextureWrapper.entry_arguments s f).2.2.1,BitVec.sub_sub] using safe a ha (12+off) mem
  · exact (OriginalTextureWrapper.entry_arguments s f).1.trans query
  · exact resolved

theorem wrapper_result (c : Catalog) (s : X86Memory.State) (f : Option Flags) (j : Nat)
    (image : Image c s.memory) (safe : WrapperSafe c (s.regs 4))
    (query : s.regs 0=c.query) (resolved : Resolved c j) :
    (E1M1AimTextureLookup.wrapped s f).pc=(load32 s.memory (s.regs 4)).toNat ∧
      (E1M1AimTextureLookup.wrapped s f).core.regs 0=BitVec.ofNat 32 j := by
  have value := wrapper_inner_value c s f j image safe query resolved
  have success : (E1M1AimTextureLookup.inner s f).core.regs 0≠0xffffffff := by
    rw [value]
    intro eq
    have eqNat := congrArg BitVec.toNat eq
    change j%4294967296=4294967295 at eqNat
    have := resolved_bound c j resolved
    omega
  have h := (E1M1AimTextureLookup.wrapper_outcomes s f).2 success
  exact ⟨h.1,h.2.1.trans value⟩

theorem call_result (c : Catalog) (s : X86Memory.State) (f : Option Flags) (dest : Word) (j : Nat)
    (image : Image c s.memory) (safe : CallSafe c (s.regs 4))
    (query : s.regs 0=c.query) (resolved : Resolved c j) :
    (E1M1AimTextureLookup.wrapped (X86Routine.pushWord s dest) f).pc=dest.toNat ∧
      (E1M1AimTextureLookup.wrapped (X86Routine.pushWord s dest) f).core.regs 0=BitVec.ofNat 32 j := by
  have h := wrapper_result c (X86Routine.pushWord s dest) f j
    (image_frame c _ _ image (by intro a ha; exact load_store_apart _ _ _ _ (safe a ha 4 (by simp))))
    (by
      intro a ha off member
      have mem : 4+off∈[(4#32),8,12,16,20,24,28,32,36,40,44] := by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at member
        rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
      simpa [X86Routine.pushWord,put,write,BitVec.sub_sub] using safe a ha (4+off) mem)
    (by simpa [X86Routine.pushWord,put,write] using query) resolved
  simpa only [X86Routine.pushWord,put,write,↓reduceIte,load_store] using h
def SideSafe (c : Catalog) (s : X86Memory.State) : Prop :=
  ∀ a, Reads c a → E1M1AimSideLookup.Safe s a

structure SideInput (a b c : Catalog) (s : X86Memory.State) (x y z : Nat) : Prop where
  images : Image a s.memory ∧ Image b s.memory ∧ Image c s.memory
  safe : SideSafe a s ∧ SideSafe b s ∧ SideSafe c s
  queries : s.regs 0=a.query ∧ s.regs 7=b.query ∧ s.regs 6=c.query
  resolved : Resolved a x ∧ Resolved b y ∧ Resolved c z

theorem side_call_safe (c : Catalog) (s : X86Memory.State) (safe : SideSafe c s) :
    CallSafe c (s.regs 4) := by
  intro a ha off member
  exact (safe a ha).stack off (List.mem_cons_of_mem 0 member)

theorem side_safe_transport (c : Catalog) (s t : X86Memory.State) (safe : SideSafe c s)
    (stack : t.regs 4=s.regs 4) (record : t.regs 2=s.regs 2) : SideSafe c t := by
  intro a ha
  refine ⟨?_,?_⟩
  · simpa only [stack] using (safe a ha).stack
  · simpa only [record] using (safe a ha).fields

theorem call_image (c : Catalog) (s : X86Memory.State) (f : Option Flags) (dest : Word)
    (image : Image c s.memory) (safe : CallSafe c (s.regs 4)) :
    Image c (E1M1AimTextureLookup.wrapped (X86Routine.pushWord s dest) f).core.memory := by
  exact image_frame c _ _ image (fun a ha => E1M1AimSideLookup.call_frame s f dest a (safe a ha))

theorem stored_image (c : Catalog) (s : X86Memory.State) (off : Word)
    (image : Image c s.memory) (safe : SideSafe c s) (field : off∈[(8#32),10,12]) :
    Image c (OriginalSideTextures.stored s off).memory := by
  apply image_frame c _ _ image
  intro a ha
  exact OriginalSideTextures.stored_frame s off a (by simpa using (safe a ha).stack 0 (by simp))
    ((safe a ha).fields off field)

attribute [local irreducible] E1M1AimTextureLookup.wrapped

/-- All three actual calls return the catalog's exact IDs. The only images
supplied are at the incoming side-call boundary; intermediate images are derived. -/
theorem side_results (a b c : Catalog) (s : X86Memory.State) (f : Option Flags) (x y z : Nat)
    (input : SideInput a b c s x y z) :
    ((E1M1AimSideLookup.first s f).pc=0x2e483 ∧ (E1M1AimSideLookup.first s f).core.regs 0=BitVec.ofNat 32 x) ∧
    ((E1M1AimSideLookup.second s f).pc=0x2e494 ∧ (E1M1AimSideLookup.second s f).core.regs 0=BitVec.ofNat 32 y) ∧
    ((E1M1AimSideLookup.third s f).pc=0x2e4a5 ∧ (E1M1AimSideLookup.third s f).core.regs 0=BitVec.ofNat 32 z) := by
  have h1 := call_result a s f 0x2e483 x input.images.1 (side_call_safe a s input.safe.1) input.queries.1 input.resolved.1
  change (E1M1AimSideLookup.first s f).pc=0x2e483 ∧ (E1M1AimSideLookup.first s f).core.regs 0=BitVec.ofNat 32 x at h1
  have ok1 : (E1M1AimSideLookup.first s f).pc≠0x34760 := by rw [h1.1]; decide
  have r1 (r : Reg) (h : r≠0) : (E1M1AimSideLookup.first s f).core.regs r=s.regs r :=
    E1M1AimSideLookup.call_registers s f 0x2e483 ok1 r h
  let t := put (OriginalSideTextures.stored (E1M1AimSideLookup.first s f).core 8) 0 ((E1M1AimSideLookup.first s f).core.regs 7)
  have rt (r : Reg) (h : r≠0) : t.regs r=s.regs r := by
    simpa [t,put,write,h,OriginalSideTextures.stored] using r1 r h
  have img (d : Catalog) (hd : Image d s.memory) (hs : SideSafe d s) : Image d t.memory := by
    exact stored_image d _ 8 (call_image d s f 0x2e483 hd (side_call_safe d s hs))
      (side_safe_transport d s _ hs (r1 4 (by decide)) (r1 2 (by decide))) (by simp)
  have safe (d : Catalog) (hs : SideSafe d s) : SideSafe d t :=
    side_safe_transport d s t hs (rt 4 (by decide)) (rt 2 (by decide))
  have q2 : t.regs 0=b.query := by
    simpa [t,put,write] using (r1 7 (by decide)).trans input.queries.2.1
  have h2 := call_result b t (E1M1AimSideLookup.first s f).flags 0x2e494 y
    (img b input.images.2.1 input.safe.2.1) (side_call_safe b t (safe b input.safe.2.1)) q2 input.resolved.2.1
  change (E1M1AimSideLookup.second s f).pc=0x2e494 ∧ (E1M1AimSideLookup.second s f).core.regs 0=BitVec.ofNat 32 y at h2
  have ok2 : (E1M1AimSideLookup.second s f).pc≠0x34760 := by rw [h2.1]; decide
  have r2 (r : Reg) (h : r≠0) : (E1M1AimSideLookup.second s f).core.regs r=s.regs r :=
    (E1M1AimSideLookup.call_registers t (E1M1AimSideLookup.first s f).flags 0x2e494 ok2 r h).trans (rt r h)
  let u := put (OriginalSideTextures.stored (E1M1AimSideLookup.second s f).core 10) 0 ((E1M1AimSideLookup.second s f).core.regs 6)
  have ru (r : Reg) (h : r≠0) : u.regs r=s.regs r := by
    simpa [u,put,write,h,OriginalSideTextures.stored] using r2 r h
  have img3 : Image c u.memory :=
    stored_image c _ 10 (call_image c t (E1M1AimSideLookup.first s f).flags 0x2e494
      (img c input.images.2.2 input.safe.2.2) (side_call_safe c t (safe c input.safe.2.2)))
      (side_safe_transport c s _ input.safe.2.2 (r2 4 (by decide)) (r2 2 (by decide))) (by simp)
  have q3 : u.regs 0=c.query := by
    simpa [u,put,write] using (r2 6 (by decide)).trans input.queries.2.2
  have h3 := call_result c u (E1M1AimSideLookup.second s f).flags 0x2e4a5 z img3
    (side_call_safe c u (side_safe_transport c s u input.safe.2.2 (ru 4 (by decide)) (ru 2 (by decide)))) q3 input.resolved.2.2
  exact ⟨h1,h2,h3⟩

theorem side_returned (a b c : Catalog) (s : X86Memory.State) (f : Option Flags) (x y z : Nat)
    (input : SideInput a b c s x y z) : E1M1AimSideLookup.Returned s f := by
  have h := side_results a b c s f x y z input
  exact ⟨by rw [h.1.1]; decide,by rw [h.2.1.1]; decide,by rw [h.2.2.1]; decide⟩

theorem side_emitted (a b c : Catalog) (s : X86Memory.State) (f : Option Flags) (x y z : Nat)
    (catalog : SideInput a b c s x y z)
    (side : BitVec 16) (index : Nat) (sideBase sectorBase : Word)
    (input : E1M1AimSideEncoding.Input s side index sideBase sectorBase)
    (sourceSafe : E1M1AimSideLookup.Safe s (s.regs 3+28))
    (sectorSafe : E1M1AimSideLookup.Safe s 0x2c148) :
    E1M1NoiseImage.Realizes
      (E1M1NoiseImage.word (E1M1NoiseGraph.sideAddress sideBase side) (E1M1AimSideEncoding.sectorAddress sectorBase index))
      (E1M1AimSideLookup.iteration s f).core.memory := by
  exact E1M1AimSideLookup.emitted s f (side_returned a b c s f x y z catalog)
    side index sideBase sectorBase input sourceSafe sectorSafe
def OffsetSafe (s : X86Memory.State) (p : Word) : Prop :=
  Apart p (s.regs 2) ∧ Apart p (s.regs 2+4)
structure BodySafe (s : X86Memory.State) (p : Word) : Prop where
  offsets : OffsetSafe s p
  textures : E1M1AimSideLookup.Safe s p
  pointer : Apart p (s.regs 2+14)

/-- Input at 0x2e46a. EAX is set from ECX by the actual offset prefix.
This is an explicit initialized image assumption, not construction or reachability. -/
structure BodyCatalog (a b c : Catalog) (s : X86Memory.State) (x y z : Nat) : Prop where
  incoming : SideInput a b c (put s 0 (s.regs 1)) x y z
  offsets : ∀ d∈[a,b,c], ∀ p, Reads d p → OffsetSafe s p

def body (s : X86Memory.State) := E1M1AimSideLookup.iteration (OriginalSideAdvance.prepared s).core none

theorem offset_registers (s : X86Memory.State) (r : Reg) (h : r≠0) :
    (OriginalSideAdvance.prepared s).core.regs r=s.regs r := by
  simp [OriginalSideAdvance.prepared,put,write,h]

theorem body_catalog_input (a b c : Catalog) (s : X86Memory.State) (x y z : Nat)
    (catalog : BodyCatalog a b c s x y z) :
    SideInput a b c (OriginalSideAdvance.prepared s).core x y z := by
  have frame (d : Catalog) (hd : d∈[a,b,c]) (im : Image d s.memory) :
      Image d (OriginalSideAdvance.prepared s).core.memory := by
    apply image_frame d _ _ im
    intro p hp
    exact OriginalSideAdvance.offsets_frame s p (catalog.offsets d hd p hp).1 (catalog.offsets d hd p hp).2
  refine ⟨⟨frame a (by simp) catalog.incoming.images.1,
    frame b (by simp) catalog.incoming.images.2.1,frame c (by simp) catalog.incoming.images.2.2⟩,?_,catalog.incoming.queries,catalog.incoming.resolved⟩
  exact ⟨side_safe_transport a _ _ catalog.incoming.safe.1 rfl rfl,
    side_safe_transport b _ _ catalog.incoming.safe.2.1 rfl rfl,
    side_safe_transport c _ _ catalog.incoming.safe.2.2 rfl rfl⟩

theorem body_returned (a b c : Catalog) (s : X86Memory.State) (x y z : Nat)
    (catalog : BodyCatalog a b c s x y z) :
    E1M1AimSideLookup.Returned (OriginalSideAdvance.prepared s).core none :=
  side_returned a b c _ none x y z (body_catalog_input a b c s x y z catalog)

theorem body_execution (s : X86Memory.State) (f : Option Flags) :
    ∃ k≤3*(202*2147483647+30)+36,
      X86ByteRoutine.Prefix E1M1AimSideLookup.iterationProgram [] k ⟨s,f,0x2e46a⟩ (body s) :=
  E1M1AimSideLookup.body_execution s f

theorem body_frame (a b c : Catalog) (s : X86Memory.State) (x y z : Nat)
    (catalog : BodyCatalog a b c s x y z) (p : Word) (safe : BodySafe s p) :
    load32 (body s).core.memory p=load32 s.memory p := by
  let t := (OriginalSideAdvance.prepared s).core
  have ok := body_returned a b c s x y z catalog
  have regs (r : Reg) (h : r≠0) : (E1M1AimSideLookup.finished t none).core.regs r=s.regs r :=
    (E1M1AimSideLookup.registers t none ok r h).trans (offset_registers s r h)
  have before := OriginalSideAdvance.offsets_frame s p safe.offsets.1 safe.offsets.2
  have middle := E1M1AimSideLookup.frame t none ok p ⟨safe.textures.stack,safe.textures.fields⟩
  have scratch : Apart p ((E1M1AimSideLookup.finished t none).core.regs 4) := by
    rw [regs 4 (by decide)]
    simpa using safe.textures.stack 0 (by simp)
  have pointer : Apart p ((E1M1AimSideLookup.finished t none).core.regs 2+14) := by
    rw [regs 2 (by decide)]; exact safe.pointer
  have suffix : load32 (OriginalSideAdvance.result (E1M1AimSideLookup.finished t none).core).core.memory p=
      load32 (E1M1AimSideLookup.finished t none).core.memory p := by
    exact (load_store_apart _ _ _ _ pointer).trans (load_store_apart _ _ _ _ scratch)
  have pc := E1M1AimSideLookup.returned_pc t none ok
  change load32 (E1M1AimSideLookup.iteration t none).core.memory p=load32 s.memory p
  rw [E1M1AimSideLookup.iteration,pc,if_neg (by decide : (0x2e4af : Nat)≠0x34760)]
  exact suffix.trans (middle.trans before)

/-- Simultaneously retains every supplied protected word, not just the last
emitted pointer. Protection covers offsets, every CALL/PUSH, fields and suffix. -/
theorem body_words (a b c : Catalog) (s : X86Memory.State) (x y z : Nat)
    (catalog : BodyCatalog a b c s x y z) (addresses : List Word)
    (safe : ∀ p∈addresses, BodySafe s p) :
    ∀ p∈addresses, load32 (body s).core.memory p=load32 s.memory p := by
  intro p hp
  exact body_frame a b c s x y z catalog p (safe p hp)

theorem offset_input (s : X86Memory.State) (side : BitVec 16) (index : Nat) (sideBase sectorBase : Word)
    (input : E1M1AimSideEncoding.Input s side index sideBase sectorBase)
    (source : OffsetSafe s (s.regs 3+28)) (sectors : OffsetSafe s 0x2c148) :
    E1M1AimSideEncoding.Input (OriginalSideAdvance.prepared s).core side index sideBase sectorBase := by
  refine ⟨input.record,?_,(OriginalSideAdvance.offsets_frame s _ sectors.1 sectors.2).trans input.sectors,input.safe,input.valid⟩
  apply E1M1AimSideLookup.half_of_load
  exact (E1M1LineSource.half_of_word (OriginalSideAdvance.offsets_frame s _ source.1 source.2)).trans
    (E1M1NoiseImage.read_half input.source)

theorem body_emitted (a b c : Catalog) (s : X86Memory.State) (x y z : Nat)
    (catalog : BodyCatalog a b c s x y z)
    (side : BitVec 16) (index : Nat) (sideBase sectorBase : Word)
    (input : E1M1AimSideEncoding.Input s side index sideBase sectorBase)
    (sourceSafe : BodySafe s (s.regs 3+28)) (sectorSafe : BodySafe s 0x2c148) :
    E1M1NoiseImage.Realizes
      (E1M1NoiseImage.word (E1M1NoiseGraph.sideAddress sideBase side) (E1M1AimSideEncoding.sectorAddress sectorBase index))
      (body s).core.memory := by
  exact side_emitted a b c _ none x y z (body_catalog_input a b c s x y z catalog) side index sideBase sectorBase
    (offset_input s side index sideBase sectorBase input sourceSafe.offsets sectorSafe.offsets)
    ⟨sourceSafe.textures.stack,sourceSafe.textures.fields⟩
    ⟨sectorSafe.textures.stack,sectorSafe.textures.fields⟩
theorem body_bounded (a b c : Catalog) (s : X86Memory.State) (x y z : Nat)
    (catalog : BodyCatalog a b c s x y z) (countSafe : BodySafe s 0x2c11c)
    (i total : Nat) (index : (s.regs 5).toNat=i) (count : (load32 s.memory 0x2c11c).toNat=total)
    (small : total<2147483648) (inside : i<total) :
    (body s).pc=(if i+1<total then 0x2e46a else 0x2e4dd) ∧
      ((body s).core.regs 5).toNat=i+1 := by
  let t := (OriginalSideAdvance.prepared s).core
  have ok := body_returned a b c s x y z catalog
  have regs (r : Reg) (h : r≠0) : (E1M1AimSideLookup.finished t none).core.regs r=s.regs r :=
    (E1M1AimSideLookup.registers t none ok r h).trans (offset_registers s r h)
  have mem := (E1M1AimSideLookup.frame t none ok 0x2c11c ⟨countSafe.textures.stack,countSafe.textures.fields⟩).trans
    (OriginalSideAdvance.offsets_frame s _ countSafe.offsets.1 countSafe.offsets.2)
  have next := E1M1AimSideAdvance.bounded_branch (E1M1AimSideLookup.finished t none).core i total
    (by rw [regs 5 (by decide)]; exact index) (by rw [mem]; exact count) small inside
    (by rw [regs 4 (by decide)]; simpa using countSafe.textures.stack 0 (by simp))
    (by rw [regs 2 (by decide)]; exact countSafe.pointer)
  change (E1M1AimSideLookup.iteration t none).pc=_ ∧ ((E1M1AimSideLookup.iteration t none).core.regs 5).toNat=_
  rw [E1M1AimSideLookup.iteration,E1M1AimSideLookup.returned_pc t none ok,if_neg (by decide : (0x2e4af : Nat)≠0x34760)]
  exact next
end Doom.Proofs.E1M1AimTextureCatalog
