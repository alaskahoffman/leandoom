import Doom.Proofs.E1M1AimPinnedCatalog
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1600000
set_option linter.unusedSimpArgs false
namespace Doom.Proofs.E1M1AimSideLoop
open Verification X86 X86Memory X86Control BlockSummary
open E1M1AimTextureCatalog E1M1AimPinnedCatalog
open E1M1NoiseAllocation (Region)

theorem body_progress (s : X86Memory.State) (table : Word) (pointer : Nat → Word)
    (row : Fin 648) (ready : BodyReady s table pointer row) :
    (body s).core.regs 3=s.regs 3+30 ∧
    (body s).core.regs 2=s.regs 2+18 ∧
    (body s).core.regs 5=s.regs 5+1 ∧
    (body s).core.regs 4=s.regs 4 ∧
    (body s).core.regs 1=s.regs 1+30 ∧
    (body s).core.regs 7=s.regs 7+30 ∧
    (body s).core.regs 6=s.regs 6+30 := by
  let t := (OriginalSideAdvance.prepared s).core
  have ok := body_returned _ _ _ s _ _ _ (pinned_body_catalog s table pointer row ready)
  have regs (r : Reg) (h : r≠0) : (E1M1AimSideLookup.finished t none).core.regs r=s.regs r :=
    (E1M1AimSideLookup.registers t none ok r h).trans (offset_registers s r h)
  unfold body E1M1AimSideLookup.iteration
  rw [E1M1AimSideLookup.returned_pc t none ok,if_neg (by decide : (0x2e4af : Nat)≠0x34760)]
  simpa only [regs 3 (by decide),regs 2 (by decide),regs 5 (by decide),regs 4 (by decide),
    regs 1 (by decide),regs 7 (by decide),regs 6 (by decide)] using
    E1M1AimSideAdvance.progress (E1M1AimSideLookup.finished t none).core

/-- Static addresses only: no reached states, images or successful paths. -/
structure LayoutData where
  raw : Word
  output : Word
  sp : Word
  sectors : Word
  table : Word
  pointer : Nat → Word
  sectorIndex : Fin 648 → Nat

def cursor (base : Word) (stride i : Nat) : Word := base+BitVec.ofNat 32 (stride*i)
def region (base : Word) (size : Nat) : Region := ⟨base.toNat,base.toNat+size⟩
def query (l : LayoutData) (row : Fin 648) (k : Fin 3) : Word :=
  cursor l.raw 30 row.val+BitVec.ofNat 32 (4+8*k.val)
def rowCatalog (l : LayoutData) (row : Fin 648) (k : Fin 3) : Catalog :=
  catalog l.table l.pointer (query l row k) (fieldQuery row k)

/-- All source bytes, every catalog read, and the three loader globals.
Four-byte protection windows at byte reads deliberately overprotect by 3 bytes. -/
def Persistent (l : LayoutData) (p : Word) : Prop :=
  p=0x2c11c ∨ p=0x2c148 ∨ p=0x2c118 ∨
  (∃ row : Fin 648, ∃ off<30, p=cursor l.raw 30 row.val+BitVec.ofNat 32 off) ∨
  (∃ row : Fin 648, ∃ k : Fin 3, Reads (rowCatalog l row k) p)

structure Storage (l : LayoutData) where
  stack : Region
  reserve : stack.lo+44≤l.sp.toNat ∧ l.sp.toNat+4≤stack.hi ∧ stack.hi≤2^32
  outputBound : l.output.toNat+18*648≤2^32
  outputStack : (region l.output (18*648)).Disjoint stack
  protectedReads : ∀ p, Persistent l p → ∃ r : Region,
    r.Contains p ∧ r.Disjoint (region l.output (18*648)) ∧ r.Disjoint stack

structure Layout (l : LayoutData) extends Storage l where
  sectorValid : ∀ row, l.sectorIndex row<32768

/-- All data hypotheses refer to this single memory. Query bytes are at the
actual raw SIDEDEFS offsets, not a separate string oracle. -/
structure SourceImage (l : LayoutData) (m : Memory) : Prop where
  catalogs : ∀ row k, Image (rowCatalog l row k) m
  source : ∀ row : Fin 648, load16 m (cursor l.raw 30 row.val+28)=BitVec.ofNat 16 (l.sectorIndex row)
  sectors : load32 m 0x2c148=l.sectors
  count : load32 m 0x2c11c=648
  published : load32 m 0x2c118=l.output

structure Registers (l : LayoutData) (i : Nat) (s : X86Memory.State) : Prop where
  raw : s.regs 3=cursor l.raw 30 i
  output : s.regs 2=cursor l.output 18 i
  index : (s.regs 5).toNat=i
  stack : s.regs 4=l.sp
  upper : s.regs 1=cursor l.raw 30 i+4
  lower : s.regs 7=cursor l.raw 30 i+12
  middle : s.regs 6=cursor l.raw 30 i+20

structure Incoming (l : LayoutData) (s : X86Memory.State) : Prop where
  registers : Registers l 0 s
  image : SourceImage l s.memory

def Outputs (l : LayoutData) (n : Nat) (m : Memory) : Prop :=
  ∀ row : Fin 648, row.val<n → load32 m (cursor l.output 18 row.val+14)=
    E1M1AimSideEncoding.sectorAddress l.sectors (l.sectorIndex row)

def states (s : X86Memory.State) (f : Option Flags) : Nat → X86Control.State
  | 0 => ⟨s,f,0x2e46a⟩
  | n+1 => body (states s f n).core

structure Invariant (l : LayoutData) (before : Memory) (n : Nat) (s : X86Memory.State) : Prop where
  registers : Registers l n s
  image : SourceImage l s.memory
  outputs : Outputs l n s.memory
  preserved : ∀ p, Persistent l p → load32 s.memory p=load32 before p

theorem at_next (base : Word) (stride n : Nat) :
    cursor base stride (n+1)=cursor base stride n+BitVec.ofNat 32 stride := by
  simp [cursor,Nat.mul_add,BitVec.ofNat_add,BitVec.add_assoc]

theorem at_nat (base : Word) (stride n : Nat) (bound : base.toNat+stride*n<2^32) :
    (cursor base stride n).toNat=base.toNat+stride*n := by
  simp only [cursor,BitVec.toNat_add,BitVec.toNat_ofNat]
  omega

theorem region_field (base : Word) (size off : Nat)
    (bound : base.toNat+size≤2^32) (fits : off+4≤size) :
    (region base size).Contains (base+BitVec.ofNat 32 off) := by
  simp only [region,Region.Contains,BitVec.toNat_add,BitVec.toNat_ofNat]
  omega

/-- Derives the full body guard from ordinary disjoint byte regions. -/
theorem region_safe (l : LayoutData) (layout : Layout l) (i : Nat) (s : X86Memory.State)
    (regs : Registers l i s) (inside : i<648) (p : Word) (r : Region)
    (read : r.Contains p) (output : r.Disjoint (region (cursor l.output 18 i) 18))
    (stack : r.Disjoint layout.stack) : BodySafe s p := by
  have pos := at_nat l.output 18 i (by have := layout.outputBound; omega)
  have word (off : Nat) (fits : off+4≤18) : Apart p (s.regs 2+BitVec.ofNat 32 off) := by
    rw [regs.output]
    exact Region.apart read (region_field _ 18 off (by have := layout.outputBound; omega) fits) output
  have saved (n : Nat) (hn : n≤44) : layout.stack.Contains (l.sp-BitVec.ofNat 32 n) := by
    have reserve := layout.reserve
    simp only [Region.Contains,BitVec.toNat_sub,BitVec.toNat_ofNat]
    have := l.sp.isLt
    omega
  refine ⟨⟨?_,word 4 (by decide)⟩,⟨?_,?_⟩,word 14 (by decide)⟩
  · simpa only [BitVec.add_zero] using word 0 (by decide)
  · intro off member
    rw [regs.stack]
    apply Region.apart read _ stack
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> exact saved _ (by decide)
  · intro off member
    have whole : Apart p (s.regs 2+off) := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl|rfl|rfl <;> exact word _ (by decide)
    intro a b eq
    exact whole a ⟨b.val,by have := b.isLt; omega⟩ eq

theorem persistent_safe (l : LayoutData) (layout : Layout l) (i : Nat) (s : X86Memory.State)
    (regs : Registers l i s) (inside : i<648) (p : Word) (hp : Persistent l p) : BodySafe s p := by
  obtain ⟨r,read,out,stack⟩ := layout.protectedReads p hp
  have pos := at_nat l.output 18 i (by have := layout.outputBound; omega)
  apply region_safe l layout i s regs inside p r read _ stack
  rcases out with left|right
  · exact Or.inl (by simp only [region,pos]; simp only [region] at left; omega)
  · exact Or.inr (by simp only [region,pos]; simp only [region] at right; omega)

/-- Every four-byte window of every earlier record, not just its pointer. -/
theorem earlier_safe (l : LayoutData) (layout : Layout l) (i j off : Nat) (s : X86Memory.State)
    (regs : Registers l i s) (inside : i<648) (order : j<i) (fits : off+4≤18) :
    BodySafe s (cursor l.output 18 j+BitVec.ofNat 32 off) := by
  have left := at_nat l.output 18 j (by have := layout.outputBound; omega)
  have right := at_nat l.output 18 i (by have := layout.outputBound; omega)
  apply region_safe l layout i s regs inside _ (region (cursor l.output 18 j) 18)
    (region_field _ 18 off (by have := layout.outputBound; omega) fits)
    (Or.inl (by simp only [region,left,right]; omega))
  rcases layout.outputStack with before|after
  · exact Or.inl (by simp only [region,left]; simp only [region] at before; omega)
  · exact Or.inr (by simp only [region,left]; simp only [region] at after; omega)

theorem query_register (l : LayoutData) (row : Fin 648) (s : X86Memory.State)
    (regs : Registers l row.val s) (k : Fin 3) :
    s.regs (if k=0 then 1 else if k=1 then 7 else 6)=query l row k := by
  have hk := k.isLt
  rcases (show k.val=0 ∨ k.val=1 ∨ k.val=2 by omega) with h|h|h
  · have : k=0 := Fin.ext h; subst k; exact regs.upper
  · have : k=1 := Fin.ext h; subst k; exact regs.lower
  · have : k=2 := Fin.ext h; subst k; exact regs.middle

theorem body_ready (l : LayoutData) (layout : Layout l) (row : Fin 648) (s : X86Memory.State)
    (regs : Registers l row.val s) (image : SourceImage l s.memory) : BodyReady s l.table l.pointer row := by
  have eq (k : Fin 3) : bodyCatalog s l.table l.pointer row k=rowCatalog l row k := by
    unfold bodyCatalog rowCatalog; rw [query_register l row s regs k]
  refine ⟨?_,?_,?_⟩
  · intro k; rw [eq]; exact image.catalogs row k
  · intro k p hp
    rw [eq] at hp
    exact (persistent_safe l layout row.val s regs row.isLt p (Or.inr (Or.inr (Or.inr (Or.inr ⟨row,k,hp⟩))))).textures
  · intro k p hp
    rw [eq] at hp
    exact (persistent_safe l layout row.val s regs row.isLt p (Or.inr (Or.inr (Or.inr (Or.inr ⟨row,k,hp⟩))))).offsets

theorem source_frame (l : LayoutData) (before after : Memory) (image : SourceImage l before)
    (frame : ∀ p, Persistent l p → load32 after p=load32 before p) : SourceImage l after := by
  refine ⟨?_,?_,(frame _ (Or.inr (Or.inl rfl))).trans image.sectors,
    (frame _ (Or.inl rfl)).trans image.count,
    (frame _ (Or.inr (Or.inr (Or.inl rfl)))).trans image.published⟩
  · intro row k
    exact image_frame _ _ _ (image.catalogs row k)
      (fun p hp => frame p (Or.inr (Or.inr (Or.inr (Or.inr ⟨row,k,hp⟩)))))
  · intro row
    exact (E1M1LineSource.half_of_word (frame _ (Or.inr (Or.inr (Or.inr (Or.inl ⟨row,28,by decide,rfl⟩)))))).trans (image.source row)

theorem source_input (l : LayoutData) (layout : Layout l) (row : Fin 648) (s : X86Memory.State)
    (regs : Registers l row.val s) (image : SourceImage l s.memory) :
    E1M1AimSideEncoding.Input s (BitVec.ofNat 16 row.val) (l.sectorIndex row) l.output l.sectors := by
  have sign : (BitVec.ofNat 16 row.val).signExtend 32=BitVec.ofNat 32 row.val := by
    have hi := row.isLt
    apply BitVec.eq_of_toInt_eq
    rw [BitVec.toInt_signExtend_of_le (by decide)]
    simp only [BitVec.toInt_eq_toNat_cond,BitVec.toNat_ofNat]
    omega
  refine ⟨?_,?_,image.sectors,?_,layout.sectorValid row⟩
  · rw [regs.output,sign]
    simp [cursor,BitVec.ofNat_mul,BitVec.mul_comm]
  · rw [regs.raw]
    exact E1M1AimSideLookup.half_of_load _ _ _ (image.source row)
  · have safe := persistent_safe l layout row.val s regs row.isLt 0x2c148 (Or.inr (Or.inl rfl))
    simpa using safe.textures.stack 0 (by simp)


/-- One derived transition: no caller-supplied body success or next image. -/
theorem invariant_step (l : LayoutData) (layout : Layout l) (before : Memory)
    (i : Nat) (s : X86Memory.State) (inv : Invariant l before i s) (inside : i<648) :
    Invariant l before (i+1) (body s).core ∧
      (body s).pc=(if i+1<648 then 0x2e46a else 0x2e4dd) := by
  let row : Fin 648 := ⟨i,inside⟩
  have ready := body_ready l layout row s inv.registers inv.image
  have cat := pinned_body_catalog s l.table l.pointer row ready
  have frame (p : Word) (safe : BodySafe s p) : load32 (body s).core.memory p=load32 s.memory p :=
    body_frame _ _ _ s _ _ _ cat p safe
  have stable (p : Word) (hp : Persistent l p) : load32 (body s).core.memory p=load32 s.memory p :=
    frame p (persistent_safe l layout i s inv.registers inside p hp)
  have latch := body_bounded _ _ _ s _ _ _ cat
    (persistent_safe l layout i s inv.registers inside 0x2c11c (Or.inl rfl)) i 648
    inv.registers.index (by rw [inv.image.count]; rfl) (by decide) inside
  have step := body_progress s l.table l.pointer row ready
  have regs : Registers l (i+1) (body s).core := by
    refine ⟨?_,?_,latch.2,step.2.2.2.1.trans inv.registers.stack,?_,?_,?_⟩
    · simpa [inv.registers.raw,at_next] using step.1
    · simpa [inv.registers.output,at_next] using step.2.1
    · simpa [inv.registers.upper,at_next,BitVec.add_assoc,BitVec.add_comm (4#32)] using step.2.2.2.2.1
    · simpa [inv.registers.lower,at_next,BitVec.add_assoc,BitVec.add_comm (12#32)] using step.2.2.2.2.2.1
    · simpa [inv.registers.middle,at_next,BitVec.add_assoc,BitVec.add_comm (20#32)] using step.2.2.2.2.2.2
  have input := source_input l layout row s inv.registers inv.image
  have emitted := body_emitted _ _ _ s _ _ _ cat (BitVec.ofNat 16 i) (l.sectorIndex row) l.output l.sectors input
    (persistent_safe l layout i s inv.registers inside _ (by
      rw [inv.registers.raw]; exact Or.inr (Or.inr (Or.inr (Or.inl ⟨row,28,by decide,rfl⟩)))))
    (persistent_safe l layout i s inv.registers inside _ (Or.inr (Or.inl rfl)))
  have address : E1M1NoiseGraph.sideAddress l.output (BitVec.ofNat 16 i)=cursor l.output 18 i+14 := by
    rw [←inv.registers.output,input.record]
    simp [E1M1NoiseGraph.sideAddress,BitVec.add_comm,row]
  have current := E1M1NoiseImage.read_word emitted
  rw [address] at current
  refine ⟨⟨regs,source_frame l _ _ inv.image stable,?_,fun p hp => (stable p hp).trans (inv.preserved p hp)⟩,latch.1⟩
  intro j hj
  by_cases same : j.val=i
  · have : j=row := Fin.ext same
    subst j
    exact current
  · exact (frame _ (earlier_safe l layout i j.val 14 s inv.registers inside (by omega) (by decide))).trans
      (inv.outputs j (by omega))

/-- The invariant is proved inductively from one explicit incoming state. -/
theorem states_invariant (l : LayoutData) (layout : Layout l) (s : X86Memory.State)
    (f : Option Flags) (initial : Incoming l s) (n : Nat) (bound : n≤648) :
    Invariant l s.memory n (states s f n).core ∧
      (states s f n).pc=(if n<648 then 0x2e46a else 0x2e4dd) := by
  induction n with
  | zero =>
    exact ⟨⟨initial.registers,initial.image,by intro row h; omega,by intro p hp; rfl⟩,rfl⟩
  | succ n ih =>
    exact invariant_step l layout s.memory n (states s f n).core (ih (by omega)).1 (by omega)

/-- Actual byte-prefix composition, including every helper CALL/RET and latch. -/
theorem loop_path (l : LayoutData) (layout : Layout l) (s : X86Memory.State)
    (f : Option Flags) (initial : Incoming l s) (n : Nat) (bound : n≤648) :
    ∃ k≤n*(3*(202*2147483647+30)+36),
      X86ByteRoutine.Prefix E1M1AimSideLookup.iterationProgram [] k
        ⟨s,f,0x2e46a⟩ (states s f n) := by
  induction n with
  | zero => exact ⟨0,by omega,by constructor⟩
  | succ n ih =>
    obtain ⟨k,hk,path⟩ := ih (by omega)
    obtain ⟨m,hm,segment⟩ := body_execution (states s f n).core (states s f n).flags
    have pc : (states s f n).pc=0x2e46a := by
      rw [(states_invariant l layout s f initial n (by omega)).2,if_pos (by omega)]
    have seam : (⟨(states s f n).core,(states s f n).flags,0x2e46a⟩ : X86Control.State)=states s f n := by rw [←pc]
    rw [seam] at segment
    exact ⟨k+m,by omega,path.trans segment⟩

/-- All 648 bodies terminate at the real cleanup boundary. Catalog construction,
loader entry/allocation, and cleanup execution are NOT claimed. -/
theorem execution (l : LayoutData) (placement : Layout l) (s : X86Memory.State)
    (f : Option Flags) (initial : Incoming l s) :
    (∃ k≤648*(3*(202*2147483647+30)+36),
      X86ByteRoutine.Prefix E1M1AimSideLookup.iterationProgram [] k
        ⟨s,f,0x2e46a⟩ (states s f 648)) ∧
    (states s f 648).pc=0x2e4dd ∧
    Outputs l 648 (states s f 648).core.memory ∧
    (∀ p, Persistent l p → load32 (states s f 648).core.memory p=load32 s.memory p) := by
  have result := states_invariant l placement s f initial 648 (by decide)
  exact ⟨loop_path l placement s f initial 648 (by decide),
    by simpa using result.2,result.1.outputs,result.1.preserved⟩

/-- Every earlier record's four-byte windows survive the whole remaining loop.
The guard is a single static region layout, not a repeated Kept assumption. -/
theorem earlier_words (l : LayoutData) (layout : Layout l) (s : X86Memory.State)
    (f : Option Flags) (initial : Incoming l s) (j start count off : Nat)
    (earlier : j<start) (bound : start+count≤648) (fits : off+4≤18) :
    load32 (states s f (start+count)).core.memory (cursor l.output 18 j+BitVec.ofNat 32 off)=
      load32 (states s f start).core.memory (cursor l.output 18 j+BitVec.ofNat 32 off) := by
  induction count with
  | zero => rfl
  | succ count ih =>
    have inv := (states_invariant l layout s f initial (start+count) (by omega)).1
    let row : Fin 648 := ⟨start+count,by omega⟩
    have ready := body_ready l layout row _ inv.registers inv.image
    have frame := body_frame _ _ _ _ _ _ _ (pinned_body_catalog _ l.table l.pointer row ready) _
      (earlier_safe l layout (start+count) j off _ inv.registers (by omega) (by omega) fits)
    exact frame.trans (ih (by omega))

end Doom.Proofs.E1M1AimSideLoop
