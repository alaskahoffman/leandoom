import Doom.Verification.X86Memory

namespace Doom.Proofs.InitializedAddress
open Verification X86Memory

/-- Typed observations, not a blanket relocation of numeric values. Addresses
are canonical data offsets; only `.pointer` values are translated. -/
inductive Read where
  | scalar (address value : Word)
  | pointer (address value : Word)
  | short (address : Word) (value : BitVec 16)
  deriving DecidableEq

def Read.address : Read → Word
  | .scalar a _ | .pointer a _ | .short a _ => a

def Read.size : Read → Nat
  | .short .. => 2
  | _ => 4

/-- Ordinary captured RAM only. Natural bounds prohibit modular address wrap.
The extent is an input identifying the retained RAM backing, not device memory. -/
def Address (base extent : Nat) (r : Read) : Prop :=
  0x100000 ≤ base + r.address.toNat ∧
  base + r.address.toNat + r.size ≤ extent ∧ extent ≤ 2^32
instance (base extent : Nat) (r : Read) : Decidable (Address base extent r) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- Null remains null; nonnull pointers must be above the data base, in retained
ordinary RAM, and are translated exactly once. No executable relocation claim. -/
def Pointer (base extent : Nat) (raw canonical : Word) : Prop :=
  (raw = 0 ∧ canonical = 0) ∨
  (base < raw.toNat ∧ 0x100000 ≤ raw.toNat ∧ raw.toNat < extent ∧
    canonical.toNat = raw.toNat-base)
instance (base extent : Nat) (raw canonical : Word) : Decidable (Pointer base extent raw canonical) :=
  inferInstanceAs (Decidable (_ ∨ _))

def Encodes (m : Memory) : Read → Prop
  | .scalar a v | .pointer a v => load32 m a=v
  | .short a v => load16 m a=v
instance (m : Memory) (r : Read) : Decidable (Encodes m r) := by
  cases r <;> unfold Encodes <;> infer_instance

/-- Read-local provenance between two *single incoming* byte memories. The
canonical image may differ at typed pointer bytes; scalar reads must agree. -/
def Observed (raw canonical : Memory) (base extent : Nat) : Read → Prop
  | .scalar a _ => load32 canonical a=load32 raw (BitVec.ofNat 32 base+a)
  | .short a _ => load16 canonical a=load16 raw (BitVec.ofNat 32 base+a)
  | .pointer a _ => Pointer base extent
      (load32 raw (BitVec.ofNat 32 base+a)) (load32 canonical a)
instance (raw canonical : Memory) (base extent : Nat) (r : Read) :
    Decidable (Observed raw canonical base extent r) := by
  cases r <;> unfold Observed <;> infer_instance

def check (raw canonical : Memory) (base extent : Nat) (reads : List Read) : Bool :=
  reads.all fun r => decide (Address base extent r ∧
    Observed raw canonical base extent r ∧ Encodes canonical r)

/-- Checking finite typed reads derives both provenance and canonical contents;
it assumes neither a machine execution nor any future read or state. -/
theorem sound (raw canonical : Memory) (base extent : Nat) (reads : List Read)
    (checked : check raw canonical base extent reads=true) :
    ∀ r∈reads, Address base extent r ∧
      Observed raw canonical base extent r ∧ Encodes canonical r := by
  intro r member
  exact of_decide_eq_true ((List.all_eq_true.mp checked) r member)

theorem encodes (raw canonical : Memory) (base extent : Nat) (reads : List Read)
    (checked : check raw canonical base extent reads=true) :
    ∀ r∈reads, Encodes canonical r := by
  intro r member
  exact (sound raw canonical base extent reads checked r member).2.2

theorem pointer_translation (raw canonical : Memory) (base extent : Nat)
    (reads : List Read) (checked : check raw canonical base extent reads=true)
    (a v : Word) (member : Read.pointer a v∈reads) :
    Pointer base extent (load32 raw (BitVec.ofNat 32 base+a)) v := by
  have h := sound raw canonical base extent reads checked _ member
  have value : load32 canonical a=v := h.2.2
  have observed : Pointer base extent (load32 raw (BitVec.ofNat 32 base+a))
      (load32 canonical a) := h.2.1
  rwa [value] at observed

theorem scalar_preserved (raw canonical : Memory) (base extent : Nat)
    (reads : List Read) (checked : check raw canonical base extent reads=true)
    (a v : Word) (member : Read.scalar a v∈reads) :
    load32 raw (BitVec.ofNat 32 base+a)=v := by
  have h := sound raw canonical base extent reads checked _ member
  exact h.2.1.symm.trans h.2.2
/-- The address checked in natural arithmetic is exactly the physical word
address consumed by load32/load16, without modular wrap or base truncation. -/
theorem address_exact (base extent : Nat) (r : Read) (h : Address base extent r) :
    (BitVec.ofNat 32 base+r.address).toNat=base+r.address.toNat := by
  have positive : 0<r.size := by cases r <;> simp [Read.size]
  have small : base+r.address.toNat<2^32 := by unfold Address at h; omega
  have hb : base<2^32 := by omega
  simp only [BitVec.toNat_add,BitVec.toNat_ofNat,Nat.mod_eq_of_lt hb,Nat.mod_eq_of_lt small]

/-- A checked nonnull pointer reconstitutes its original physical value exactly;
null is handled separately and is never translated to the data base. -/
theorem pointer_reconstruct (base extent : Nat) (raw canonical : Word)
    (h : Pointer base extent raw canonical) :
    (raw=0 ∧ canonical=0) ∨
    (BitVec.ofNat 32 base+canonical=raw ∧ canonical≠0) := by
  rcases h with null|h
  · exact Or.inl null
  · right
    have hr := raw.isLt
    have hb : base<2^32 := by omega
    have sum : base+canonical.toNat=raw.toNat := by omega
    constructor
    · apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add,BitVec.toNat_ofNat,Nat.mod_eq_of_lt hb,sum,
        Nat.mod_eq_of_lt hr]
    · intro zero
      have hz := congrArg BitVec.toNat zero
      change canonical.toNat=0 at hz
      omega

/-- Finite pointer evidence in source-number form, retaining raw values. Bounds
reject oversized certificate literals instead of silently truncating them. -/
abbrev Row := Nat × Nat × Nat

def rowCheck (base extent : Nat) (r : Row) : Bool :=
  decide (r.1<2^32 ∧ r.2.1<2^32 ∧ r.2.2<2^32 ∧
    Address base extent (.pointer (BitVec.ofNat 32 r.1) (BitVec.ofNat 32 r.2.2)) ∧
    Pointer base extent (BitVec.ofNat 32 r.2.1) (BitVec.ofNat 32 r.2.2))

def rowsCheck (base extent : Nat) (rows : List Row) : Bool :=
  rows.all (rowCheck base extent)

theorem rows_append (base extent : Nat) (a b : List Row)
    (ha : rowsCheck base extent a=true) (hb : rowsCheck base extent b=true) :
    rowsCheck base extent (a++b)=true := by
  simp only [rowsCheck,List.all_append] at *
  rw [ha,hb]
  rfl

/-- Specialization uses only explicitly stated raw/canonical decoding equalities.
These equalities are the extraction boundary, not assumptions of relocation
compatibility for execution or of any future scene. -/
theorem rows_sound (base extent : Nat) (rows : List Row)
    (checked : rowsCheck base extent rows=true) (raw canonical : Memory)
    (rawDecoded : ∀ r∈rows, load32 raw (BitVec.ofNat 32 base+BitVec.ofNat 32 r.1)=BitVec.ofNat 32 r.2.1)
    (canonicalDecoded : ∀ r∈rows, load32 canonical (BitVec.ofNat 32 r.1)=BitVec.ofNat 32 r.2.2) :
    ∀ r∈rows, Address base extent (.pointer (BitVec.ofNat 32 r.1) (BitVec.ofNat 32 r.2.2)) ∧
      Observed raw canonical base extent (.pointer (BitVec.ofNat 32 r.1) (BitVec.ofNat 32 r.2.2)) := by
  intro r hr
  have h := of_decide_eq_true (List.all_eq_true.mp checked r hr)
  refine ⟨h.2.2.2.1,?_⟩
  change Pointer base extent _ _
  rw [rawDecoded r hr,canonicalDecoded r hr]
  exact h.2.2.2.2

end Doom.Proofs.InitializedAddress
