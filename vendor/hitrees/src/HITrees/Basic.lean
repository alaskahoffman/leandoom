namespace HITrees

inductive HITree.Raw (I O : Type u) (ρ : Type v) : Type (max u v) where
  | unreachable
  | pure (r : ρ)
  | impure (i : I) (k : O → HITree.Raw I O ρ)

instance [Inhabited ρ] : Inhabited (HITree.Raw I O ρ) where
  default := .pure default

instance(priority:=low) : Inhabited (HITree.Raw I O ρ) where
  default := .unreachable

def HITree.Raw.map {I O : Type u} {ρ ρ' : Type v} (t : HITree.Raw I O ρ) (f : ρ → ρ')
  := match t with
    | .unreachable => HITree.Raw.unreachable
    | .pure r => HITree.Raw.pure (f r)
    | .impure i k => HITree.Raw.impure i (λ x => map (k x) f)

structure Effect : Type (u + 1) where
  I : Type u
  O : Type u

abbrev HITree.{u} (E : Effect.{u}) := HITree.Raw.{u} E.I E.O

def HITree.unreachable {E : Effect} {ρ : Type v} : HITree E ρ :=
  HITree.Raw.unreachable

abbrev HITree.pure {E : Effect} {ρ : Type v} (r : ρ) : HITree E ρ :=
  HITree.Raw.pure r

abbrev HITree.impure {E : Effect.{u}} {ρ : Type v} (i : E.I) (k : E.O → HITree E ρ) : HITree E ρ :=
  HITree.Raw.impure i k

def HITree.bind {E : Effect.{u}} {ρ : Type v} {ρ' : Type w} (t : HITree E ρ) (f : ρ → HITree E ρ')
  := match t with
    | .unreachable => unreachable
    | .pure r => f r
    | .impure i k => impure i (λ x => bind (k x) f)

@[always_inline, simp]
def HITree.Raw.bind {E : Effect.{u}} {ρ : Type v} {ρ' : Type w} (t : HITree.Raw E.I E.O ρ) (f : ρ → HITree.Raw E.I E.O ρ')
    : HITree E ρ'
  := HITree.bind t f

@[simp]
theorem HITree.bind_pure {E : Effect} (r : ρ) (f : ρ → HITree E ρ') :
    (@pure E ρ r).bind f = f r := by rfl

@[simp]
theorem HITree.bind_impure {E : Effect} i k (f : ρ → HITree E ρ') :
    (impure i k).bind f = impure i (λ x => (k x).bind f) := by rfl

@[simp]
theorem HITree.bind_pure_comp {E : Effect} {ρ : Type u} {t : HITree E ρ} :
    (t.bind pure) = t := by
  induction t with
  | unreachable => simp [bind, unreachable]
  | pure r => simp
  | impure i k ih => simp; apply funext; intros a; exact ih a

@[simp]
theorem HITree.bind_assoc {E : Effect} (t : HITree E α) (k₁ : α → HITree E β) (k₂ : β → HITree E γ) :
    (t.bind k₁).bind k₂ = t.bind (λ a => (k₁ a).bind k₂) := by
  induction t with
  | unreachable => simp [bind, unreachable]
  | pure r => simp
  | impure i k ih => simp; apply funext; intros a; exact ih a

instance gtreeMonad.{u, v} {E : Effect.{u}} : Monad (HITree.{u, v} E) where
  pure := HITree.pure
  bind := HITree.bind

instance : LawfulMonad (HITree E) where
  map_const := by simp [Functor.mapConst, Functor.map]
  id_map := by simp [Functor.map]
  seqLeft_eq := by
    simp [Functor.map, SeqLeft.seqLeft, Seq.seq];
    unfold Function.const; grind
  seqRight_eq := by
    simp [Functor.map, SeqRight.seqRight, Seq.seq];
  pure_seq := by simp [pure, Seq.seq, Functor.map]
  bind_pure_comp := by
    intros
    simp [Bind.bind, Functor.map, pure];
    unfold Function.comp; rfl
  bind_map := by simp [Bind.bind, Seq.seq, Functor.map]
  pure_bind := by simp [pure, Bind.bind]
  bind_assoc := by simp [Bind.bind]

def HITree.map {E : Effect} {ρ ρ' : Type u} (t : HITree E ρ) (f : ρ → ρ')
  := HITree.Raw.map t f

@[simp]
def HITree.elim {E : Effect} (t : HITree E Empty) : HITree E ρ := t.bind Empty.elim

@[always_inline, simp]
def HITree.Raw.elim {E : Effect} (t : HITree.Raw E.I E.O Empty) : HITree E ρ := HITree.elim t

/--
  Means that `E` unfolds to `EPre`

  The `fix_effect E := ...` syntax, will generate `UnfoldEffect E (E.Pre E)`.
  If interpreters create instances for `EPre` based on its structure
  (it's usually a sum of effects), they should create instances that
  converts these instances to instances for E. See `Subeffect.derivedSub`
  or `Exec.derivedEH` as examples.

  An equivalence isn't used because we need it to be directed,
  instances for `E` shouldn't be converted to `EPre`.
-/
class UnfoldEffect (E : Effect) (EPre : outParam Effect) where
  injI : E.I → EPre.I
  invI : EPre.I → E.I
  injI_invI : ∀ i, injI (invI i) = i
  invI_injI : ∀ i, invI (injI i) = i
  out_eq : E.O = EPre.O
