/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Catalogue.Semantics.Foundation.FiniteSubsets
public import LeanCategories.Catalogue.Semantics.Foundation.Cardinality
public import LeanCategories.Catalogue.Semantics.Limits.Registration
public import Mathlib.SetTheory.Cardinal.Finite
public meta import LeanCategories.Catalogue.Registry.Semantic
public meta import Lean.Elab.Tactic.Basic
public meta import Lean.Meta.Tactic.Rewrite
public meta import Lean.Meta.Tactic.Delta
public meta import Lean.Meta.Tactic.Replace

@[expose] public section

/-!
# Finite-subset literals of the power objects of `Sets`

The literal form `lit.sets.finite_subsets` of the power object `pow.sets`: a literal at a set `X`
with decidable equality is a finite subset `s : Finset X`, and it denotes the element
`{a₁, …, aₙ} ↦ {a₁, …, aₙ} ⊆ X` of `𝒫(X)`, the global element `1 ⟶ 𝒫 X` at `↑s`. It is the
element `s` of `𝒫_fin(X)` followed by the registered inclusion `𝒫_fin(X) ↪ 𝒫(X)`
(`literal_eq_comp_inclusion`).

**Normal form.** `Finset X` is the quotient of the lists of elements of `X` by reordering and
repetition (Mathlib: `Multiset` is `List` modulo `List.Perm`, a `Finset` is a duplicate-free
multiset, `List.toFinset` the quotient map). So `[1, 2, 3]`, `[3, 1, 2]` and `[1, 2, 2, 3]` are
the same literal, and equality of literals is equality of the subsets they denote
(`literal_inj`, from `Finset.coe_inj`). It is decided by kernel evaluation whenever equality on `X`
is: ℕ, ℤ, `ZMod n`, `Fin n`, and ℚ (for ℚ, `decide` reduces integer numerals; a fraction such as
`1 / 2` reduces through `Rat.inv`, which the elaborator does not unfold, and needs
`decide +kernel`). `ℝ` has no decidable equality and no literal form here.

**Evaluation.** Equality in `𝒫(X) = Set X` is not decidable in general. Between denotations of
literals it is (`decidableEqLiteral`). The Boolean-algebra operations `∪ ∩ \ △` on `𝒫(X)`,
applied as the catalogue applies a binary operation (the pair is the mediator of the registered
product cone `lim.sets.product`), send literals to the literal of the corresponding `Finset`
operation (`union_literal`, `inter_literal`, `diff_literal`, `symmDiff_literal`): the images of
literals are literals. So `A ∪ B = {1, 2, 3, 4, 5}` for literals `A`, `B` is decided by rewriting
with these lemmas and `decide`. The literal form registers that rewriting as its evaluation
(`evaluation`, the row's `evaluation` field): it removes the expected-type hints and the other
spelling of a functor's action that a consumer's terms carry, rewrites every image of literals to a
literal, and leaves the statement between literals for `decide`.

The literals agree with the power object's own formation of finite subsets from `∅`, singletons
and `∪` (`literal_empty`, `literal_insert`).

**Cardinality.** The cardinality method (`card : Core(Sets) ⥤ Disc(Card)`) sends the extent of a
literal `s` to the cardinal literal `s.card` (`cardinality_literal`, `Cardinal.mk_coe_finset`), and
equality of cardinal literals' denotations is decided on the literals
(`CardinalLiteral.decidableEqDenote`). So `|{1, 2, 3}| = 3` is decided by rewriting and `decide`.
-/

open CategoryTheory Limits

namespace CasCatalogue.Foundation.FiniteSubsetLiterals

open CasCatalogue.Foundation.PowerSets CasCatalogue.Foundation.Objects
open CasCatalogue.Foundation.FiniteSubsets CasCatalogue.Foundation.Cardinality
open CasCatalogue.Limits.Registration

/-- The element `{a₁, …, aₙ} ⊆ X` of `𝒫(X)` that the literal `s = {a₁, …, aₙ}` denotes. The
decidable equality of `X` is that of the literal form, `Finset X`, on which the operations
`∪ ∩ \ △` of literals are computed. -/
def literal (X : Type) [DecidableEq X] (s : Finset X) : fin 1 ⟶ powerSet X :=
  TypeCat.ofHom fun _ => (s : Set X)

variable {X : Type} [DecidableEq X]

/-- The literal `s` is the element `s` of `𝒫_fin(X)` included into `𝒫(X)`. -/
theorem literal_eq_comp_inclusion (s : Finset X) :
    literal X s = (TypeCat.ofHom fun _ => s : fin 1 ⟶ finiteSubsets X) ≫ inclusion X := rfl

/-- Two literals denote the same subset exactly when they are the same literal. -/
theorem literal_inj {s t : Finset X} : literal X s = literal X t ↔ s = t := by
  refine ⟨fun h => ?_, congrArg _⟩
  have h := congrArg (fun f => ConcreteCategory.hom (C := Type) f 0) h
  exact Finset.coe_inj.mp h

/-- Equality of the subsets two literals denote is decided on the literals. -/
instance decidableEqLiteral (s t : Finset X) : Decidable (literal X s = literal X t) :=
  decidable_of_iff (s = t) literal_inj.symm

/-- The element `op(A, B)` of `𝒫(X)`, formed as the catalogue forms it: the pair `(A, B)` is the
mediator of the registered product cone `lim.sets.product` on `𝒫 X × 𝒫 X`, followed by the
operation `𝒫 X × 𝒫 X → 𝒫 X`. It is notation for that composite. The evaluation lemmas below are
stated on the composite itself, the term the catalogue forms, and not on this abbreviation: `rw`
finds an occurrence by its head symbol (`CategoryStruct.comp`) and does not unfold an
abbreviation. They state its endpoints as the catalogue does, `1 ⟶ apex ⟶ 𝒫 X`; the composite
`lift _ ≫ op` elaborated by itself has instead the apex of the fan `BinaryFan.mk A B` as its
source and the carrier of the Boolean algebra `𝒫 X` as its target. -/
abbrev applyBinary
    (op : (boolCarrier (boolPowerSet X) × boolCarrier (boolPowerSet X) : SetsCat.{0}) ⟶
      (boolCarrier (boolPowerSet X) : SetsCat.{0}))
    (A B : fin 1 ⟶ powerSet X) : fin 1 ⟶ powerSet X :=
  @CategoryStruct.comp SetsCat.{0} _ (fin 1) (setsProduct (pair (powerSet X) (powerSet X))).cone.pt
    (powerSet X) ((setsProduct (pair (powerSet X) (powerSet X))).isLimit.lift (BinaryFan.mk A B)) op

theorem union_literal (s t : Finset X) :
    @CategoryStruct.comp SetsCat.{0} _ (fin 1) (setsProduct (pair (powerSet X) (powerSet X))).cone.pt
      (powerSet X)
      ((setsProduct (pair (powerSet X) (powerSet X))).isLimit.lift
        (BinaryFan.mk (literal X s) (literal X t)))
      (union (boolPowerSet X)) = literal X (s ∪ t) := by
  apply ConcreteCategory.hom_ext; intro p
  simp [literal, union]; rfl

theorem inter_literal (s t : Finset X) :
    @CategoryStruct.comp SetsCat.{0} _ (fin 1) (setsProduct (pair (powerSet X) (powerSet X))).cone.pt
      (powerSet X)
      ((setsProduct (pair (powerSet X) (powerSet X))).isLimit.lift
        (BinaryFan.mk (literal X s) (literal X t)))
      (inter (boolPowerSet X)) = literal X (s ∩ t) := by
  apply ConcreteCategory.hom_ext; intro p
  simp [literal, inter]; rfl

theorem diff_literal (s t : Finset X) :
    @CategoryStruct.comp SetsCat.{0} _ (fin 1) (setsProduct (pair (powerSet X) (powerSet X))).cone.pt
      (powerSet X)
      ((setsProduct (pair (powerSet X) (powerSet X))).isLimit.lift
        (BinaryFan.mk (literal X s) (literal X t)))
      (diff (boolPowerSet X)) = literal X (s \ t) := by
  apply ConcreteCategory.hom_ext; intro p
  simp [literal, diff]; rfl

theorem symmDiff_literal (s t : Finset X) :
    @CategoryStruct.comp SetsCat.{0} _ (fin 1) (setsProduct (pair (powerSet X) (powerSet X))).cone.pt
      (powerSet X)
      ((setsProduct (pair (powerSet X) (powerSet X))).isLimit.lift
        (BinaryFan.mk (literal X s) (literal X t)))
      (PowerSets.symmDiff (boolPowerSet X)) = literal X (_root_.symmDiff s t) := by
  apply ConcreteCategory.hom_ext; intro p
  simp [literal, PowerSets.symmDiff, Finset.coe_symmDiff]; rfl

/-- The empty literal is the power object's `∅`. -/
theorem literal_empty : literal X ∅ = empty X := by
  apply ConcreteCategory.hom_ext; intro p
  simp [literal, empty]

/-- `{x} ∪ s`, formed from the power object's singleton and `∪`, is the literal `insert x s`. -/
theorem literal_insert (x : fin 1 ⟶ (X : SetsCat.{0})) (s : Finset X) :
    applyBinary (union (boolPowerSet X)) (x ≫ singleton X) (literal X s) =
      literal X (insert (ConcreteCategory.hom (C := Type) x 0) s) := by
  apply ConcreteCategory.hom_ext; intro p
  obtain rfl : p = 0 := Subsingleton.elim _ _
  change {ConcreteCategory.hom (C := Type) x (0 : Fin 1)} ∪ (s : Set X) =
    ((insert (ConcreteCategory.hom (C := Type) x 0) s : Finset X) : Set X)
  rw [Finset.coe_insert, Set.insert_eq]

/-- `|s|`: the cardinality method sends the extent of the literal `s` to the cardinal literal
`s.card` (`Cardinal.mk_coe_finset`). It is stated with Mathlib's spelling of a functor's action
on objects, `Functor.obj F X`, a reducible definition `F.toPrefunctor.obj X` whose head is
`Functor.obj`; the other spelling, `Prefunctor.obj F.toPrefunctor X` (head `Prefunctor.obj`), is
folded to it by `foldFunctorActions` before the evaluation rewrites. -/
theorem cardinality_literal (s : Finset X) :
    setsCardinality.obj (⟨extent X (literal X s)⟩ : Core (Type)) =
      CardinalLiteral.denote (.finite s.card) := by
  apply Discrete.ext
  exact Cardinal.mk_coe_finset

/-- The evaluation of the literal form: the statements whose images of literals it rewrites to
literals. One per operation of the catalogue on `𝒫 X` (the Boolean-algebra operations `∪ ∩ \ △`
applied through the product cone) and per functor out of it (the cardinality, into the cardinal
literals). They are stated for every set `X` with decidable equality and all literals `s`, `t`. -/
meta def evaluationLemmas : Array Lean.Name :=
  #[``union_literal, ``inter_literal, ``diff_literal, ``symmDiff_literal, ``cardinality_literal]

open Lean Meta in
/-- Fold the two spellings of a functor's actions to Mathlib's: `Prefunctor.obj F.toPrefunctor X`
to `Functor.obj F X` and `Prefunctor.map F.toPrefunctor f` to `Functor.map F f`. `Functor.obj` and
`Functor.map` are reducible definitions whose values are those terms, so the result is
definitionally the input. A term formed by applying `Prefunctor.obj` to `Functor.toPrefunctor F`
(as `mkAppM` forms it) has head `Prefunctor.obj`, and `rw` and `simp` find a statement about
`F.obj X` by its head `Functor.obj`: without this fold they find none. -/
meta def foldFunctorActions (e : Expr) : MetaM Expr :=
  Core.transform e (post := fun e => do
    let fn := e.getAppFn
    let args := e.getAppArgs
    let fold (functorAction : Name) : Option Expr := do
      -- `Prefunctor.{obj,map} V instV W instW P …` with `P = Functor.toPrefunctor C iC D iD F`.
      let prefunctor ← args[4]?
      guard (prefunctor.isAppOfArity ``CategoryTheory.Functor.toPrefunctor 5)
      let .const _ levels := prefunctor.getAppFn | none
      return mkAppN (.const functorAction levels) (prefunctor.getAppArgs ++ args.extract 5)
    let folded := match fn.constName? with
      | some ``Prefunctor.obj => fold ``CategoryTheory.Functor.obj
      | some ``Prefunctor.map => fold ``CategoryTheory.Functor.map
      | _ => none
    return .continue folded)

open Lean Meta in
/-- Rewrite the goal once with the first statement of `evaluationLemmas` that has an occurrence
in it (all occurrences of its first instance, as `rw` does); `none` when none has. -/
meta def rewriteOnce (goal : MVarId) : MetaM (Option MVarId) := goal.withContext do
  for statement in evaluationLemmas do
    let saved ← saveState
    try
      let result ← goal.rewrite (← goal.getType) (← mkConstWithFreshMVarLevels statement)
      unless result.mvarIds.isEmpty do
        throwError "{statement} leaves hypotheses to prove"
      return some (← goal.replaceTargetEq result.eNew result.eqProof)
    catch _ =>
      saved.restore
  return none

open Lean Meta Elab Tactic in
/-- The registered evaluation of `lit.sets.finite_subsets`. On the main goal it first unfolds the
expected-type hints `@id T a` to `a` (a consumer inserts them to fix the type at which a subterm is
elaborated; they are definitionally `a`, and a hint is a constant `rw` would have to see through)
and the notation `applyBinary` to the composite it abbreviates, and folds a functor's action
spelled `Prefunctor.obj F.toPrefunctor X` to `F.obj X` (`foldFunctorActions`). It then rewrites
with the statements of `evaluationLemmas` until none has an occurrence. Each rewriting replaces
an image of literals under an operation by the literal it equals, so the loop terminates, and an
image becomes a literal for the operation around it: in `|A ∪ B|`, first `A ∪ B` becomes a
literal, then its cardinality a cardinal literal. The rewriting is `rw`'s (`MVarId.rewrite`:
occurrences found by head symbol and definitional equality at instance transparency), with no
other lemma and no simproc. It never closes the goal: a statement between literals remains,
decided on the literals (`decide`, by `decidableEqLiteral` and
`CardinalLiteral.decidableEqDenote`). A goal with no image of literals is left as it is, up to
the unfolding of hints. -/
meta def evaluation : TacticM Unit := liftMetaTactic fun goal => goal.withContext do
  let target ← instantiateMVars (← goal.getType)
  let unfolded ← deltaExpand target fun name => name == ``id || name == ``applyBinary
  let unfolded ← foldFunctorActions unfolded
  let mut goal ← goal.replaceTargetDefEq unfolded
  let mut progress := true
  while progress do
    match ← rewriteOnce goal with
    | some next => goal := next
    | none => progress := false
  return [goal]

end CasCatalogue.Foundation.FiniteSubsetLiterals

namespace CasCatalogue

normalized_registry .subsetLiteral
  { id := ⟨"lit.sets.finite_subsets"⟩, powerObject := ⟨"pow.sets"⟩
    type := `Finset
    denotation := `CasCatalogue.Foundation.FiniteSubsetLiterals.literal
    evaluation := some `CasCatalogue.Foundation.FiniteSubsetLiterals.evaluation }

end CasCatalogue
