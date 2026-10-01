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
with these lemmas and `decide`.

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
mediator of the registered product cone, followed by the operation `𝒫 X × 𝒫 X → 𝒫 X`. -/
abbrev applyBinary
    (op : (boolCarrier (boolPowerSet X) × boolCarrier (boolPowerSet X) : SetsCat.{0}) ⟶
      (boolCarrier (boolPowerSet X) : SetsCat.{0}))
    (A B : fin 1 ⟶ powerSet X) : fin 1 ⟶ powerSet X :=
  (setsProduct _ _).isLimit.lift (BinaryFan.mk A B) ≫ op

theorem union_literal (s t : Finset X) :
    applyBinary (union (boolPowerSet X)) (literal X s) (literal X t) = literal X (s ∪ t) := by
  apply ConcreteCategory.hom_ext; intro p
  simp [literal, union]; rfl

theorem inter_literal (s t : Finset X) :
    applyBinary (inter (boolPowerSet X)) (literal X s) (literal X t) = literal X (s ∩ t) := by
  apply ConcreteCategory.hom_ext; intro p
  simp [literal, inter]; rfl

theorem diff_literal (s t : Finset X) :
    applyBinary (diff (boolPowerSet X)) (literal X s) (literal X t) = literal X (s \ t) := by
  apply ConcreteCategory.hom_ext; intro p
  simp [literal, diff]; rfl

theorem symmDiff_literal (s t : Finset X) :
    applyBinary (PowerSets.symmDiff (boolPowerSet X)) (literal X s) (literal X t) =
      literal X (_root_.symmDiff s t) := by
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
`s.card` (`Cardinal.mk_coe_finset`). -/
theorem cardinality_literal (s : Finset X) :
    setsCardinality.obj (⟨extent X (literal X s)⟩ : Core (Type)) =
      CardinalLiteral.denote (.finite s.card) := by
  apply Discrete.ext
  exact Cardinal.mk_coe_finset

end CasCatalogue.Foundation.FiniteSubsetLiterals

namespace CasCatalogue

normalized_registry .subsetLiteral
  { id := ⟨"lit.sets.finite_subsets"⟩, powerObject := ⟨"pow.sets"⟩
    type := `Finset
    denotation := `CasCatalogue.Foundation.FiniteSubsetLiterals.literal }

end CasCatalogue
