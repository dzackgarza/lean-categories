/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Catalogue.Semantics.Foundation.FiniteSubsetLiterals

@[expose] public section

/-!
# Finite-subset literals: denotation, evaluation and cardinality

Over the catalogue's own declarations: the literal form `lit.sets.finite_subsets` of the power
object `pow.sets` (`FiniteSubsetLiterals.literal`), the operations `∪ ∩ \ △` of the Boolean algebra
`𝒫(X)` applied through the registered product cone `lim.sets.product`, and the registered
cardinality functor `fun.sets.cardinality` with the cardinal literals `lit.cardinals`.

Equality in `𝒫(ℤ) = Set ℤ` is not decidable in general; between literals it is. An equation
between an operation's image of literals and a literal is decided by rewriting the image to a
literal (the generic lemmas `union_literal`, …, `cardinality_literal`) and `decide`, whose proof is
a kernel evaluation of equality of `Finset`s (resp. of cardinal literals).
-/

namespace CasCatalogue.FiniteSubsetLiteralTests

open CategoryTheory
open CasCatalogue.Foundation.PowerSets CasCatalogue.Foundation.FiniteSubsetLiterals
open CasCatalogue.Foundation.Cardinality

/-- The literal `[1, 2, 3]` denotes the subset `{1, 2, 3} ⊆ ℤ`. -/
example : ConcreteCategory.hom (C := Type) (literal ℤ [1, 2, 3].toFinset) 0 =
    ({1, 2, 3} : Set ℤ) := by
  ext x; simp [literal]

/-- Reordered and repeated lists are the same literal, and denote the same subset. -/
example : literal ℤ [3, 1, 2, 2].toFinset = literal ℤ [1, 2, 3].toFinset := by decide

/-- `{1, 2, 3} ≠ {1, 2}` in `𝒫(ℤ)`. -/
example : literal ℤ {1, 2, 3} ≠ literal ℤ {1, 2} := by decide

/-- `{1, 2, 3} ∪ {3, 4, 5} = {1, 2, 3, 4, 5}` in `𝒫(ℤ)`. -/
example : applyBinary (union (boolPowerSet ℤ)) (literal ℤ {1, 2, 3}) (literal ℤ {3, 4, 5}) =
    literal ℤ {1, 2, 3, 4, 5} := by
  rw [union_literal]; decide

/-- `{1, 2, 3} ∪ {3, 4, 5} ≠ {1, 2, 3, 4}` in `𝒫(ℤ)`. -/
example : applyBinary (union (boolPowerSet ℤ)) (literal ℤ {1, 2, 3}) (literal ℤ {3, 4, 5}) ≠
    literal ℤ {1, 2, 3, 4} := by
  rw [union_literal]; decide

/-- `{1, 2, 3} ∩ {3, 4, 5} = {3}` in `𝒫(ℕ)`. -/
example : applyBinary (inter (boolPowerSet ℕ)) (literal ℕ {1, 2, 3}) (literal ℕ {3, 4, 5}) =
    literal ℕ {3} := by
  rw [inter_literal]; decide

/-- `{0, 1, 2} \ {2, 3} = {0, 1}` in `𝒫(ℤ/5)`. -/
example : applyBinary (diff (boolPowerSet (ZMod 5))) (literal (ZMod 5) {0, 1, 2})
    (literal (ZMod 5) {2, 3}) = literal (ZMod 5) {0, 1} := by
  rw [diff_literal]; decide

/-- `{0, 1, 2} △ {2, 3} = {0, 1, 3}` in `𝒫(Fin 4)`, and not `{0, 1}`. -/
example : applyBinary (Foundation.PowerSets.symmDiff (boolPowerSet (Fin 4)))
    (literal (Fin 4) {0, 1, 2})
    (literal (Fin 4) {2, 3}) = literal (Fin 4) {0, 1, 3} := by
  rw [symmDiff_literal]; decide

example : applyBinary (Foundation.PowerSets.symmDiff (boolPowerSet (Fin 4)))
    (literal (Fin 4) {0, 1, 2})
    (literal (Fin 4) {2, 3}) ≠ literal (Fin 4) {0, 1} := by
  rw [symmDiff_literal]; decide

/-- `{-1, 2} ∪ {2, 3} = {-1, 2, 3}` in `𝒫(ℚ)`. -/
example : applyBinary (union (boolPowerSet ℚ)) (literal ℚ {-1, 2}) (literal ℚ {2, 3}) =
    literal ℚ {-1, 2, 3} := by
  rw [union_literal]; decide

/-- `|{1, 2, 3}| = 3`, by the cardinality functor. -/
example : setsCardinality.obj (⟨extent ℤ (literal ℤ {1, 2, 3})⟩ : Core Type) =
    CardinalLiteral.denote 3 := by
  rw [cardinality_literal]; decide

/-- `|{1, 2, 2, 3}| ≠ 4` and `≠ ℵ₀`: a repeated element is counted once. -/
example : setsCardinality.obj (⟨extent ℤ (literal ℤ [1, 2, 2, 3].toFinset)⟩ : Core Type) ≠
    CardinalLiteral.denote 4 := by
  rw [cardinality_literal]; decide

example : setsCardinality.obj (⟨extent ℤ (literal ℤ {1, 2, 3})⟩ : Core Type) ≠
    CardinalLiteral.denote .aleph0 := by
  rw [cardinality_literal]; decide

/-- `|{1, 2, 3} ∪ {3, 4, 5}| = 5`. -/
example : setsCardinality.obj (⟨extent ℤ (applyBinary (union (boolPowerSet ℤ))
    (literal ℤ {1, 2, 3}) (literal ℤ {3, 4, 5}))⟩ : Core Type) = CardinalLiteral.denote 5 := by
  rw [union_literal, cardinality_literal]; decide

end CasCatalogue.FiniteSubsetLiteralTests
