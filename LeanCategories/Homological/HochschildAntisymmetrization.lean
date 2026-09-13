/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Homological.AlgebraicDeRham
public import LeanCategories.Homological.HochschildComplex

/-!
# Normalized antisymmetrization from Hochschild chains to differential forms

Weibel, *An Introduction to Homological Algebra* (1994), Construction 9.8.12,
pp. 344--353 (FC05-C09-U128).

For a commutative algebra `R` containing `ℚ`, Weibel uses the normalized map

`e(r₀ ⊗ r₁ ⊗ ... ⊗ rₙ) = (1 / n!) r₀ dr₁ ∧ ... ∧ drₙ`.

This file records that chain-level construction.  The assertions that `e b = 0`
and that `e` identifies the top Hodge Hochschild summand with differential forms
are result-level clauses and are deliberately left to the theorem sweep.
-/

@[expose] public noncomputable section

namespace LeanCategories.Homological

open CategoryTheory
open scoped TensorProduct

universe u

variable (k : Type u) [CommRing k]
variable (R : Type u) [CommRing R] [Algebra k R] [Algebra ℚ R]

/-- The normalized pure-tensor value
`(1/n!) r₀ dr₁ ∧ ... ∧ drₙ` from Weibel Construction 9.8.12. -/
def normalizedAntisymmetrizationPure {n : ℕ} (r₀ : R) (a : Fin n → R) :
    DeRhamDegree k R n :=
  algebraMap ℚ R ((n.factorial : ℚ)⁻¹) • deRhamPureForm k R r₀ a

/-- A realization of Weibel's normalized antisymmetrization map
`e : R ⊗_k R^{⊗ n} → Ω^n_{R/k}`.

The `map_pure` field is exactly the defining formula.  Compatibility with the
Hochschild differential and the Hodge projector is theorem-layer content. -/
structure HochschildAntisymmetrizationRealization (n : ℕ) where
  /-- The normalized antisymmetrization in Hochschild degree `n`. -/
  map : ModuleCat.of k (HochschildChainDegree (k := k) (R := R) (M := R) n) ⟶
    ModuleCat.of k (DeRhamDegree k R n)
  /-- The map has Weibel's normalized formula on pure Hochschild chains. -/
  map_pure : ∀ (r₀ : R) (a : Fin n → R),
    map (hochschildChainPure (k := k) (R := R) (M := R) r₀ a) =
      normalizedAntisymmetrizationPure k R r₀ a

end LeanCategories.Homological
