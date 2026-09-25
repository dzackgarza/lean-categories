/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Lattices.Valued.PeriodDomainData
public import Mathlib.LinearAlgebra.QuadraticForm.Signature
public import Mathlib.LinearAlgebra.TensorProduct.Tower

/-!
# Weight-two Hodge data

Definition-level realization of Peters--Sterk FC11-B-U031 (Definition B.4.1),
the period-domain construction FC11-B-U032, and marked period data
FC11-B-U034.

The source defines a weight-two Hodge structure by a direct decomposition of
the literal complexification of a finite free integral module.  TauCeti's
pinned Hodge reference instead starts from an opposed filtration and later
proves the equivalent decomposition.  Sweep III therefore records the source
decomposition directly and uses only the reference's tensor-complexification
convention.

No decomposition theorem, Hodge symmetry theorem, real-form existence theorem,
or Hodge--Riemann consequence is proved here.  The polarization and K3-type
conditions are predicates on supplied data.
-/

@[expose] public noncomputable section

open scoped ComplexOrder TensorProduct

namespace LeanCategories.Lattices.Valued

universe u

variable (L : Type u) [AddCommGroup L] [Module.Free ℤ L] [Module.Finite ℤ L]

/-- The literal complexification of the finite free integral module `L`. -/
abbrev WeightTwoComplexificationData := LatticeComplexificationData L

/-- The literal realification of the finite free integral module `L`. -/
abbrev WeightTwoRealificationData := ℝ ⊗[ℤ] L

/-- Scalar conjugation on `ℂ ⊗[ℤ] L`, reusing the period-domain owner. -/
abbrev weightTwoComplexConjugationData :=
  latticeConjugationData L

/-- The canonical map from `L_ℝ` to `L_ℂ`, induced by
`ℝ ↪ ℂ` on the scalar tensor factor. -/
def weightTwoRealToComplexData :
    WeightTwoRealificationData L →ₗ[ℤ] WeightTwoComplexificationData L :=
  TensorProduct.map Complex.ofRealHom.toAddMonoidHom.toIntLinearMap
    (LinearMap.id : L →ₗ[ℤ] L)

/-- A weight-two Hodge decomposition on a finite free integral module.

The three complex subspaces are required to form a direct decomposition of
`L_ℂ`.  The `(2,0)` and `(0,2)` pieces are exchanged by the canonical
tensor conjugation, while the `(1,1)` piece is stable under it. -/
structure WeightTwoHodgeStructureData where
  h20 : Submodule ℂ (WeightTwoComplexificationData L)
  h11 : Submodule ℂ (WeightTwoComplexificationData L)
  h02 : Submodule ℂ (WeightTwoComplexificationData L)
  span_eq_top : h20 ⊔ (h11 ⊔ h02) = ⊤
  h20_disjoint_rest : Disjoint h20 (h11 ⊔ h02)
  h11_disjoint_h02 : Disjoint h11 h02
  conj_h20_h02 :
    ∀ x, x ∈ h20 ↔ weightTwoComplexConjugationData L x ∈ h02
  conj_h02_h20 :
    ∀ x, x ∈ h02 ↔ weightTwoComplexConjugationData L x ∈ h20
  conj_h11 :
    ∀ x, x ∈ h11 ↔ weightTwoComplexConjugationData L x ∈ h11

/-- The two Riemann bilinear relations defining a polarization in
Peters--Sterk Definition B.4.1, together with symmetry and nondegeneracy of the
integral form.

The complex form is Mathlib's literal scalar extension of `Q`; no comparison
map or descent theorem is postulated. -/
def IsWeightTwoPolarizationData
    (hs : WeightTwoHodgeStructureData L)
    (Q : LinearMap.BilinForm ℤ L) : Prop :=
  Q.IsSymm ∧
    Q.Nondegenerate ∧
    (∀ u, u ∈ hs.h20 → ∀ v, v ∈ hs.h20 →
      Q.baseChange ℂ u v = 0) ∧
    (∀ u, u ∈ hs.h20 → u ≠ 0 →
      0 < Q.baseChange ℂ u (weightTwoComplexConjugationData L u))

/-- The complex span in `L_ℂ` of a real subspace of `L_ℝ`.

This is the direct data-level meaning of the notation `(L')_ℂ` used in the
source. -/
def weightTwoComplexSpanOfRealSubspaceData
    (V : Submodule ℝ (WeightTwoRealificationData L)) :
    Submodule ℂ (WeightTwoComplexificationData L) :=
  Submodule.span ℂ
    (Set.image (weightTwoRealToComplexData L) (V : Set (WeightTwoRealificationData L)))

/-- A polarized weight-two Hodge structure is of K3 type when
`dim_ℂ L^{2,0} = 1` and its real `(1,1)` part is Lorentzian.

The real `(1,1)` part is quantified rather than chosen as structure data:
its complex span must be exactly `L^{1,1}`.  The Lorentzian clause is stated
using Mathlib's positive/negative indices of the real scalar extension of the
same integral form.  Thus the source's preceding existence statement for the
real decomposition is not turned into a Sweep-III construction theorem. -/
def IsK3TypeWeightTwoHodgeData
    (hs : WeightTwoHodgeStructureData L)
    (Q : LinearMap.BilinForm ℤ L) : Prop :=
  IsWeightTwoPolarizationData L hs Q ∧
    Module.finrank ℂ hs.h20 = 1 ∧
    ∃ V : Submodule ℝ (WeightTwoRealificationData L),
      weightTwoComplexSpanOfRealSubspaceData L V = hs.h11 ∧
        sigPos ((Q.baseChange ℝ).toQuadraticMap.restrict V) = 1 ∧
        sigNeg ((Q.baseChange ℝ).toQuadraticMap.restrict V) =
          Module.finrank ℝ V - 1

/-- The positive isotropic-plane condition defining the weight-two period
domain with fixed Hodge number `h^{2,0}=p` (FC11-B-U032).

This is the concrete period-domain model displayed by Peters--Sterk.  The
statement that such a plane reconstructs, or is equivalent to, a polarized
Hodge decomposition is comparison theorem content and is not part of this
Sweep-III definition. -/
def IsWeightTwoPeriodPlaneData
    (Q : LinearMap.BilinForm ℤ L) (p : ℕ)
    (P : Submodule ℂ (WeightTwoComplexificationData L)) : Prop :=
  Module.finrank ℂ P = p ∧
    (∀ u, u ∈ P → ∀ v, v ∈ P → Q.baseChange ℂ u v = 0) ∧
    (∀ u, u ∈ P → u ≠ 0 →
      0 < Q.baseChange ℂ u (weightTwoComplexConjugationData L u))

/-- The period domain of positive isotropic `p`-planes in `L_ℂ`. -/
def weightTwoPeriodDomainData
    (Q : LinearMap.BilinForm ℤ L) (p : ℕ) :
    Set (Submodule ℂ (WeightTwoComplexificationData L)) :=
  {P | IsWeightTwoPeriodPlaneData L Q p P}

section Marking

universe v

variable {H : Type v} [AddCommGroup H] [Module.Free ℤ H] [Module.Finite ℤ H]

/-- The transported `(2,0)` subspace under an integral marking
`φ : H ≃ L` (FC11-B-U034). -/
def markedWeightTwoH20Data
    (φ : H ≃ₗ[ℤ] L) (hs : WeightTwoHodgeStructureData H) :
    Submodule ℂ (WeightTwoComplexificationData L) :=
  hs.h20.map (φ.baseChange ℤ ℂ H L).toLinearMap

/-- The transported `(1,1)` subspace under an integral marking. -/
def markedWeightTwoH11Data
    (φ : H ≃ₗ[ℤ] L) (hs : WeightTwoHodgeStructureData H) :
    Submodule ℂ (WeightTwoComplexificationData L) :=
  hs.h11.map (φ.baseChange ℤ ℂ H L).toLinearMap

/-- The transported `(0,2)` subspace under an integral marking. -/
def markedWeightTwoH02Data
    (φ : H ≃ₗ[ℤ] L) (hs : WeightTwoHodgeStructureData H) :
    Submodule ℂ (WeightTwoComplexificationData L) :=
  hs.h02.map (φ.baseChange ℤ ℂ H L).toLinearMap

/-- The period plane determined by a marking is the transported
`(2,0)` subspace. -/
abbrev markedWeightTwoPeriodPlaneData
    (φ : H ≃ₗ[ℤ] L) (hs : WeightTwoHodgeStructureData H) :
    Submodule ℂ (WeightTwoComplexificationData L) :=
  markedWeightTwoH20Data L φ hs

end Marking

end LeanCategories.Lattices.Valued
