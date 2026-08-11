/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Lattices.Valued.DiscriminantQuadratic
public import LeanCategories.Lattices.Valued.Gluing
public import LeanCategories.Modules.Quadratic.Valued.Witt

@[expose] public section

open LeanCategories.Modules.Bilinear.Valued
open LeanCategories.Modules.Quadratic.Valued

namespace LeanCategories.Lattices.Valued

universe u

variable {R : Type u} [CommRing R] [IsDomain R]
variable {L : IntegralLatticeCat R}

/-- The discriminant anti-isometry data used to glue two even lattices. -/
structure EvenDiscriminantGluingData
    (L M : IntegralLatticeCat R) where
  left_fractionFieldPerfect : IsFractionFieldPerfect R L
  right_fractionFieldPerfect : IsFractionFieldPerfect R M
  left_isEven : IsEven L
  right_isEven : IsEven M
  antiIsometry : EvenDiscriminantAntiIsometry L M
    left_fractionFieldPerfect right_fractionFieldPerfect
    left_isEven right_isEven

/-- Two even lattices have discriminant data which can support anti-isometric gluing. -/
def HasEvenDiscriminantGluingData
    (L M : IntegralLatticeCat R) : Prop :=
  Nonempty (EvenDiscriminantGluingData L M)

/-- An isotropic subgroup of the quadratic discriminant form of an even lattice. -/
noncomputable abbrev EvenDiscriminantIsotropicSubgroup
    (hL : IsFractionFieldPerfect R L) (hEven : IsEven L) :=
  {H : Submodule R L.obj.defect //
    (evenDiscriminantQuadraticObject L hL hEven).IsTotallyIsotropic H}

/-- A quadratic metabolizer is both quadratic-isotropic and bilinear-Lagrangian. -/
noncomputable abbrev EvenDiscriminantMetabolizer
    (hL : IsFractionFieldPerfect R L) (hEven : IsEven L) :=
  {H : Submodule R L.obj.defect //
    (evenDiscriminantQuadraticObject L hL hEven).IsTotallyIsotropic H ∧
      (discriminantBilinObject R L hL).IsLagrangian H}

/-- A quadratic-isotropic subgroup is isotropic for the discriminant pairing. -/
noncomputable def EvenDiscriminantIsotropicSubgroup.toBilinear
    [NeZero (2 : R)]
    {hL : IsFractionFieldPerfect R L} {hEven : IsEven L}
    (H : EvenDiscriminantIsotropicSubgroup hL hEven) :
    DiscriminantIsotropicSubgroup R hL := by
  refine ⟨H.1, ?_⟩
  intro x hx
  rw [(discriminantBilinObject R L hL).mem_orthogonalSubmodule_iff]
  intro y hy
  change discriminantBilinMap R L hL y x = 0
  have hpolar := H.property.polar_eq_zero hy hx
  change QuadraticMap.polar (evenDiscriminantQuadraticMap L hL hEven)
      y x = 0 at hpolar
  rw [evenDiscriminantQuadraticMap_polar] at hpolar
  apply (doubleValueEquiv R).injective
  rw [map_zero]
  simpa [doubleValueMap_eq_doubleValueEquiv] using hpolar

/-- A quadratic-isotropic subgroup constructs an integral overlattice. -/
noncomputable def evenOverlatticeFromIsotropicSubgroup
    [NeZero (2 : R)]
    (hL : IsFractionFieldPerfect R L) (hEven : IsEven L)
    (H : EvenDiscriminantIsotropicSubgroup hL hEven) : Overlattice R L :=
  overlatticeFromIsotropicSubgroup R hL H.toBilinear

end LeanCategories.Lattices.Valued
