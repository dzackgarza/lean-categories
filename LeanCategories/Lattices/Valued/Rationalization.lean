/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Lattices.Valued.ScaleAndEvenness

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open Opposite
open LeanCategories.Modules.Bilinear.Valued

namespace LeanCategories.Lattices.Valued

universe u

variable (R : Type u) [CommRing R]
variable (W : Type u) [AddCommGroup W] [Module R W]

/-- Rational lattices obtained from `R`-lattices. -/
abbrev RationalLatticeCat [IsDomain R] :=
  LatticeCat (FractionRing R) (FractionRing R)

/-- Rationalization is scalar extension followed by the canonical value isomorphism. -/
noncomputable def rationalization [IsDomain R] :
    IntegralLatticeCat R ⥤ RationalLatticeCat R :=
  baseChange R R (FractionRing R) ⋙
    changeValue (FractionRing R) (TensorProduct R (FractionRing R) R)
      (TensorProduct.AlgebraTensorModule.rid R (FractionRing R)
        (FractionRing R)).toLinearMap

section RationalSpan

variable [IsDomain R]


abbrev RationalSpan (L : IntegralLatticeCat R) :=
  TensorProduct R (FractionRing R) L.obj.carrier

/-- The canonical map into the rational span. -/
def toRationalSpan (L : IntegralLatticeCat R) :
    L.obj.carrier →ₗ[R] RationalSpan R L :=
  TensorProduct.mk R (FractionRing R) L.obj.carrier 1

/-- The image of the lattice inside its rational span. -/
def integralImage (L : IntegralLatticeCat R) :
    Submodule R (RationalSpan R L) :=
  LinearMap.range (toRationalSpan R L)

/-- The rationalized bilinear form. -/
noncomputable abbrev rationalizedForm (L : IntegralLatticeCat R) :
    LinearMap.BilinForm (FractionRing R) (RationalSpan R L) :=
  LinearMap.compr₂ (LinearMap.BilinMap.baseChange (FractionRing R) L.obj.bilinMap)
    (TensorProduct.AlgebraTensorModule.rid R (FractionRing R)
      (FractionRing R)).toLinearMap

omit [IsDomain R] in
theorem rationalizedForm_tmul (L : IntegralLatticeCat R)
    (a b : FractionRing R) (x y : L.obj.carrier) :
    rationalizedForm R L (a ⊗ₜ[R] x) (b ⊗ₜ[R] y) =
      (a * b) * algebraMap R (FractionRing R) (L.obj.pairing x y) := by
  simp [rationalizedForm, BilinModuleCat.bilinMap, BilinModuleCat.adjoint,
    BilinModuleCat.pairing, Algebra.smul_def, mul_comm]

end RationalSpan

end LeanCategories.Lattices.Valued

