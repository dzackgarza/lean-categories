/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Lattices.Valued.Rationalization
public import LeanCategories.Algebra.FractionalIdeals

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open Opposite
open LeanCategories.Modules.Bilinear.Valued

namespace LeanCategories.Lattices.Valued

universe u

variable (R : Type u) [CommRing R]
variable (W : Type u) [AddCommGroup W] [Module R W]

variable [IsDomain R]

/-- A fractional ideal of `R` in its fraction field. -/
abbrev FractionalRIdeal :=
  FractionalIdeal (nonZeroDivisors R) (FractionRing R)

/-- The value module `Frac(R) / I` for a fractional ideal `I`. -/
abbrev FractionalIdealValueQuotient (I : FractionalRIdeal R) :=
  FractionRing R ⧸ (I : Submodule R (FractionRing R))

/-- The quotient map `Frac(R) → Frac(R) / I` for a fractional ideal `I`. -/
def fractionalIdealValueProjection (I : FractionalRIdeal R) :
    FractionRing R →ₗ[R] FractionalIdealValueQuotient R I :=
  Submodule.mkQ (I : Submodule R (FractionRing R))

/-- Pair a rational vector with the original lattice. -/
noncomputable def rationalPairingMap (L : IntegralLatticeCat R) :
    RationalSpan R L →ₗ[R] (L.obj.carrier →ₗ[R] FractionRing R) where
  toFun x := ((rationalizedForm R L x).restrictScalars R).comp
    (toRationalSpan R L)
  map_add' x y := by
    ext z
    simp
  map_smul' r x := by
    ext z
    simp [Algebra.smul_def]

/-- The map whose kernel is the metric fractional-`I`-dual. -/
noncomputable def fractionalIdealDualMap
    (L : IntegralLatticeCat R) (I : FractionalRIdeal R) :
    RationalSpan R L →ₗ[R]
      (L.obj.carrier →ₗ[R] FractionalIdealValueQuotient R I) where
  toFun x := (fractionalIdealValueProjection R I).comp (rationalPairingMap R L x)
  map_add' x y := by
    ext z
    simp
  map_smul' r x := by
    ext z
    simp

/-- The metric fractional-`I`-dual, defined as a kernel without generators. -/
noncomputable def fractionalIdealDual
    (L : IntegralLatticeCat R) (I : FractionalRIdeal R) :
    Submodule R (RationalSpan R L) :=
  LinearMap.ker (fractionalIdealDualMap R L I)

/-- A lattice is fractional-`I`-modular when it equals its metric `I`-dual. -/
noncomputable def IsFractionalIModular
    (L : IntegralLatticeCat R) (I : FractionalRIdeal R) : Prop :=
  fractionalIdealDual R L I = integralImage R L

/-- Fractional-`I`-modularity as a property of finite projective integral lattices. -/
noncomputable def isFractionalIModularFiniteProjectiveLattice
    (I : FractionalRIdeal R) :
    ObjectProperty (FiniteProjectiveLatticeCat R R) :=
  fun L ↦ IsFractionalIModular R L.obj I

/-- The full category of finite projective fractional-`I`-modular lattices. -/
noncomputable abbrev FractionalIModularLatticeCat (I : FractionalRIdeal R) :=
  (isFractionalIModularFiniteProjectiveLattice R I).FullSubcategory

noncomputable def fractionalIdealDualInclusion
    (L : IntegralLatticeCat R) (I : FractionalRIdeal R) :
    fractionalIdealDual R L I →ₗ[R] RationalSpan R L :=
  (fractionalIdealDual R L I).subtype

omit [IsDomain R] in
theorem exact_fractionalIdealDual
    (L : IntegralLatticeCat R) (I : FractionalRIdeal R) :
    Function.Exact (fractionalIdealDualInclusion R L I)
      (fractionalIdealDualMap R L I) :=
  LinearMap.exact_subtype_ker_map (fractionalIdealDualMap R L I)

omit [IsDomain R] in
theorem toRationalSpan_mem_fractionalIdealDual_iff
    (L : IntegralLatticeCat R) (I : FractionalRIdeal R)
    (x : L.obj.carrier) :
    toRationalSpan R L x ∈ fractionalIdealDual R L I ↔
      ∀ y, algebraMap R (FractionRing R) (L.obj.pairing x y) ∈ I := by
  constructor
  · intro hx y
    rw [fractionalIdealDual, LinearMap.mem_ker] at hx
    have hy := LinearMap.congr_fun hx y
    change fractionalIdealValueProjection R I
      (rationalizedForm R L (toRationalSpan R L x)
        (toRationalSpan R L y)) = 0 at hy
    change fractionalIdealValueProjection R I
      (rationalizedForm R L (1 ⊗ₜ[R] x) (1 ⊗ₜ[R] y)) = 0 at hy
    rw [rationalizedForm_tmul] at hy
    simp only [one_mul] at hy
    simpa [fractionalIdealValueProjection] using hy
  · intro h
    rw [fractionalIdealDual, LinearMap.mem_ker]
    apply LinearMap.ext
    intro y
    change fractionalIdealValueProjection R I
      (rationalizedForm R L (toRationalSpan R L x)
        (toRationalSpan R L y)) = 0
    change fractionalIdealValueProjection R I
      (rationalizedForm R L (1 ⊗ₜ[R] x) (1 ⊗ₜ[R] y)) = 0
    rw [rationalizedForm_tmul]
    simp only [one_mul]
    simpa [fractionalIdealValueProjection] using h y

/-- The integral ideal `I` as a fractional ideal in `Frac(R)`. -/
abbrev integralFractionalIdeal (I : Ideal R) : FractionalRIdeal R := I

/-- The metric dual for an integral ideal is the fractional ideal dual of its image. -/
noncomputable abbrev idealDual (L : IntegralLatticeCat R) (I : Ideal R) :=
  fractionalIdealDual R L (integralFractionalIdeal R I)

/-- Integral `I`-modularity is fractional modularity for the image of `I`. -/
noncomputable abbrev IsIModular (L : IntegralLatticeCat R) (I : Ideal R) : Prop :=
  IsFractionalIModular R L (integralFractionalIdeal R I)

/-- Integral `I`-modularity as a property of finite projective lattices. -/
noncomputable abbrev isIModularFiniteProjectiveLattice (I : Ideal R) :=
  isFractionalIModularFiniteProjectiveLattice R (integralFractionalIdeal R I)

/-- The integral-ideal specialization of the fractional modular lattice category. -/
noncomputable abbrev IModularLatticeCat (I : Ideal R) :=
  FractionalIModularLatticeCat R (integralFractionalIdeal R I)

noncomputable abbrev idealDualMap (L : IntegralLatticeCat R) (I : Ideal R) :=
  fractionalIdealDualMap R L (integralFractionalIdeal R I)

/-- The pairing map from the metric `I`-dual to the `I`-valued module dual. -/
noncomputable def idealDualPairingMap (L : IntegralLatticeCat R) (I : Ideal R) :
    idealDual R L I →ₗ[R] (L.obj.carrier →ₗ[R] I) where
  toFun x := by
    let e := Submodule.equivMapOfInjective
      (Algebra.linearMap R (FractionRing R))
      (FaithfulSMul.algebraMap_injective R (FractionRing R)) I
    let f := rationalPairingMap R L (x : RationalSpan R L)
    have hx (y : L.obj.carrier) : f y ∈ (integralFractionalIdeal R I : FractionalRIdeal R) := by
      have hx' : (x : RationalSpan R L) ∈
          fractionalIdealDual R L (integralFractionalIdeal R I) := x.property
      rw [fractionalIdealDual, LinearMap.mem_ker] at hx'
      have hxy := LinearMap.congr_fun hx' y
      change fractionalIdealValueProjection R I (f y) = 0 at hxy
      rw [fractionalIdealValueProjection, Submodule.mkQ_apply,
        Submodule.Quotient.mk_eq_zero] at hxy
      exact hxy
    exact
      { toFun := fun y => e.symm ⟨f y, hx y⟩
        map_add' := by
          intro y z
          apply e.injective
          apply Subtype.ext
          simp [e, f]
        map_smul' := by
          intro r y
          apply e.injective
          apply Subtype.ext
          simp [e, f] }
  map_add' x y := by
    apply LinearMap.ext
    intro z
    let e := Submodule.equivMapOfInjective
      (Algebra.linearMap R (FractionRing R))
      (FaithfulSMul.algebraMap_injective R (FractionRing R)) I
    apply e.injective
    simp [e, rationalPairingMap]
  map_smul' r x := by
    apply LinearMap.ext
    intro y
    let e := Submodule.equivMapOfInjective
      (Algebra.linearMap R (FractionRing R))
      (FaithfulSMul.algebraMap_injective R (FractionRing R)) I
    apply e.injective
    simp [e, rationalPairingMap]

noncomputable abbrev idealDualInclusion (L : IntegralLatticeCat R) (I : Ideal R) :=
  fractionalIdealDualInclusion R L (integralFractionalIdeal R I)

omit [IsDomain R] in
theorem exact_idealDual (L : IntegralLatticeCat R) (I : Ideal R) :
    Function.Exact (idealDualInclusion R L I) (idealDualMap R L I) :=
  exact_fractionalIdealDual R L (integralFractionalIdeal R I)

theorem toRationalSpan_mem_idealDual_iff (L : IntegralLatticeCat R)
    (I : Ideal R) (x : L.obj.carrier) :
    toRationalSpan R L x ∈ idealDual R L I ↔
      ∀ y, L.obj.pairing x y ∈ I := by
  rw [toRationalSpan_mem_fractionalIdealDual_iff]
  constructor
  · intro h y
    rcases (FractionalIdeal.mem_coeIdeal (nonZeroDivisors R)).mp (h y) with
      ⟨z, hz, hzy⟩
    exact (FaithfulSMul.algebraMap_injective R (FractionRing R)) hzy ▸ hz
  · intro h y
    exact FractionalIdeal.mem_coeIdeal_of_mem (nonZeroDivisors R) (h y)

/-- The canonical map to the rational span factors through the metric `I`-dual. -/
def CanonicalMapLiftsToIdealDual (L : IntegralLatticeCat R) (I : Ideal R) : Prop :=
  ∃ ι : L.obj.carrier →ₗ[R] idealDual R L I,
    idealDualInclusion R L I ∘ₗ ι = toRationalSpan R L

theorem isIIntegral_iff_canonicalMapLiftsToIdealDual
    (L : IntegralLatticeCat R) (I : Ideal R) :
    IsIIntegral L I ↔ CanonicalMapLiftsToIdealDual R L I := by
  rw [isIIntegral_iff_pairing_mem]
  constructor
  · intro h
    refine ⟨LinearMap.codRestrict (idealDual R L I) (toRationalSpan R L) ?_, ?_⟩
    · intro x
      exact (toRationalSpan_mem_idealDual_iff R L I x).mpr (h x)
    · ext x
      rfl
  · rintro ⟨ι, hι⟩ x y
    apply (toRationalSpan_mem_idealDual_iff R L I x).mp
    have hx : idealDualInclusion R L I (ι x) = toRationalSpan R L x :=
      LinearMap.congr_fun hι x
    rw [← hx]
    exact (ι x).property

end LeanCategories.Lattices.Valued
