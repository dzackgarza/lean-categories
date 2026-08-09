/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Lattices.Valued.Rationalization

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

/-- The image of an ideal of `R` inside its fraction field. -/
def idealInFractionRing (I : Ideal R) : Submodule R (FractionRing R) :=
  Submodule.map (Algebra.linearMap R (FractionRing R)) I

/-- The value module `Frac(R) / I`. -/
abbrev IdealValueQuotient (I : Ideal R) :=
  FractionRing R ⧸ idealInFractionRing R I

/-- The quotient map `Frac(R) → Frac(R) / I`. -/
def idealValueProjection (I : Ideal R) :
    FractionRing R →ₗ[R] IdealValueQuotient R I :=
  Submodule.mkQ (idealInFractionRing R I)

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

/-- The map whose kernel is the metric `I`-dual. -/
noncomputable def idealDualMap (L : IntegralLatticeCat R) (I : Ideal R) :
    RationalSpan R L →ₗ[R]
      (L.obj.carrier →ₗ[R] IdealValueQuotient R I) where
  toFun x := (idealValueProjection R I).comp (rationalPairingMap R L x)
  map_add' x y := by
    ext z
    simp
  map_smul' r x := by
    ext z
    simp

/-- The metric `I`-dual, defined as a kernel without generators. -/
noncomputable def idealDual (L : IntegralLatticeCat R) (I : Ideal R) :
    Submodule R (RationalSpan R L) :=
  LinearMap.ker (idealDualMap R L I)

noncomputable def idealDualInclusion (L : IntegralLatticeCat R) (I : Ideal R) :
    idealDual R L I →ₗ[R] RationalSpan R L :=
  (idealDual R L I).subtype

omit [IsDomain R] in
theorem exact_idealDual (L : IntegralLatticeCat R) (I : Ideal R) :
    Function.Exact (idealDualInclusion R L I) (idealDualMap R L I) :=
  LinearMap.exact_subtype_ker_map (idealDualMap R L I)

theorem toRationalSpan_mem_idealDual_iff (L : IntegralLatticeCat R)
    (I : Ideal R) (x : L.obj.carrier) :
    toRationalSpan R L x ∈ idealDual R L I ↔
      ∀ y, L.obj.pairing x y ∈ I := by
  constructor
  · intro hx y
    rw [idealDual, LinearMap.mem_ker] at hx
    have hy := LinearMap.congr_fun hx y
    change idealValueProjection R I
      (rationalizedForm R L (toRationalSpan R L x)
        (toRationalSpan R L y)) = 0 at hy
    change idealValueProjection R I
      (rationalizedForm R L (1 ⊗ₜ[R] x) (1 ⊗ₜ[R] y)) = 0 at hy
    rw [rationalizedForm_tmul] at hy
    simp only [one_mul] at hy
    rw [idealValueProjection, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero, idealInFractionRing] at hy
    rcases hy with ⟨a, ha, hEq⟩
    have : a = L.obj.pairing x y :=
      (FaithfulSMul.algebraMap_injective R (FractionRing R)) hEq
    simpa [this] using ha
  · intro h
    rw [idealDual, LinearMap.mem_ker]
    apply LinearMap.ext
    intro y
    change idealValueProjection R I
      (rationalizedForm R L (toRationalSpan R L x)
        (toRationalSpan R L y)) = 0
    change idealValueProjection R I
      (rationalizedForm R L (1 ⊗ₜ[R] x) (1 ⊗ₜ[R] y)) = 0
    rw [rationalizedForm_tmul]
    simp only [one_mul]
    rw [idealValueProjection, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero, idealInFractionRing]
    exact ⟨L.obj.pairing x y, h y, rfl⟩

/-- The canonical map to the rational span factors through the metric `I`-dual. -/
def CanonicalMapLiftsToIdealDual (L : IntegralLatticeCat R) (I : Ideal R) : Prop :=
  ∃ ι : L.obj.carrier →ₗ[R] idealDual R L I,
    idealDualInclusion R L I ∘ₗ ι = toRationalSpan R L

theorem isBilinearlyEven_iff_canonicalMapLiftsToIdealDual
    (L : IntegralLatticeCat R) (I : Ideal R) :
    IsBilinearlyEven L I ↔ CanonicalMapLiftsToIdealDual R L I := by
  rw [isBilinearlyEven_iff_pairing_mem]
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

