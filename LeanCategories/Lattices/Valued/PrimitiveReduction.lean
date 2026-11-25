/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Modules.Bilinear.Valued.Witt
public import LeanCategories.Lattices.Valued.Rationalization
public import LeanCategories.Lattices.Valued.Sublattice
public import LeanCategories.Lattices.Valued.MetricDual
public import LeanCategories.Lattices.Valued.Discriminant
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import Mathlib.RingTheory.Localization.Basic

/-!
# Primitive isotropic reduction: no assumed radical equality

The radical hypothesis of `IsotropicReductionData` is *derived* here from a primitive totally
isotropic submodule `P` of a nondegenerate integral lattice. The argument goes through the
rational span `K ⊗_R L`, where `K = Frac(R)`:

* any element of the `K`-span of the image of `P` clears a denominator, landing back in `P`;
* the base-changed form is nondegenerate (from `L.obj.IsNondegenerate`), and it is reflexive
  since the form is symmetric;
* over a field `B.orthogonal (B.orthogonal W) = W`, so if `x` is orthogonal to everything orthogonal
  to `P`, its rationalization lies in the span of `P`;
* primitivity (`saturation P = P`) brings this back to `x ∈ P`.

No structural assumption on `P` beyond `IsPrimitiveSubmodule` is used. The projective/even
lattice wrapper, the intrinsic discriminant subgroup and the discriminant quotient isometry are
developed elsewhere; this file proves the radical statement used by the isotropic reduction.
-/

@[expose] public section

open LeanCategories.Modules.Bilinear.Valued

namespace LeanCategories.Lattices.Valued

universe u

variable {R : Type u} [CommRing R] [IsDomain R]

section DenominatorClearing

/-- Every fraction clears a denominator in `R`. -/
lemma fraction_denominator (x : FractionRing R) :
    ∃ d n : R, d ≠ 0 ∧ (algebraMap R (FractionRing R) d) * x =
      algebraMap R (FractionRing R) n := by
  classical
  obtain ⟨⟨n, d, hd⟩, h⟩ := IsLocalization.surj (nonZeroDivisors R) x
  have hd0 : d ≠ 0 := nonZeroDivisors.coe_ne_zero ⟨d, hd⟩
  exact ⟨d, n, hd0, by rw [mul_comm]; exact h⟩

/-- An element of the `Frac(R)`-span of the image of a submodule in the rational span clears a
denominator to an element of that submodule. -/
lemma exists_clear_denominator_of_mem_span
    (L : IntegralLatticeCat R) (P : Submodule R L.obj.carrier)
    {z : TensorProduct R (FractionRing R) L.obj.carrier}
    (hz : z ∈ Submodule.span (FractionRing R) ((toRationalSpan R L) '' P)) :
    ∃ a : R, a ≠ 0 ∧ ∃ p : L.obj.carrier, p ∈ P ∧
      a • z = toRationalSpan R L p := by
  induction hz using Submodule.span_induction with
  | mem y hy =>
      obtain ⟨p, hp, rfl⟩ := hy
      refine ⟨1, one_ne_zero, p, hp, ?_⟩
      simp
  | zero =>
      refine ⟨1, one_ne_zero, 0, P.zero_mem, ?_⟩
      simp
  | add x y hx hy hxs hys =>
      obtain ⟨a, ha, pa, hpa, ha'⟩ := hxs
      obtain ⟨b, hb, pb, hpb, hb'⟩ := hys
      refine ⟨a * b, mul_ne_zero ha hb, a • pb + b • pa, ?_, ?_⟩
      · exact P.add_mem (P.smul_mem a hpb) (P.smul_mem b hpa)
      · have hs1 : (a * b) • x = b • (a • x) := by rw [mul_comm, mul_smul]
        have hs2 : (a * b) • y = a • (b • y) := by rw [mul_smul]
        rw [smul_add, hs1, hs2, ha', hb', map_add, map_smul, map_smul, add_comm]
  | smul s x hx hxs =>
      obtain ⟨d, n, hd, hd'⟩ := fraction_denominator (R := R) s
      obtain ⟨a, ha, pa, hpa, ha'⟩ := hxs
      refine ⟨a * d, mul_ne_zero ha hd, n • pa, P.smul_mem n hpa, ?_⟩
      have hd'' : (d • s) = algebraMap R (FractionRing R) n := by
        rw [Algebra.smul_def]
        exact hd'
      have hstep : (a * d) • (s • x) = n • (a • x) := by
        calc (a * d) • (s • x) = a • d • (s • x) := by rw [mul_smul]
          _ = a • ((d • s) • x) := by rw [IsScalarTower.smul_assoc]
          _ = a • (n • x) := by rw [hd'', IsScalarTower.algebraMap_smul]
          _ = n • (a • x) := by rw [smul_comm]

      rw [hstep, ha', map_smul]

/-- A pure tensor in the rational span clears a denominator. -/
lemma exists_clear_denominator_tmul (L : IntegralLatticeCat R)
    (c : FractionRing R) (x : L.obj.carrier) :
    ∃ a : R, a ≠ 0 ∧ ∃ p : L.obj.carrier,
      a • (c ⊗ₜ[R] x) = toRationalSpan R L p := by
  obtain ⟨d, n, hd, hd'⟩ := fraction_denominator (R := R) c
  refine ⟨d, hd, n • x, ?_⟩
  calc
    d • (c ⊗ₜ[R] x) = ((algebraMap R (FractionRing R) d) * c) ⊗ₜ[R] x := by
      show (d • c) ⊗ₜ[R] x = ((algebraMap R (FractionRing R) d) * c) ⊗ₜ[R] x
      rw [Algebra.smul_def]
    _ = (algebraMap R (FractionRing R) n) ⊗ₜ[R] x := by rw [hd']
    _ = toRationalSpan R L (n • x) := by
      rw [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
      rfl

/-- Any element of the rational span clears a denominator to an element of the lattice. -/
lemma exists_clear_denominator (L : IntegralLatticeCat R)
    (z : TensorProduct R (FractionRing R) L.obj.carrier) :
    ∃ a : R, a ≠ 0 ∧ ∃ p : L.obj.carrier,
      a • z = toRationalSpan R L p := by
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨1, one_ne_zero, 0, by simp⟩
  | tmul c x => exact exists_clear_denominator_tmul L c x
  | add x y hx hy =>
      obtain ⟨a, ha, pa, ha'⟩ := hx
      obtain ⟨b, hb, pb, hb'⟩ := hy
      refine ⟨a * b, mul_ne_zero ha hb, a • pb + b • pa, ?_⟩
      have hs1 : (a * b) • x = b • (a • x) := by rw [mul_comm, mul_smul]
      have hs2 : (a * b) • y = a • (b • y) := by rw [mul_smul]
      rw [smul_add, hs1, hs2, ha', hb', map_add, map_smul, map_smul, add_comm]

end DenominatorClearing


section RationalForm

variable (L : IntegralLatticeCat R)

theorem rational_pairing_eq (L : IntegralLatticeCat R)
    (x y : L.obj.carrier) :
    rationalizedForm R L (toRationalSpan R L x) (toRationalSpan R L y) =
      algebraMap R (FractionRing R) (L.obj.pairing x y) := by
  simp only [toRationalSpan, TensorProduct.mk_apply, rationalizedForm_tmul, one_mul]

private theorem rationalizedForm_nondegenerate (hN : L.obj.IsNondegenerate) :
    (rationalizedForm R L).Nondegenerate := by
  have hrefl : (rationalizedForm R L).IsRefl := by
    intro x y
    exact fun h => by
      rw [rationalizedForm_isSymmetric R L x y] at h
      exact h
  have hleft : LinearMap.SeparatingLeft (rationalizedForm R L) := by
    intro z hz
    obtain ⟨a, ha, p, ha'⟩ := exists_clear_denominator L z
    have hp0 : p = 0 := by
      apply hN.1
      intro y
      rw [BilinModuleCat.bilinMap_apply]
      apply (FaithfulSMul.algebraMap_injective R (FractionRing R))
      rw [map_zero]
      rw [← rational_pairing_eq L p y, ← ha', LinearMap.BilinForm.smul_left_of_tower,
        hz (toRationalSpan R L y), smul_zero]
    have hz0 : a • z = 0 := by rw [ha', hp0, map_zero]
    rw [← IsScalarTower.algebraMap_smul (A := FractionRing R)] at hz0
    exact (smul_eq_zero.mp hz0).resolve_left (by
      intro h
      exact ha (FaithfulSMul.algebraMap_injective R (FractionRing R) (by simpa using h)))
  refine ⟨hleft, ?_⟩
  intro z hz
  refine hleft z (fun w => ?_)
  rw [rationalizedForm_isSymmetric R L]
  exact hz w

/-- The orthogonal of the `K`-span of a rationalized submodule is contained in the `K`-span of its
integral orthogonal. -/
theorem mem_span_orthogonal_of_mem_orthogonal
    (L : IntegralLatticeCat R) (P : Submodule R L.obj.carrier)
    {z : TensorProduct R (FractionRing R) L.obj.carrier}
    (hz : z ∈ (rationalizedForm R L).orthogonal
      (Submodule.span (FractionRing R) ((toRationalSpan R L) '' P))) :
    z ∈ Submodule.span (FractionRing R)
      ((toRationalSpan R L) '' L.obj.orthogonalSubmodule P) := by
  obtain ⟨a, ha, q, hq⟩ := exists_clear_denominator L z
  have hna : (algebraMap R (FractionRing R) a) ≠ 0 :=
    fun h => ha (FaithfulSMul.algebraMap_injective R (FractionRing R) (by simpa using h))
  have hqperp : q ∈ L.obj.orthogonalSubmodule P := by
    rw [L.obj.mem_orthogonalSubmodule_iff]
    intro p hp
    have hzq : rationalizedForm R L (toRationalSpan R L p) (toRationalSpan R L q) = 0 := by
      calc
        rationalizedForm R L (toRationalSpan R L p) (toRationalSpan R L q) =
            a • rationalizedForm R L (toRationalSpan R L p) z := by
              rw [← LinearMap.BilinForm.smul_right_of_tower, hq]
        _ = 0 := by
              have hpz := ((LinearMap.BilinForm.mem_orthogonal_iff).mp hz
                (toRationalSpan R L p) (Submodule.subset_span ⟨p, hp, rfl⟩))
              rw [hpz, smul_zero]
    have hpair := hzq
    rw [rational_pairing_eq L p q] at hpair
    exact (FaithfulSMul.algebraMap_injective R (FractionRing R)) (by simpa using hpair)
  have hqspan : toRationalSpan R L q ∈ Submodule.span (FractionRing R)
      ((toRationalSpan R L) '' L.obj.orthogonalSubmodule P) :=
    Submodule.subset_span ⟨q, hqperp, rfl⟩
  have hzq : z = ((algebraMap R (FractionRing R) a)⁻¹) • toRationalSpan R L q := by
    have haux : ((algebraMap R (FractionRing R) a)⁻¹) • ((algebraMap R (FractionRing R) a) • z) = z := by
      rw [smul_smul, inv_mul_cancel₀ hna, one_smul]
    have hzq' : (algebraMap R (FractionRing R) a) • z = toRationalSpan R L q := by
      rw [IsScalarTower.algebraMap_smul (A := FractionRing R)]
      exact hq
    rw [hzq'] at haux
    exact haux.symm
  rw [hzq]
  exact Submodule.smul_mem _ _ hqspan

/-- The radical equality for a primitive totally isotropic submodule. -/
theorem mem_primitive_of_isotropic_orthogonal_orthogonal
    (L : IntegralLatticeCat R) [Module.Finite R L.obj.carrier] (hN : L.obj.IsNondegenerate)
    {P : Submodule R L.obj.carrier} (hP : IsPrimitiveSubmodule P)
    {x : L.obj.carrier} (hx1 : x ∈ L.obj.orthogonalSubmodule P)
    (hx2 : ∀ y, y ∈ L.obj.orthogonalSubmodule P → L.obj.pairing y x = 0) : x ∈ P := by
  letI : FiniteDimensional (FractionRing R) (RationalSpan R L) := inferInstance
  have hrefl : (rationalizedForm R L).IsRefl := by
    intro y z
    exact fun h => by
      rw [rationalizedForm_isSymmetric R L y z] at h
      exact h
  set S : Submodule (FractionRing R) (TensorProduct R (FractionRing R) L.obj.carrier) :=
    Submodule.span (FractionRing R) ((toRationalSpan R L) '' P)
  have hspanx : toRationalSpan R L x ∈ (rationalizedForm R L).orthogonal
      ((rationalizedForm R L).orthogonal S) := by
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro z hz
    have hz' : z ∈ Submodule.span (FractionRing R)
        ((toRationalSpan R L) '' L.obj.orthogonalSubmodule P) := by
      exact mem_span_orthogonal_of_mem_orthogonal L P hz
    refine Submodule.span_induction
      (p := fun z _ => (rationalizedForm R L z) (toRationalSpan R L x) = 0)
      ?_ ?_ ?_ ?_ hz'
    · rintro y ⟨q, hq, rfl⟩
      rw [rational_pairing_eq L q x, hx2 q hq, map_zero]
    · exact LinearMap.BilinForm.zero_left _
    · intro y z _ _ hy' hz'
      rw [LinearMap.BilinForm.add_left, hy', hz', add_zero]
    · intro a y _ hy'
      rw [LinearMap.BilinForm.smul_left_of_tower, hy', smul_zero]
  rw [LinearMap.BilinForm.orthogonal_orthogonal
    (rationalizedForm_nondegenerate L hN) hrefl] at hspanx
  obtain ⟨a, ha, q, hq, hax⟩ := exists_clear_denominator_of_mem_span L P hspanx
  have hax' : toRationalSpan R L (a • x) = toRationalSpan R L q := by
    rw [map_smul, hax]
  have haxp : a • x = q := toRationalSpan_injective R L hax'
  have hmem : x ∈ saturation P := by
    rw [mem_saturation_iff]
    exact ⟨a, ha, haxp ▸ hq⟩
  exact (isPrimitiveSubmodule_iff_saturation_eq P |>.mp hP) ▸ hmem

/-- A lattice vector whose rationalization lies in the span of a primitive submodule already
belongs to that submodule. -/
theorem mem_of_toRationalSpan_mem_rationalSpan (L : IntegralLatticeCat R)
    (P : Submodule R L.obj.carrier) (hP : IsPrimitiveSubmodule P) {x : L.obj.carrier}
    (hx : toRationalSpan R L x ∈
      Submodule.span (FractionRing R) ((toRationalSpan R L) '' P)) : x ∈ P := by
  obtain ⟨a, ha, q, hq, hax⟩ := exists_clear_denominator_of_mem_span L P hx
  have hax' : toRationalSpan R L (a • x) = toRationalSpan R L q := by
    rw [map_smul, hax]
  have haxp : a • x = q := toRationalSpan_injective R L hax'
  have hmem : x ∈ saturation P := by
    rw [mem_saturation_iff]
    exact ⟨a, ha, haxp ▸ hq⟩
  exact (isPrimitiveSubmodule_iff_saturation_eq P |>.mp hP) ▸ hmem

end RationalForm

end LeanCategories.Lattices.Valued
