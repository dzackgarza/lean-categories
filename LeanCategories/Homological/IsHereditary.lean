/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Module.Projective
public import Mathlib.Algebra.Field.Opposite
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.RingTheory.DedekindDomain.Ideal.Basic
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.SimpleModule.InjectiveProjective
public import Mathlib.RingTheory.SimpleModule.WedderburnArtin

/-!
# Hereditary rings

Weibel, *An Introduction to Homological Algebra*, Definition 4.2.10 (p. 95):

> A ring `R` is called *(right) hereditary* if every right ideal is projective.

Following Mathlib's convention for noncommutative rings, a right ideal of `R` is
a left ideal of the opposite ring `Rᵐᵒᵖ`, i.e. an element of `Ideal Rᵐᵒᵖ`.
Projectivity of such an ideal is therefore projectivity as a right `R`-module,
`Module.Projective Rᵐᵒᵖ I`.
-/

@[expose] public section

namespace LeanCategories.Homological

/-- A ring `R` is *right hereditary* if every right ideal of `R` is a projective
right `R`-module (Weibel, Definition 4.2.10). -/
def IsRightHereditary (R : Type*) [Ring R] : Prop :=
  ∀ I : Ideal Rᵐᵒᵖ, Module.Projective Rᵐᵒᵖ I

namespace IsRightHereditary

open scoped nonZeroDivisors

private theorem ideal_mul_inv_cancel_of_projective
    {R : Type*} [CommRing R] [IsDomain R] (I : Ideal R) (hI : I ≠ ⊥)
    (hproj : Module.Projective R I) :
    (I : FractionalIdeal R⁰ (FractionRing R)) *
        (I : FractionalIdeal R⁰ (FractionRing R))⁻¹ = 1 := by
  apply le_antisymm FractionalIdeal.mul_one_div_le_one
  rw [FractionalIdeal.one_le]
  obtain ⟨aI, haI0⟩ := Submodule.nonzero_mem_of_bot_lt (bot_lt_iff_ne_bot.mpr hI)
  have ha0 : (aI : R) ≠ 0 := fun h => haI0 (Subtype.ext h)
  obtain ⟨s, hs⟩ := hproj.out
  let phi (i : I) : I →ₗ[R] R :=
    { toFun := fun b => s b i
      map_add' := fun b c => by simp
      map_smul' := fun r b => by simp }
  have hcoord (i b : I) : (aI : R) * phi i b = (b : R) * phi i aI := by
    have hscale : (aI : R) • s b = (b : R) • s aI := by
      rw [← s.map_smul, ← s.map_smul]
      congr 1
      apply Subtype.ext
      simp [smul_eq_mul, mul_comm]
    exact DFunLike.congr_fun hscale i
  let K := FractionRing R
  have hmapa : algebraMap R K (aI : R) ≠ 0 :=
    by simpa using (IsFractionRing.injective R K).ne ha0
  have hq (i : I) :
      algebraMap R K (phi i aI) * (algebraMap R K (aI : R))⁻¹ ∈
        (I : FractionalIdeal R⁰ K)⁻¹ := by
    rw [FractionalIdeal.mem_inv_iff (FractionalIdeal.coeIdeal_ne_zero.mpr hI)]
    intro y hy
    obtain ⟨b, hb, rfl⟩ := (FractionalIdeal.mem_coeIdeal R⁰).mp hy
    have hrel := congrArg (algebraMap R K) (hcoord i ⟨b, hb⟩)
    have heq :
      algebraMap R K (phi i aI) * (algebraMap R K (aI : R))⁻¹ * algebraMap R K b =
          algebraMap R K (phi i ⟨b, hb⟩) := by
      calc
        algebraMap R K (phi i aI) * (algebraMap R K (aI : R))⁻¹ * algebraMap R K b =
            (algebraMap R K (aI : R))⁻¹ *
              (algebraMap R K b * algebraMap R K (phi i aI)) := by ac_rfl
        _ = (algebraMap R K (aI : R))⁻¹ *
              (algebraMap R K (aI : R) * algebraMap R K (phi i ⟨b, hb⟩)) := by
            simpa only [map_mul] using congrArg
              (fun z : K => (algebraMap R K (aI : R))⁻¹ * z) hrel.symm
        _ = algebraMap R K (phi i ⟨b, hb⟩) := by
            rw [← mul_assoc, inv_mul_cancel₀ hmapa, one_mul]
    rw [heq]
    exact FractionalIdeal.coe_mem_one R⁰ _
  let t := s aI
  have hsum_mem :
      ∑ i ∈ t.support,
          algebraMap R K (i : R) *
            (algebraMap R K (t i) * (algebraMap R K (aI : R))⁻¹) ∈
        (I : FractionalIdeal R⁰ K) * (I : FractionalIdeal R⁰ K)⁻¹ := by
    apply Submodule.sum_mem
    intro i hi
    exact FractionalIdeal.mul_mem_mul
      (FractionalIdeal.mem_coeIdeal_of_mem R⁰ i.2) (by simpa [t, phi] using hq i)
  have hlin : ∑ i ∈ t.support, (i : R) * t i = (aI : R) := by
    have h := congrArg I.subtype (hs aI)
    simpa [t, Finsupp.sum, Finsupp.linearCombination_apply, map_finsuppSum, smul_eq_mul,
      mul_comm] using h
  have hsum_eq :
      ∑ i ∈ t.support,
          algebraMap R K (i : R) *
            (algebraMap R K (t i) * (algebraMap R K (aI : R))⁻¹) = 1 := by
    calc
      ∑ i ∈ t.support,
          algebraMap R K (i : R) *
            (algebraMap R K (t i) * (algebraMap R K (aI : R))⁻¹) =
          (∑ i ∈ t.support, algebraMap R K ((i : R) * t i)) *
            (algebraMap R K (aI : R))⁻¹ := by
              simp_rw [← mul_assoc, ← map_mul]
              rw [Finset.sum_mul]
      _ = algebraMap R K (∑ i ∈ t.support, (i : R) * t i) *
            (algebraMap R K (aI : R))⁻¹ := by
              rw [map_sum]
      _ = 1 := by rw [hlin, mul_inv_cancel₀ hmapa]
  rw [← hsum_eq]
  exact hsum_mem

/-- Every module over a division ring has a basis, hence is projective, so every
division ring is right hereditary (Weibel p. 95: "any principal ideal domain ...
is hereditary, as is any commutative Dedekind domain", and a fortiori any
division ring). -/
theorem of_divisionRing (R : Type*) [DivisionRing R] : IsRightHereditary R := by
  intro I
  exact Module.Projective.of_basis (Module.Basis.ofVectorSpace Rᵐᵒᵖ I)

/-- Every semisimple ring is right hereditary: the opposite ring is semisimple, hence every
right ideal is projective as a module over the opposite ring. -/
theorem of_isSemisimpleRing (R : Type*) [Ring R] [IsSemisimpleRing R] :
    IsRightHereditary R := by
  intro I
  haveI : IsSemisimpleRing Rᵐᵒᵖ := (isSemisimpleRing_mulOpposite_iff (R := R)).2 inferInstance
  exact Module.projective_of_isSemisimpleRing Rᵐᵒᵖ I

/-- Every commutative principal ideal domain is right hereditary. -/
theorem of_principalIdealDomain (R : Type*) [CommRing R] [IsDomain R]
    [IsPrincipalIdealRing R] : IsRightHereditary R := by
  let e : R ≃+* Rᵐᵒᵖ := RingEquiv.toOpposite R
  letI : IsPrincipalIdealRing Rᵐᵒᵖ :=
    IsPrincipalIdealRing.of_surjective e.toRingHom e.surjective
  intro I
  by_cases hI : I = ⊥
  · subst I
    use 0
    intro x
    exact Subsingleton.elim _ _
  · let g : Rᵐᵒᵖ := Submodule.IsPrincipal.generator I
    have hg : g ≠ 0 := by
      intro hg0
      apply hI
      exact (Submodule.IsPrincipal.eq_bot_iff_generator_eq_zero I).2 hg0
    let f : Rᵐᵒᵖ →ₗ[Rᵐᵒᵖ] I :=
      { toFun := fun r => ⟨r • g, Submodule.smul_mem I r (Submodule.IsPrincipal.generator_mem I)⟩
        map_add' := fun a b => by
          apply Subtype.ext
          simp [smul_eq_mul, add_mul]
        map_smul' := fun r a => by
          apply Subtype.ext
          simp [smul_eq_mul, mul_assoc] }
    have hf_injective : Function.Injective f := by
      intro a b hab
      have hab' : a * g = b * g := by
        simpa [f, smul_eq_mul] using congrArg Subtype.val hab
      exact mul_right_cancel₀ hg hab'
    have hf_surjective : Function.Surjective f := by
      intro x
      obtain ⟨r, hr⟩ :=
        (Submodule.IsPrincipal.mem_iff_eq_smul_generator I).mp x.2
      refine ⟨r, Subtype.ext ?_⟩
      simpa [f] using hr.symm
    let fEquiv : Rᵐᵒᵖ ≃ₗ[Rᵐᵒᵖ] I :=
      LinearEquiv.ofBijective f ⟨hf_injective, hf_surjective⟩
    haveI : Module.Projective Rᵐᵒᵖ Rᵐᵒᵖ := inferInstance
    exact Module.Projective.of_equiv' fEquiv

end IsRightHereditary

end LeanCategories.Homological
