/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Lattices.Valued.CliffordCenter
public import LeanCategories.Lattices.Valued.LipschitzAction
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Descent of the spinor norm to the orthogonal group

The Lipschitz group carries a spinor norm and covers the orthogonal group of a nondegenerate
form. This file shows the covering map kills the spinor norm on its kernel, so the spinor norm
descends, and packages the descent as a term of `SpinorNorm L`.

The kernel of the covering map consists of the twisted-central units. Those are the scalars,
by `exists_algebraMap_of_isTwistedCentral`, which needs two inputs: every functional is a polar
form (nondegeneracy plus finite dimension) and the contraction criterion
`ContractionsDetectScalars`. The second stays a hypothesis of every theorem here.

Reference: Cassels, *Rational Quadratic Forms*, Chapter 10, §3.
-/

@[expose] public section

open CliffordAlgebra
open LeanCategories.Modules.Bilinear.Valued

namespace LeanCategories.Lattices.Valued

universe u

variable {K : Type u} [Field K] [Invertible (2 : K)]

/-- Every functional on a nondegenerate finite form is a polar form.

The adjoint of a nondegenerate form is injective, hence surjective onto the dual, which has the
same dimension. The polar form is twice the pairing, so halving the functional first. -/
theorem exists_polarBilin_eq (L : FiniteFormCat K K) (hL : L.obj.IsLeftNondegenerate)
    (d : Module.Dual K L.obj.carrier) :
    ∃ v : L.obj.carrier, (finiteFormQuadratic L).polarBilin v = d := by
  haveI : Module.Finite K L.obj.carrier := L.property.1
  have hinj : Function.Injective L.obj.bilinMap :=
    (BilinModuleCat.isLeftNondegenerate_iff_adjoint_injective L.obj).mp hL
  have hsurj : Function.Surjective L.obj.bilinMap :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (V₂ := Module.Dual K L.obj.carrier) Subspace.dual_finrank_eq.symm).mp hinj
  obtain ⟨v, hv⟩ := hsurj (⅟(2 : K) • d)
  refine ⟨v, LinearMap.ext fun y => ?_⟩
  have hy : L.obj.pairing v y = ⅟(2 : K) * d y := congrArg (fun f => f y) hv
  rw [QuadraticMap.polarBilin_apply_apply, polar_finiteFormQuadratic, hy, ← mul_assoc,
    mul_invOf_self, one_mul]

/-- The Lipschitz norm of a scalar unit is its square. -/
theorem lipschitzNorm_eq_of_algebraMap (L : FiniteFormCat K K) (r : Kˣ)
    (g : lipschitzGroup (finiteFormQuadratic L))
    (hg : (g : (FiniteFormClifford L)ˣ) = algebraMapUnits L r) :
    lipschitzNorm L g = r * r := by
  have key : cliffordNormUnit L (g : (FiniteFormClifford L)ˣ) = algebraMapUnits L (r * r) := by
    apply Units.ext
    rw [cliffordNormUnit_val, cliffordNorm, hg, algebraMapUnits_val, reverse.commutes,
      algebraMapUnits_val, Units.val_mul, map_mul]
  rw [lipschitzNorm, MonoidHom.coe_mk, OneHom.coe_mk, MulEquiv.symm_apply_eq]
  exact Subtype.ext key

/-- The spinor norm of a scalar unit is trivial. -/
theorem lipschitzSpinorNorm_eq_one_of_algebraMap (L : FiniteFormCat K K) (r : Kˣ)
    (g : lipschitzGroup (finiteFormQuadratic L))
    (hg : (g : (FiniteFormClifford L)ˣ) = algebraMapUnits L r) :
    lipschitzSpinorNorm L g = 1 := by
  rw [lipschitzSpinorNorm, MonoidHom.comp_apply, lipschitzNorm_eq_of_algebraMap L r g hg,
    QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  exact Subgroup.mem_square.mpr ⟨r, rfl⟩

/-- A Lipschitz element acting trivially is twisted-central. -/
theorem isTwistedCentral_of_mem_ker (L : FiniteFormCat K K)
    {g : lipschitzGroup (finiteFormQuadratic L)} (hg : g ∈ (lipschitzActionHom L).ker) :
    IsTwistedCentral (finiteFormQuadratic L) (g : (FiniteFormClifford L)ˣ) := by
  intro x
  have hx : lipschitzAction L g x = x := by
    have h1 : lipschitzAction L g = 1 := congrArg Subtype.val hg
    exact congrArg (fun e : L.obj.carrier ≃ₗ[K] L.obj.carrier => e x) h1
  rw [← ι_lipschitzAction, hx]

/-- The covering map kills the spinor norm on its kernel.

The kernel is the group of twisted-central units, which the contraction criterion identifies
with the scalars, and the spinor norm of a scalar is trivial. -/
theorem ker_lipschitzActionHom_le_ker_lipschitzSpinorNorm (L : FiniteFormCat K K)
    (hL : L.obj.IsLeftNondegenerate)
    (hC : ContractionsDetectScalars (finiteFormQuadratic L)) :
    (lipschitzActionHom L).ker ≤ (lipschitzSpinorNorm L).ker := by
  intro g hg
  obtain ⟨r, hr⟩ := (isTwistedCentral_iff_mem_scalarRange (finiteFormQuadratic L) hC
    (exists_polarBilin_eq L hL)).mp (isTwistedCentral_of_mem_ker L hg)
  exact lipschitzSpinorNorm_eq_one_of_algebraMap L r g hr.symm

/-- The spinor norm of a nondegenerate finite symmetric form.

The Lipschitz group covers the orthogonal group and its spinor norm is trivial on the kernel of
the covering map, so the spinor norm factors through the orthogonal group. The value on a
reflection is the square class of `b(v,v)`, because the reflection is the action of the
corresponding vector generator. -/
noncomputable def spinorNormOfNondegenerate (L : FiniteFormCat K K)
    (hL : L.obj.IsLeftNondegenerate)
    (hC : ContractionsDetectScalars (finiteFormQuadratic L)) : SpinorNorm L :=
  ⟨MonoidHom.liftOfSurjective (lipschitzActionHom L) (lipschitzActionHom_surjective L hL)
      ⟨lipschitzSpinorNorm L, ker_lipschitzActionHom_le_ker_lipschitzSpinorNorm L hL hC⟩, by
    intro v hv
    rw [← lipschitzActionHom_cliffordVectorUnit L v hv,
      MonoidHom.liftOfRightInverse_comp_apply]
    exact lipschitzSpinorNorm_cliffordVectorUnit L v hv⟩

end LeanCategories.Lattices.Valued
