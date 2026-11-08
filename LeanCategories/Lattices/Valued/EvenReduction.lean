/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Lattices.Valued.IsotropicReduction
public import LeanCategories.Lattices.Valued.ScaleAndEvenness
public import LeanCategories.Lattices.Valued.Sublattice
public import Mathlib.LinearAlgebra.FreeModule.PID

/-!
# The even projective isotropic reduction

Over a PID with a finite free lattice, the isotropic reduction `Q = P^⊥/P` has a finite,
torsion-free carrier. Torsion-freeness comes directly from primitivity of `P`: if `a • z` is in
the quotient's kernel, i.e. `a • x ∈ P`, then `x` is in the saturation of `P`, which is `P` itself.
Finite generation over a PID and torsion-freeness give a free/projective carrier, so the reduced
formed module is an integral lattice, not an externally postulated construction. Nondegeneracy,
symmetry and evenness descend from those of `L`.
-/

@[expose] public section

open LeanCategories.Modules.Bilinear.Valued
open LeanCategories.Lattices.Valued

namespace LeanCategories.Lattices.Valued.IsotropicReductionData

universe u

variable {R : Type u} [CommRing R] [IsDomain R]
variable {L : IntegralLatticeCat R}

/-- The reduction of a primitive isotropic submodule over a PID has torsion-free carrier. -/
theorem reduction_isTorsionFree (D : IsotropicReductionData L) :
    Module.IsTorsionFree R (D.perp ⧸ D.kernel) := by
  rw [Module.isTorsionFree_iff_smul_eq_zero]
  intro a z hz
  by_cases ha : a = 0
  · exact Or.inl ha
  refine Or.inr ?_
  induction z using Submodule.Quotient.induction_on with
  | _ x =>
    change (Submodule.Quotient.mk x : D.perp ⧸ D.kernel) = 0
    rw [Submodule.Quotient.mk_eq_zero]
    have hax : a • x ∈ D.kernel := by
      rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_smul]
      exact hz
    have hmem : (x : L.obj.carrier) ∈ saturation D.submodule := by
      rw [mem_saturation_iff]
      exact ⟨a, ha, hax⟩
    exact (isPrimitiveSubmodule_iff_saturation_le D.submodule).mp D.primitive hmem

/-- Over a PID the reduced module is finite and torsion-free, hence free and projective. -/
theorem reduction_projective [IsPrincipalIdealRing R] [Module.Finite R L.obj.carrier]
    (D : IsotropicReductionData L) : Module.Projective R (D.perp ⧸ D.kernel) := by
  letI : Module.IsTorsionFree R (D.perp ⧸ D.kernel) := reduction_isTorsionFree D
  letI : Module.Finite R (D.perp ⧸ D.kernel) :=
    Module.Finite.of_surjective D.kernel.mkQ (Submodule.mkQ_surjective D.kernel)
  exact @Module.Projective.of_free R _ _ _ _ (Module.free_iff_isTorsionFree.mpr
    (reduction_isTorsionFree D))

/-- The reduced form is even whenever the original lattice is even. -/
theorem reduction_isEven [IsPrincipalIdealRing R] [Module.Free R L.obj.carrier]
    [Module.Finite R L.obj.carrier]
    (D : IsotropicReductionData L) (hL : L.obj.IsSymmetric)
    (hEven : IsEven L) : IsEven
      ((⟨D.reduction hL, reduction_projective D, D.reduction_isSymmetric hL⟩ :
        IntegralLatticeCat R)) := by
  rw [IsEven, isIEven_iff_value_mem]
  intro z
  induction z using Submodule.Quotient.induction_on with
  | _ x =>
    change (D.reduction hL).pairing (Submodule.Quotient.mk x) (Submodule.Quotient.mk x) ∈
      Ideal.span {(2 : R)}
    rw [reduction_pairing_mk]
    exact (isIEven_iff_value_mem L (Ideal.span {(2 : R)})).mp hEven (x : L.obj.carrier)

end LeanCategories.Lattices.Valued.IsotropicReductionData
