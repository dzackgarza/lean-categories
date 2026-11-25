/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Lattices.Valued.IsotropicReduction
public import LeanCategories.Lattices.Valued.BaseChange
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.LinearAlgebra.TensorProduct.Quotient
public import Mathlib.RingTheory.Flat.Basic

/-!
# The reduction `e^⊥/ℤe` at a primitive isotropic line: freeness (#120)

For a finite free `ℤ`-lattice `L` and a primitive isotropic vector `e`, the reduction
`e^⊥/ℤe` is again a free `ℤ`-module: it embeds into the torsion-free quotient `L/ℤe`, and a
finitely generated torsion-free `ℤ`-module is free (`Module.free_of_finite_type_torsion_free'`).

`e^⊥` is `L.obj.orthogonalSubmodule (ℤ • e)` and `ℤe ⊆ e^⊥` is its intersection with the line; the
reduction is the quotient of the former by the latter, which is `IsotropicReductionData.perp` and
`IsotropicReductionData.kernel` for the rank-one data of `ℤ • e`.

The `ℤ`-subquotients here carry two candidate `Module ℤ` instances (`Submodule.module` and
`Submodule.Quotient.module` against `AddCommGroup.toIntModule`); the inherited ones are pinned
locally, as `IsotropicReductionU2Quotient` does, so that one instance is used throughout.

**Not here:** the isometry with `(e_ℝ)^⊥/⟨e_ℝ⟩` of `#119`. It needs base change to commute with
both the submodule `e^⊥` and the quotient by `ℤe`; see the `COMPLAINTS.md` entry of #120.

## References

* V. V. Nikulin, *Integral symmetric bilinear forms and some of their applications*, Izv. Akad.
  Nauk SSSR Ser. Mat. 43 (1979), §1: primitive isotropic vectors and the reduction `P^⊥/P`.
-/

@[expose] public section

open LeanCategories.Modules.Bilinear.Valued

namespace LeanCategories.Lattices.Valued

attribute [local instance 10000] Submodule.module
attribute [local instance 10000] Submodule.Quotient.module

variable {L : IntegralLatticeCat ℤ}

/-! ## The line `ℤ • e`, its orthogonal complement, and the kernel -/

/-- The line `ℤ • e` spanned by `e`. -/
noncomputable abbrev isotropicLine (e : L.obj.carrier) : Submodule ℤ L.obj.carrier :=
  Submodule.span ℤ {e}

/-- The orthogonal complement `e^⊥` of the line `ℤ • e`. -/
noncomputable abbrev isotropicLinePerp (e : L.obj.carrier) : Submodule ℤ L.obj.carrier :=
  L.obj.orthogonalSubmodule (isotropicLine (L := L) e)

/-- The line `ℤ • e` as a submodule of `e^⊥`, i.e. the kernel of `e^⊥ → e^⊥/ℤe`. -/
noncomputable abbrev isotropicLineKernel (e : L.obj.carrier) :
    Submodule ℤ ↥(isotropicLinePerp (L := L) e) :=
  Submodule.comap (isotropicLinePerp (L := L) e).subtype (isotropicLine (L := L) e)

theorem mem_isotropicLineKernel_iff (e : L.obj.carrier) (x : ↥(isotropicLinePerp (L := L) e)) :
    x ∈ isotropicLineKernel (L := L) e ↔ (x : L.obj.carrier) ∈ isotropicLine (L := L) e :=
  Submodule.mem_comap

/-- An isotropic vector lies in its own orthogonal complement. -/
theorem mem_isotropicLinePerp (e : L.obj.carrier) (he : L.obj.pairing e e = 0) :
    e ∈ isotropicLinePerp (L := L) e := by
  rw [isotropicLinePerp, BilinModuleCat.mem_orthogonalSubmodule_iff]
  intro p hp
  obtain ⟨n, rfl⟩ := Submodule.mem_span_singleton.mp hp
  rw [BilinModuleCat.pairing_smul_left, he, smul_eq_mul, mul_zero]

/-! ## Freeness of the reduction -/

/-- **The reduction `e^⊥/ℤe` of a primitive isotropic vector is a free `ℤ`-module.** It is
finitely generated (a quotient of a submodule of a finite module), and torsion-free because it
embeds into `L/ℤe`, which is torsion-free by primitivity. -/
theorem moduleFree_isotropicLineQuotient [Module.Finite ℤ L.obj.carrier]
    (e : L.obj.carrier) (hprim : IsPrimitiveSubmodule (isotropicLine (L := L) e)) :
    Module.Free ℤ (↥(isotropicLinePerp (L := L) e) ⧸ isotropicLineKernel (L := L) e) := by
  have htf : Module.IsTorsionFree ℤ (L.obj.carrier ⧸ isotropicLine (L := L) e) := hprim
  haveI := htf
  -- the comparison map into the primitive quotient `L/ℤe`
  let f : (↥(isotropicLinePerp (L := L) e) ⧸ isotropicLineKernel (L := L) e) →ₗ[ℤ]
      (L.obj.carrier ⧸ isotropicLine (L := L) e) :=
    Submodule.mapQ (isotropicLineKernel (L := L) e) (isotropicLine (L := L) e)
      (isotropicLinePerp (L := L) e).subtype (fun _ hx => hx)
  have hf : Function.Injective f := by
    intro x y hxy
    induction x using Submodule.Quotient.induction_on with
    | _ x =>
      induction y using Submodule.Quotient.induction_on with
      | _ y =>
        have h : (Submodule.Quotient.mk (x : L.obj.carrier) :
            L.obj.carrier ⧸ isotropicLine (L := L) e) =
            Submodule.Quotient.mk (y : L.obj.carrier) := hxy
        rw [Submodule.Quotient.eq] at h
        rw [Submodule.Quotient.eq, mem_isotropicLineKernel_iff]
        simpa using h
  haveI : Module.IsTorsionFree ℤ
      (↥(isotropicLinePerp (L := L) e) ⧸ isotropicLineKernel (L := L) e) :=
    Function.Injective.moduleIsTorsionFree f hf (fun r m => f.map_smul r m)
  exact Module.free_of_finite_type_torsion_free'

end LeanCategories.Lattices.Valued
