/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Lattices.Valued.Spinor
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal

@[expose] public section

open CategoryTheory
open LeanCategories.Modules.Bilinear.Valued

namespace LeanCategories.Lattices.Valued

universe u

variable {K : Type u} [Field K]

/-- The orthogonal complement of the line spanned by `v`. -/
def anisotropicComplement (L : FiniteFormCat K K) (v : L.obj.carrier) :
    Submodule K L.obj.carrier :=
  L.obj.asBilinForm.orthogonal (K ∙ v)

/-- Membership in the complement is orthogonality to `v`. -/
theorem mem_anisotropicComplement_iff (L : FiniteFormCat K K)
    (v x : L.obj.carrier) :
    x ∈ anisotropicComplement L v ↔ L.obj.pairing v x = 0 := by
  constructor
  · intro hx
    exact hx v (Submodule.mem_span_singleton_self v)
  · intro hx n hn
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hn
    change L.obj.pairing (a • v) x = 0
    rw [BilinModuleCat.pairing_smul_left, hx, smul_zero]

/-- A nonsingular vector splits its line off from its orthogonal complement. -/
theorem isCompl_span_anisotropicComplement (L : FiniteFormCat K K)
    (v : L.obj.carrier) (hv : L.obj.pairing v v ≠ 0) :
    IsCompl (K ∙ v) (anisotropicComplement L v) :=
  LinearMap.BilinForm.isCompl_span_singleton_orthogonal hv

/-- An isometry fixing `v` preserves the orthogonal complement of `v`. -/
theorem map_anisotropicComplement_le (L : FiniteFormCat K K)
    (v : L.obj.carrier) (g : BilinModuleCat.OrthogonalGroup L.obj)
    (hg : BilinModuleCat.OrthogonalGroup.actOnVector g v = v) :
    BilinModuleCat.OrthogonalGroup.actOnSubmodule g (anisotropicComplement L v) ≤
      anisotropicComplement L v := by
  rintro y ⟨x, hx, rfl⟩
  rw [SetLike.mem_coe, mem_anisotropicComplement_iff] at hx
  rw [mem_anisotropicComplement_iff]
  have hgv : g.1 v = v := hg
  calc L.obj.pairing v (g.1 x)
      = L.obj.pairing (g.1 v) (g.1 x) := by rw [hgv]
    _ = L.obj.pairing v x := g.property v x
    _ = 0 := hx

/-- A nonzero nondegenerate symmetric form has an anisotropic vector.

If every vector were isotropic then polarization would make the whole form vanish, which a
nondegenerate form on a nonzero module cannot do. -/
theorem exists_pairing_self_ne_zero [Invertible (2 : K)] (L : FiniteFormCat K K)
    (hL : L.obj.IsLeftNondegenerate) {x : L.obj.carrier} (hx : x ≠ 0) :
    ∃ v : L.obj.carrier, L.obj.pairing v v ≠ 0 := by
  by_contra hcon
  push Not at hcon
  have hzero : ∀ y z : L.obj.carrier, L.obj.pairing y z = 0 := by
    intro y z
    have hsum := hcon (y + z)
    rw [BilinModuleCat.pairing_add_left, BilinModuleCat.pairing_add_right,
      BilinModuleCat.pairing_add_right, hcon y, hcon z, L.property.2 z y] at hsum
    have h2 : (2 : K) ≠ 0 := Invertible.ne_zero 2
    have hdouble : L.obj.pairing y z + L.obj.pairing y z = 0 := by simpa using hsum
    have : (2 : K) * L.obj.pairing y z = 0 := by
      rw [two_mul]
      exact hdouble
    exact (mul_eq_zero.mp this).resolve_left h2
  apply hx
  have hker : x ∈ LinearMap.ker L.obj.adjoint := by
    simp only [LinearMap.mem_ker]
    exact LinearMap.ext fun y => hzero x y
  rw [BilinModuleCat.IsLeftNondegenerate] at hL
  rw [hL] at hker
  simpa using hker

end LeanCategories.Lattices.Valued
