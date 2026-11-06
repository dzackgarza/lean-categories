/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Homological.SheafPresheafComparison

/-! # Card: `LeanCategories.Homological.noContinuousGlobalLog`

source: Weibel, *An Introduction to Homological Algebra* (1994), §1.6 (FC05-C01-U057).

Published copy of a result from `LeanCategories.Homological.SheafPresheafComparison`; the definition module keeps the original declaration, this file restates it, and the platform submission replaces the delegated proof with `by sorry`.
-/

@[expose] public section

namespace LeanCategories.Cards

open LeanCategories.Homological

open CategoryTheory Opposite TopologicalSpace
open scoped AlgebraicGeometry
universe u
namespace LeanCategories.Homological

/-- There is no continuous logarithm defined on all of `ℂˣ`. -/
theorem LeanCategories_Homological_noContinuousGlobalLog :
    ¬ ∃ l : C(ℂˣ, ℂ),
      ∀ z : ℂˣ, complexExpAddHom (l z) = Additive.ofMul z := by
  rintro ⟨l, hl⟩
  let turn : ℝ → ℂ := fun t => (t : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)
  let g₁ : ℝ → ℂ := fun t => l (Additive.toMul (complexExpAddHom (turn t)))
  let g₂ : ℝ → ℂ := fun t => l 1 + turn t
  have hturn : Continuous turn := by
    dsimp [turn]
    fun_prop
  have hg₁ : Continuous g₁ := by
    dsimp [g₁]
    exact l.continuous.comp
      (continuous_toMul.comp (complexExpAddHom.continuous.comp hturn))
  have hg₂ : Continuous g₂ := by
    dsimp [g₂]
    exact continuous_const.add hturn
  have he : complexExpAddHom ∘ g₁ = complexExpAddHom ∘ g₂ := by
    funext t
    change complexExpAddHom (l (Additive.toMul (complexExpAddHom (turn t)))) =
      complexExpAddHom (l 1 + turn t)
    rw [hl, map_add, hl]
    simp
  have hzero : g₁ 0 = g₂ 0 := by
    dsimp [g₁, g₂, turn]
    simp
  have hEq : g₁ = g₂ :=
    isCoveringMap_complexExpAdd.eq_of_comp_eq hg₁ hg₂ he 0 hzero
  have hOne := congrFun hEq 1
  dsimp [g₁, g₂, turn] at hOne
  have hOne' :
      l (Additive.toMul (complexExpAddHom (2 * (Real.pi : ℂ) * Complex.I))) =
        l 1 + 2 * (Real.pi : ℂ) * Complex.I := by
    simpa only [one_mul] using hOne
  have hloop : Additive.toMul (complexExpAddHom (2 * (Real.pi : ℂ) * Complex.I)) = (1 : ℂˣ) := by
    apply Units.ext
    change Complex.exp (2 * (Real.pi : ℂ) * Complex.I) = 1
    exact Complex.exp_two_pi_mul_I
  rw [hloop] at hOne'
  have : (2 * (Real.pi : ℂ) * Complex.I) = 0 := by
    have h : l 1 + 2 * (Real.pi : ℂ) * Complex.I = l 1 + 0 := by
      simpa only [add_zero] using hOne'.symm
    exact add_left_cancel h
  exact Complex.two_pi_I_ne_zero this

end LeanCategories.Homological
end LeanCategories.Cards
