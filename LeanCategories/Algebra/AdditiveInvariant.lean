/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

@[expose] public section

open CategoryTheory

namespace LeanCategories.Algebra

universe u v w

variable {R : Type u} [Ring R]
variable {A : Type w} [AddCommGroup A]

/-- Atiyah–Macdonald, Chapter 2 (FC04-C02-U040): a function on a class of modules is
additive when it satisfies the Euler relation on every short exact sequence whose three terms
belong to the class. -/
def IsAdditiveOnShortExact
    (P : ModuleCat.{v} R → Prop) (inv : ModuleCat.{v} R → A) : Prop :=
  ∀ (S : ShortComplex (ModuleCat.{v} R)), S.ShortExact →
    P S.X₁ → P S.X₂ → P S.X₃ → inv S.X₁ - inv S.X₂ + inv S.X₃ = 0

/-- The zero function satisfies the short-exact Euler relation on every class. -/
theorem isAdditiveOnShortExact_zero (P : ModuleCat.{v} R → Prop) :
    IsAdditiveOnShortExact P (fun _ => (0 : A)) := by
  intro _ _ _ _ _
  simp only [sub_self, add_zero]

/-- A constant function on all modules is additive only when its value is zero.
The all-zero short exact sequence already detects a nonzero constant. -/
theorem isAdditiveOnShortExact_const_iff (a : A) :
    IsAdditiveOnShortExact (fun _ : ModuleCat.{v} R => True) (fun _ => a) ↔ a = 0 := by
  constructor
  · intro h
    let Z : ModuleCat.{v} R := ModuleCat.of R PUnit
    let S : ShortComplex (ModuleCat.{v} R) :=
      ShortComplex.mk (𝟙 Z) (𝟙 Z) (by ext x)
    have s : S.Splitting :=
      { r := 𝟙 Z
        s := 𝟙 Z
        f_r := by simp [S]
        s_g := by simp [S]
        id := by ext x }
    simpa only [sub_self, zero_add] using h S s.shortExact trivial trivial trivial
  · rintro rfl
    exact isAdditiveOnShortExact_zero _

/-- FC04-C02-U041: dimension is an additive integer-valued function on finite-dimensional
vector spaces. The proof compares categorical short exactness with rank–nullity. -/
theorem isAdditiveOnShortExact_finrank (K : Type u) [DivisionRing K] :
    IsAdditiveOnShortExact (fun M : ModuleCat.{v} K => Module.Finite K M)
      (fun M => (Module.finrank K M : ℤ)) := by
  intro S hS _ h₂ _
  change (Module.finrank K S.X₁ : ℤ) - Module.finrank K S.X₂ + Module.finrank K S.X₃ = 0
  let : Module.Finite K S.X₂ := h₂
  have hrank := S.g.hom.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hS.moduleCat_surjective_g, finrank_top,
    ← hS.exact.moduleCat_range_eq_ker,
    LinearMap.finrank_range_of_inj hS.moduleCat_injective_f] at hrank
  have hcast := congrArg (fun n : ℕ => (n : ℤ)) hrank
  push_cast at hcast
  omega

end LeanCategories.Algebra
