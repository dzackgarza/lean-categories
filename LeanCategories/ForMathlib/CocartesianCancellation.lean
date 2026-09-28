/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.CategoryTheory.FiberedCategory.Cocartesian

@[expose] public section

/-!
# Cancellation for strongly cocartesian morphisms

FOUNDATIONS Lemma 31.2a: for functors `P : 𝒳 ⥤ 𝒴` and `q : 𝒴 ⥤ 𝒮`, a morphism that is
strongly `P ⋙ q`-cocartesian and whose image under `P` is strongly `q`-cocartesian is
strongly `P`-cocartesian. This is the dual of the cancellation property of cartesian
morphisms (Lurie, *Higher Topos Theory*, Prop. 2.4.1.3). No indexed Lean source states it
(formalization-corpus searches `IsStronglyCartesian comp functor cancellation`,
`isStronglyCartesian_of_comp`, `cartesian morphism composite functor`,
`cartesian of composite fibration`, `IsHomLift comp functor`).
-/

namespace CategoryTheory.Functor

universe v₁ v₂ v₃ u₁ u₂ u₃

variable {𝒮 : Type u₁} {𝒴 : Type u₂} {𝒳 : Type u₃} [Category.{v₁} 𝒮] [Category.{v₂} 𝒴]
  [Category.{v₃} 𝒳] (P : 𝒳 ⥤ 𝒴) (q : 𝒴 ⥤ 𝒮)

/-- Cancellation: strongly `P ⋙ q`-cocartesian with strongly `q`-cocartesian image implies
strongly `P`-cocartesian. -/
theorem isStronglyCocartesian_of_comp {a b : 𝒳} (φ : a ⟶ b)
    [IsStronglyCocartesian (P ⋙ q) ((P ⋙ q).map φ) φ]
    [IsStronglyCocartesian q (q.map (P.map φ)) (P.map φ)] :
    IsStronglyCocartesian P (P.map φ) φ where
  universal_property' {b'} g φ' _ := by
    have hφ' : P.map φ' = P.map φ ≫ g :=
      (CategoryTheory.IsHomLift.eq_of_isHomLift P (P.map φ ≫ g) φ').symm
    have : IsHomLift (P ⋙ q) ((P ⋙ q).map φ ≫ q.map g) φ' := by
      have h : (P ⋙ q).map φ' = (P ⋙ q).map φ ≫ q.map g := by
        simp [hφ']
      rw [← h]
      infer_instance
    obtain ⟨χ, ⟨hχlift, hχfac⟩, hχuniq⟩ :=
      IsStronglyCocartesian.universal_property' (p := P ⋙ q) (f := (P ⋙ q).map φ) (φ := φ)
        (q.map g) φ'
    have hPχ : P.map χ = g := by
      have h₁ : IsHomLift q (q.map g) (P.map χ) := by
        have : (P ⋙ q).map χ = q.map g :=
          (CategoryTheory.IsHomLift.eq_of_isHomLift (P ⋙ q) (q.map g) χ).symm
        change IsHomLift q (q.map g) (P.map χ)
        rw [show q.map g = q.map (P.map χ) from this.symm]
        infer_instance
      exact IsStronglyCocartesian.ext q (q.map (P.map φ)) (P.map φ) (q.map g)
        (by rw [← P.map_comp, hχfac, hφ'])
    refine ⟨χ, ⟨?_, hχfac⟩, ?_⟩
    · rw [← hPχ]
      infer_instance
    · rintro χ' ⟨hχ'lift, hχ'fac⟩
      apply hχuniq
      refine ⟨?_, hχ'fac⟩
      have : P.map χ' = g := (CategoryTheory.IsHomLift.eq_of_isHomLift P g χ').symm
      change IsHomLift (P ⋙ q) (q.map g) χ'
      rw [show q.map g = (P ⋙ q).map χ' by simp [this]]
      infer_instance

end CategoryTheory.Functor
