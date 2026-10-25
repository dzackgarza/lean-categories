/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Modules.Bilinear.Valued.Fixed

@[expose] public section

namespace LeanCategories.Modules.Bilinear.Valued

universe u v

variable {R W : Type u} [CommRing R] [AddCommGroup W] [Module R W]

/-- A finite indexed bilinear form whose pairing is the sum of coordinate pairings has
zero left radical when each coordinate form has zero left radical. The empty sum is included. -/
theorem isLeftNondegenerate_of_indexedOrthogonalPairing
    {I : Type v} [Fintype I] (L : I → BilinModuleCat R W)
    (B : LinearMap.BilinMap R ((i : I) → (L i).carrier) W)
    (hB : ∀ x y, B x y = ∑ i, (L i).pairing (x i) (y i))
    (hL : ∀ i, (L i).IsLeftNondegenerate) : B.SeparatingLeft := by
  classical
  intro x hx
  funext i
  apply hL i (x i)
  intro y
  have h := hx (Pi.single i y)
  rw [hB] at h
  rw [Fintype.sum_eq_single i] at h
  · simpa using h
  · intro j hji
    simp [Pi.single_eq_of_ne hji]

/-- A finite indexed bilinear form whose pairing is the sum of coordinate pairings has
zero right radical when each coordinate form has zero right radical. The empty sum is included. -/
theorem isRightNondegenerate_of_indexedOrthogonalPairing
    {I : Type v} [Fintype I] (L : I → BilinModuleCat R W)
    (B : LinearMap.BilinMap R ((i : I) → (L i).carrier) W)
    (hB : ∀ x y, B x y = ∑ i, (L i).pairing (x i) (y i))
    (hL : ∀ i, (L i).IsRightNondegenerate) : B.SeparatingRight := by
  classical
  intro y hy
  funext i
  apply hL i (y i)
  intro x
  have h := hy (Pi.single i x)
  rw [hB] at h
  rw [Fintype.sum_eq_single i] at h
  · simpa using h
  · intro j hji
    simp [Pi.single_eq_of_ne hji]

/-- Finite orthogonal sums of nondegenerate bilinear modules have both radicals zero,
including the empty indexed sum. -/
theorem isNondegenerate_of_indexedOrthogonalPairing
    {I : Type v} [Fintype I] (L : I → BilinModuleCat R W)
    (B : LinearMap.BilinMap R ((i : I) → (L i).carrier) W)
    (hB : ∀ x y, B x y = ∑ i, (L i).pairing (x i) (y i))
    (hL : ∀ i, (L i).IsNondegenerate) : B.Nondegenerate :=
  ⟨isLeftNondegenerate_of_indexedOrthogonalPairing L B hB (fun i ↦ (hL i).1),
    isRightNondegenerate_of_indexedOrthogonalPairing L B hB (fun i ↦ (hL i).2)⟩

end LeanCategories.Modules.Bilinear.Valued
