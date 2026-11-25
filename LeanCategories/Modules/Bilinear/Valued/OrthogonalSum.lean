/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Modules.Bilinear.Valued.Fixed
public import LeanCategories.Modules.Bilinear.Valued.OrthogonalGroup

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

/-! ## Block diagonal isometries of an orthogonal sum

The orthogonal group of a pairing that is the sum of two coordinate pairings receives the two
factors' orthogonal groups by block-diagonal isometries, `(g₁, g₂) ↦ (g₁, g₂)`. This is the
general statement of the orthogonal-sum map `O(M₁) × O(M₂) → O(M₁ ⊕ M₂)`; the specialization to
lattices is `LeanCategories.Lattices.Valued.orthogonalSumGroupHom`.

LC-09 search record (formalization-corpus API, whole index): `orthogonalSum OrthogonalGroup
prod` (2 files), `orthogonalSum isometry group product` (6 files), `"prodCongr" isometry
bilinear` (12 files) — all LMFDB blueprint prose or unrelated differential-geometry uses of
`prodCongr`; no formalized block-diagonal orthogonal-group map to port. Mathlib supplies the
pieces and nothing more: `LinearEquiv.prodCongr` (`Mathlib/LinearAlgebra/Prod.lean:773`) with
`LinearEquiv.prodCongr_apply` (line 782), and the subgroup API. The declarations below are glue.
-/

namespace BilinModuleCat

variable {M N : BilinModuleCat R W}

/-- Block diagonal elements of the orthogonal group of a pairing that is the sum of the two
coordinate pairings. Neither the factors nor their forms need to be nondegenerate, symmetric or
finite, and `hB` is the only way the sum pairing is used. -/
def prodCongrBlock (B : LinearMap.BilinMap R (M.carrier × N.carrier) W)
    (hB : ∀ x y, B x y = M.pairing x.1 y.1 + N.pairing x.2 y.2)
    (g : orthogonalSubgroup M × orthogonalSubgroup N) :
    orthogonalSubgroup (BilinModuleCat.ofBilinMap B) :=
  ⟨LinearEquiv.prodCongr g.1.1 g.2.1, by
    intro x y
    have key : ∀ p q : M.carrier × N.carrier,
        B ((LinearEquiv.prodCongr g.1.1 g.2.1) p)
          ((LinearEquiv.prodCongr g.1.1 g.2.1) q) = B p q := by
      intro p q
      rw [LinearEquiv.prodCongr_apply, LinearEquiv.prodCongr_apply, hB, hB,
        g.1.2 p.1 q.1, g.2.2 p.2 q.2]
    exact key x y⟩

/-- The block-diagonal map on orthogonal groups of an orthogonal sum, as a group
homomorphism. -/
noncomputable def prodCongrHom (B : LinearMap.BilinMap R (M.carrier × N.carrier) W)
    (hB : ∀ x y, B x y = M.pairing x.1 y.1 + N.pairing x.2 y.2) :
    orthogonalSubgroup M × orthogonalSubgroup N →*
      orthogonalSubgroup (BilinModuleCat.ofBilinMap B) where
  toFun := prodCongrBlock B hB
  map_one' := Subtype.ext (by ext x; rfl)
  map_mul' _ _ := Subtype.ext (by ext x; rfl)

/-- The block-diagonal map of an orthogonal sum is injective: the two components of an element
are its values on the two summands. -/
theorem prodCongrHom_injective (B : LinearMap.BilinMap R (M.carrier × N.carrier) W)
    (hB : ∀ x y, B x y = M.pairing x.1 y.1 + N.pairing x.2 y.2) :
    Function.Injective (prodCongrHom B hB) := by
  rintro ⟨g₁, g₂⟩ ⟨h₁, h₂⟩ hgh
  have hv : (LinearEquiv.prodCongr g₁.1 g₂.1) = (LinearEquiv.prodCongr h₁.1 h₂.1) :=
    congrArg Subtype.val hgh
  have h₁' : g₁.1 = h₁.1 := by
    apply LinearEquiv.ext
    intro x
    have hx := congrArg (fun e => (e (x, 0)).1) hv
    simpa [LinearEquiv.prodCongr_apply] using hx
  have h₂' : g₂.1 = h₂.1 := by
    apply LinearEquiv.ext
    intro y
    have hy := congrArg (fun e => (e (0, y)).2) hv
    simpa [LinearEquiv.prodCongr_apply] using hy
  exact Prod.ext (Subtype.ext h₁') (Subtype.ext h₂')

end BilinModuleCat

end LeanCategories.Modules.Bilinear.Valued
