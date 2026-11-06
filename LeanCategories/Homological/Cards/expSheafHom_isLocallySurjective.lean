/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Homological.SheafPresheafComparison

/-! # Card: `LeanCategories.Homological.expSheafHom_isLocallySurjective`

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

/-- The exponential morphism of continuous-function sheaves is locally surjective. -/
theorem LeanCategories_Homological_expSheafHom_isLocallySurjective (X : TopCat.{0}) :
    TopCat.Presheaf.IsLocallySurjective (expSheafHom X).hom := by
  rw [TopCat.Presheaf.isLocallySurjective_iff]
  intro U t x hx
  change C((Opens.toTopCat X).obj U, TopCat.of (Additive ℂˣ)) at t
  let xu : U := ⟨x, hx⟩
  obtain ⟨a, ha⟩ := complexExpAddHom_surjective (t xu)
  obtain ⟨e, hae, he⟩ := isCoveringMap_complexExpAdd.isLocalHomeomorph a
  have ht : t xu ∈ e.target := by
    rw [← ha, he]
    exact e.map_source hae
  let W : Set U := t ⁻¹' e.target
  have hW : IsOpen W := e.open_target.preimage t.continuous
  let V : Opens X :=
    ⟨U.inclusion' '' W, U.isOpenEmbedding.isOpenMap _ hW⟩
  have hVU : V ≤ U := by
    intro y hy
    rcases hy with ⟨z, hz, rfl⟩
    exact z.2
  let iVU : C(V, U) := ((Opens.toTopCat X).map (homOfLE hVU)).hom
  have htarget (z : V) : t (iVU z) ∈ e.target := by
    rcases z.2 with ⟨w, hw, hwz⟩
    have hzi : iVU z = w := by
      apply Subtype.ext
      exact hwz.symm
    rw [hzi]
    exact hw
  let s : C(V, ℂ) :=
    ⟨fun z => e.symm (t (iVU z)),
      e.continuousOn_symm.comp_continuous
        (t.continuous.comp iVU.continuous) htarget⟩
  refine ⟨V, hVU, ?_, ?_⟩
  · refine ⟨s, ?_⟩
    change complexExpAddHom.toContinuousMap.comp s = t.comp iVU
    apply ContinuousMap.ext
    intro z
    change complexExpAddHom (e.symm (t (iVU z))) = t (iVU z)
    rw [he]
    exact e.right_inv (htarget z)
  · exact ⟨xu, ht, rfl⟩

end LeanCategories.Homological
end LeanCategories.Cards
