/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Topology.SmashProduct
public import Mathlib.Topology.Homotopy.HomotopyGroup

/-!
# Spectra

Weibel, *An Introduction to Homological Algebra*, Definition 10.9.1, pp. 405--408
(FC05-C10-U100).

A spectrum is a sequence of based spaces `E n` together with based homeomorphisms
`E n ≅ Ω(E (n+1))`. Maps are levelwise based maps compatible with the structure
homeomorphisms. The based spaces themselves reuse the repository's canonical `BasedTop`, the
undercategory `* / Top`.
-/

@[expose] public section

open CategoryTheory

namespace LeanCategories.Homological

open LeanCategories.Topology

universe u

/-- A spectrum: based spaces `E_n` equipped with homeomorphisms from `E_n` to the based loop
space of `E_{n+1}`.  The second field says that each homeomorphism is based.

Source: Weibel, Definition 10.9.1, pp. 405--408 (FC05-C10-U100). -/
structure Spectrum where
  space : ℕ → BasedTop.{u}
  loopHomeomorph : ∀ n : ℕ, (space n).right ≃ₜ Path (space (n + 1)).point (space (n + 1)).point
  loopHomeomorph_point : ∀ n : ℕ,
    loopHomeomorph n (space n).point = Path.refl (space (n + 1)).point

namespace Spectrum

/-- A map of spectra is a compatible sequence of based maps.  Compatibility is written
pointwise on loops: applying the next-level map to the loop corresponding to `x` gives the loop
corresponding to the image of `x`.

Source: Weibel, Definition 10.9.1, pp. 405--408 (FC05-C10-U100). -/
@[ext]
structure Hom (E F : Spectrum.{u}) where
  app : ∀ n : ℕ, E.space n ⟶ F.space n
  comm : ∀ (n : ℕ) (x : (E.space n).right) (t : unitInterval),
    (app (n + 1)).right ((E.loopHomeomorph n x) t) =
      (F.loopHomeomorph n ((app n).right x)) t := by cat_disch

instance : Category Spectrum.{u} where
  Hom := Hom
  id E :=
    { app := fun _ => 𝟙 _
      comm := by intros; rfl }
  comp := fun {E F G} f g =>
    { app := fun n => f.app n ≫ g.app n
      comm := by
        intro n x t
        change (g.app (n + 1)).right ((f.app (n + 1)).right ((E.loopHomeomorph n x) t)) =
          (G.loopHomeomorph n ((g.app n).right ((f.app n).right x))) t
        rw [f.comm n x t, g.comm n ((f.app n).right x) t] }
  id_comp := by
    intro E F f
    apply Hom.ext
    funext n
    simp
  comp_id := by
    intro E F f
    apply Hom.ext
    funext n
    simp
  assoc := by
    intro E F G H f g h
    apply Hom.ext
    funext n
    simp

/-- The one-point spectrum.

Source: Weibel, Definition 10.9.1, pp. 405--408 (FC05-C10-U100). -/
noncomputable def point : Spectrum.{u} where
  space _ := Under.mk (TopCat.ofHom ⟨fun _ : PUnit => PUnit.unit, continuous_const⟩)
  loopHomeomorph _ :=
    { toFun := fun _ => Path.refl PUnit.unit
      invFun := fun _ => PUnit.unit
      left_inv := fun _ => rfl
      right_inv := by
        intro p
        apply Path.ext
        funext t
        exact Subsingleton.elim _ _
      continuous_toFun := continuous_const
      continuous_invFun := continuous_const }
  loopHomeomorph_point _ := rfl

end Spectrum

end LeanCategories.Homological
