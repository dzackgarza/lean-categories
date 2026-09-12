/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Topology.Sheaves.Skyscraper
public import Mathlib.Topology.Sheaves.Limits
public import Mathlib.Algebra.Category.Grp.Abelian

/-!
# The Godement endofunctor

Weibel, *An Introduction to Homological Algebra*, Construction 8.6.15, pp. 278--285
(FC05-C08-U073).

For a sheaf `F` of abelian groups on `X`, the Godement construction starts with
`T(F) = ∏ x, x_*(F_x)`. Mathlib already owns the stalk functor, skyscraper-sheaf functor, and their
adjunction at each point; this file supplies the all-points family and its categorical product.
The later assertions that the canonical cosimplicial resolution is Γ-acyclic and computes sheaf
cohomology are result-level content.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace LeanCategories.Homological

universe u

/-- The point-indexed family `x ↦ x_*(F_x)` used by the Godement construction.

Source: Weibel, Construction 8.6.15, pp. 278--285 (FC05-C08-U073). -/
noncomputable def godementFamilyFunctor (X : TopCat.{u}) :
    TopCat.Sheaf AddCommGrpCat.{u} X ⥤ (X → TopCat.Sheaf AddCommGrpCat.{u} X) := by
  classical
  exact
    { obj := fun F x =>
        skyscraperSheaf x ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).obj F.1)
      map := fun f x =>
        (skyscraperSheafFunctor (C := AddCommGrpCat.{u}) x).map
          ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map f.1)
      map_id := fun F => by
        funext x
        change (skyscraperSheafFunctor (C := AddCommGrpCat.{u}) x).map
          ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map (𝟙 F.1)) = 𝟙 _
        simp
      map_comp := fun f g => by
        funext x
        change (skyscraperSheafFunctor (C := AddCommGrpCat.{u}) x).map
          ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map (f.1 ≫ g.1)) =
            (skyscraperSheafFunctor (C := AddCommGrpCat.{u}) x).map
                ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map f.1) ≫
              (skyscraperSheafFunctor (C := AddCommGrpCat.{u}) x).map
                ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map g.1)
        rw [Functor.map_comp, Functor.map_comp] }

/-- The Godement endofunctor `T(F)=∏_x x_*(F_x)`.

Source: Weibel, Construction 8.6.15, pp. 278--285 (FC05-C08-U073). -/
noncomputable def godementFunctor (X : TopCat.{u}) :
    TopCat.Sheaf AddCommGrpCat.{u} X ⥤ TopCat.Sheaf AddCommGrpCat.{u} X :=
  godementFamilyFunctor X ⋙ Limits.Pi.functor X

/-- The first Godement object `T(F) = ∏_{x∈X} x_*(F_x)`.

Source: Weibel, Construction 8.6.15, pp. 278--285 (FC05-C08-U073). -/
abbrev godementObject (X : TopCat.{u}) (F : TopCat.Sheaf AddCommGrpCat.{u} X) :
    TopCat.Sheaf AddCommGrpCat.{u} X :=
  (godementFunctor X).obj F

end LeanCategories.Homological
