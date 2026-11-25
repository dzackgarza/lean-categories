/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.Groupoid

/-!
# The coslice of a groupoid at an object has unique morphisms

For a groupoid `C` and an object `X`, two objects of the coslice `Under X` are arrows out of
`X`. Every such arrow is invertible, so the triangle `f.hom ≫ φ = g.hom` that defines a
morphism `φ : f ⟶ g` has exactly one solution `φ = f.hom⁻¹ ≫ g.hom`. Consequently `Under X`
over a groupoid is a *thin* category in which every pair of objects has a unique morphism.

This is the categorical fact behind the named-section discipline of `FOUNDATIONS.md` §44.3 for
markings: the *total* coslice is contractible as a category, so an appeal to it can never
distinguish two markings. The information sits in the object, whose arrow `f.hom` is data, and
in the fibre over a fixed codomain, which is a torsor under the automorphism group of `X`.

The lemmas are stated for an arbitrary groupoid, so a consumer over the core of a category
`Core D` (itself a groupoid) instantiates them directly.

## Provenance

Mathlib owns `CategoryTheory.Under` (`Mathlib/CategoryTheory/Comma/Over/Basic.lean`, `Under X :=
StructuredArrow X (𝟭 T)`), `Under.w` and `StructuredArrow.hom_ext`; the groupoid bookkeeping
`Groupoid.inv_comp` is Mathlib's. The uniqueness statement itself was searched for
(`Under subsingleton hom`, `Under thin`, `coslice groupoid unique morphism`, `StructuredArrow
subsingleton`, `comma groupoid`) in the repository and in Mathlib and is not present: Mathlib
proves `Under.mkIdInitial` (initiality of the identity) but not that the coslice of a groupoid
is thin.
-/

@[expose] public section

noncomputable section

open CategoryTheory

namespace CategoryTheory

universe v u

variable {C : Type u} [Groupoid C] {X : C}

/-- In the coslice of a groupoid, the right component of a morphism out of `f` into `g` is
forced: it is `f.hom⁻¹ ≫ g.hom`. -/
theorem Under.Hom.right_eq_inv_comp {f g : Under X} (φ : Under.Hom f g) :
    Under.Hom.right φ = Groupoid.inv f.hom ≫ g.hom := by
  have h : f.hom ≫ Under.Hom.right φ = g.hom := Under.w φ
  rw [← h, ← Category.assoc, Groupoid.inv_comp, Category.id_comp]

/-- The unique morphism of the coslice of a groupoid from `f` to `g`. -/
def Under.homOf (f g : Under X) : f ⟶ g :=
  Under.homMk (Groupoid.inv f.hom ≫ g.hom) (by
    rw [← Category.assoc, Groupoid.comp_inv, Category.id_comp])

/-- Over a groupoid, the coslice at `X` is a thin category: any two morphisms with the same
source and target agree. The statement is phrased for `CommaMorphism`, the underlying structure
of `Under.Hom`, and applies to goals stated with `f ⟶ g` by definitional unfolding. -/
theorem Under.subsingleton_hom (f g : Under X) : Subsingleton (CommaMorphism f g) :=
  ⟨fun φ ψ ↦ by
    have hφ := Under.Hom.right_eq_inv_comp φ
    have hψ := Under.Hom.right_eq_inv_comp ψ
    exact CommaMorphism.ext (Subsingleton.elim _ _) (hφ.trans hψ.symm)⟩

/-- The canonical morphism is the only morphism of the coslice of a groupoid. -/
theorem Under.homOf_unique {f g : Under X} (φ : f ⟶ g) : φ = Under.homOf f g :=
  (Under.subsingleton_hom f g).elim φ (Under.homOf f g)

/-- The coslice of a groupoid at `X` is a thin category: every hom-type `f ⟶ g` is a
subsingleton. -/
theorem Under.subsingleton_hom_iff (f g : Under X) : Subsingleton (f ⟶ g) :=
  Under.subsingleton_hom f g

end CategoryTheory
