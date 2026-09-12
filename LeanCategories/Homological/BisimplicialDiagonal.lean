/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicTopology.SimplicialObject.Basic
public import Mathlib.CategoryTheory.Functor.Currying
public import Mathlib.CategoryTheory.Products.Basic

/-!
# The diagonal of a bisimplicial object

Weibel, *An Introduction to Homological Algebra*, §8.5, pp. 275--277
(FC05-C08-U052).

A bisimplicial object is a functor `Δᵒᵖ ⥤ (Δᵒᵖ ⥤ C)`.  Mathlib's `Functor.uncurry`
identifies this with a functor `Δᵒᵖ × Δᵒᵖ ⥤ C`; precomposition with the categorical diagonal
then gives the diagonal simplicial object.  Thus degree `n` is definitionally `A_{n,n}`, and a
simplicial operator acts in both directions by the same operator, exactly as in Weibel.
-/

@[expose] public section

open CategoryTheory

namespace LeanCategories.Homological

universe u v

variable {C : Type u} [Category.{v} C]

/-- The diagonal simplicial object of a bisimplicial object.

In degree `n` this is `A_{n,n}`.  For a simplex-category map `α`, its map is the composite of the
horizontal and vertical maps associated to `α`; hence the face maps are `∂ᵍ_i ∂ᵛ_i` and the
degeneracies are `σᵍ_i σᵛ_i` in Weibel's notation.

Source: Weibel, §8.5, pp. 275--277 (FC05-C08-U052). -/
def bisimplicialDiagonal (A : SimplicialObject (SimplicialObject C)) : SimplicialObject C :=
  Functor.diag (SimplexCategoryᵒᵖ) ⋙ Functor.uncurry.obj A

end LeanCategories.Homological
