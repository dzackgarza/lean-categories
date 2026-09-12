/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic

/-!
# Acyclic objects for a functor on complexes

Weibel, *An Introduction to Homological Algebra*, Definition 10.5.4, pp. 390--393
(FC05-C10-U060).

The target is a homotopy category of cochain complexes in an abelian category.  Mathlib already
packages its acyclic objects as `HomotopyCategory.subcategoryAcyclic`, with membership equivalent
to vanishing of every homology object.
-/

@[expose] public section

open CategoryTheory

namespace LeanCategories.Homological

universe u v u' v'

variable {K : Type u} [Category.{v} K]
variable (B : Type u') [Category.{v'} B] [Abelian B]

/-- An object `X` is `F`-acyclic when the complex represented by `F.obj X` is acyclic.

Pinned Mathlib's `HomotopyCategory.mem_subcategoryAcyclic_iff` identifies this condition with
`H^i(FX)=0` for every integer `i`, exactly the equivalent formulation in the source.

Source: Weibel, Definition 10.5.4, pp. 390--393 (FC05-C10-U060). -/
def IsFunctorAcyclic
    (F : K ⥤ HomotopyCategory B (ComplexShape.up ℤ)) (X : K) : Prop :=
  HomotopyCategory.subcategoryAcyclic B (F.obj X)

end LeanCategories.Homological
