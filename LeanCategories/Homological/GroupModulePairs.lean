/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.CategoryTheory.Bicategory.Grothendieck
public import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete
public import Mathlib.CategoryTheory.Category.Cat.Op
public import Mathlib.RepresentationTheory.Rep.Res

/-!
# Categories of group-module pairs

Weibel, *An Introduction to Homological Algebra*, Constructions 6.7.5--6.7.6, pp. 189--194
(FC05-C06-U084, FC05-C06-U085).

Restriction along a group homomorphism `ρ : H → G` is Mathlib's `Rep.resFunctor ρ`.  As `ρ`
varies this gives a contravariant family of representation categories over `GrpCat`.  The two
categories in Weibel are therefore standard CoGrothendieck constructions:

* in the covariant group-homology category a morphism `(H,B) ⟶ (G,A)` is `ρ : H → G` together
  with an `H`-map `B ⟶ ρ^# A`;
* in the contravariant group-cohomology category the fiber categories are replaced by their
  opposites, so a morphism with the same base map is equivalently an `H`-map `ρ^# A ⟶ B`.

Only these categories are defined here.  Functoriality of group homology and cohomology on them is
result-level material and remains outside the Definitions sweep.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Functor
open CategoryTheory.Pseudofunctor
open CategoryTheory.Bicategory
open Opposite
open scoped CategoryTheory.Bicategory

namespace LeanCategories.Homological

universe u

/-- The contravariant family `G ↦ Rep ℤ G` with transition functors given by restriction of
representations.  This is the common family underlying Weibel 6.7.5 and 6.7.6. -/
def groupModuleRestrictionFunctor : GrpCat.{u}ᵒᵖ ⥤ Cat.{u, u + 1} where
  obj G := Cat.of (Rep.{u} ℤ G.unop)
  map f := (Rep.resFunctor.{u} (k := ℤ) f.unop.hom).toCatHom
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The restriction family promoted to a pseudofunctor so Mathlib's standard CoGrothendieck
construction can be used. -/
abbrev groupModuleRestrictionPseudofunctor :
    LocallyDiscrete GrpCat.{u}ᵒᵖ ⥤ᵖ Cat.{u, u + 1} :=
  groupModuleRestrictionFunctor.toPseudofunctor'

/-- Weibel's covariant category of group-module pairs.

An object is `(G,A)` with `A : Rep ℤ G`.  A morphism `(H,B) ⟶ (G,A)` consists of a group map
`ρ : H → G` and a morphism `B ⟶ Rep.res ρ A` in `Rep ℤ H`, exactly as in Construction 6.7.5.

Source: Weibel, Construction 6.7.5, pp. 189--194 (FC05-C06-U084). -/
abbrev CovariantGroupModulePairs :=
  Pseudofunctor.CoGrothendieck groupModuleRestrictionPseudofunctor

/-- The same restriction family with every representation category replaced by its opposite. -/
abbrev oppositeGroupModuleRestrictionPseudofunctor :
    LocallyDiscrete GrpCat.{u}ᵒᵖ ⥤ᵖ Cat.{u, u + 1} :=
  (groupModuleRestrictionFunctor ⋙ Cat.opFunctor).toPseudofunctor'

/-- Weibel's contravariant category of group-module pairs.

Its objects are again pairs `(G,A)`.  In the opposite fiber a morphism `(H,B) ⟶ (G,A)` over
`ρ : H → G` is a morphism `Bᵒᵖ ⟶ (ρ^#A)ᵒᵖ`, equivalently an `H`-map `ρ^#A ⟶ B`, exactly as in
Construction 6.7.6.

Source: Weibel, Construction 6.7.6, pp. 189--194 (FC05-C06-U085). -/
abbrev ContravariantGroupModulePairs :=
  Pseudofunctor.CoGrothendieck oppositeGroupModuleRestrictionPseudofunctor

end LeanCategories.Homological
