/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Lattices.Valued.Basic
public import LeanCategories.Lattices.Valued.ValueFibration
public import LeanCategories.CategoryTheory.OneCat.Classifier

@[expose] public section

/-!
# Lattices as a refinement of the category of bilinear forms

specs/registry-denotation-audit.md §4: lattices are not a fibration and are not closed under
base change. A lattice is an object of the total category `Bil` of bilinear forms
(`BilinFormsOverRings`) whose carrier is projective and whose form is symmetric
(`isLattice`, FOUNDATIONS §19.2); "lattices" is the full subcategory of `Bil` cut out by that
property, i.e. the refinement of `Bil` by a property classifier. Whether a base change
preserves the property is a theorem about that base change, not registry structure.

The fibre of this refinement over `(R, W)` is `LatticeCat R W`.
-/

open CategoryTheory

namespace LeanCategories.Lattices.Valued

universe u

open LeanCategories.Modules.Bilinear.Valued

/-- The lattice property on the total category of bilinear forms: projective carrier and
symmetric form, over the form's own ring and value module. -/
def bilIsLattice : ObjectProperty BilinFormsOverRings.{u} :=
  fun X ↦ isLattice X.base X.fiber.value X.fiber.formed

/-- Lattices over all rings and value modules: the full subcategory of `Bil`. -/
abbrev LatticesOverRings : Type (u + 1) := bilIsLattice.{u}.FullSubcategory

/-- The lattice property classifier on `Bil`: the full subcategory inclusion. -/
noncomputable def latticeClassifier :
    PropertyClassifier.{u + 1, u} (Cat.of BilinFormsOverRings.{u}) where
  total := Cat.of LatticesOverRings.{u}
  forget := bilIsLattice.{u}.ι.toCatHom
  full := inferInstanceAs bilIsLattice.{u}.ι.Full
  faithful := inferInstanceAs bilIsLattice.{u}.ι.Faithful

end LeanCategories.Lattices.Valued
