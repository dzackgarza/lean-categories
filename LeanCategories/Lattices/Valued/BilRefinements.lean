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

The further lattice conditions are property classifiers on `Bil` too, stated for every ring `R`
and value module `W` (audit §4): a finite carrier (with the lattice property: finite projective
lattices), a free one, *evenness* `b(v, v) ∈ 2W` — for integral forms (`W = R`) the `I = 2R`
integrality of the diagonal quadratic form (`EvenDiagonal.lean`) — and *unimodularity*, the
adjoint `L → Hom(L, W)` being bijective (`L^{#} = L`, metric unimodularity).
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

/-- A property of `Bil`, as the full-subcategory classifier. -/
noncomputable def bilPropertyClassifier (P : ObjectProperty BilinFormsOverRings.{u}) :
    PropertyClassifier.{u + 1, u} (Cat.of BilinFormsOverRings.{u}) where
  total := Cat.of P.FullSubcategory
  forget := P.ι.toCatHom
  full := inferInstanceAs P.ι.Full
  faithful := inferInstanceAs P.ι.Faithful

/-- A finite carrier. -/
def bilIsFinite : ObjectProperty BilinFormsOverRings.{u} :=
  fun X ↦ Module.Finite X.base X.fiber.formed.carrier

/-- A free carrier. -/
def bilIsFree : ObjectProperty BilinFormsOverRings.{u} :=
  fun X ↦ Module.Free X.base X.fiber.formed.carrier

/-- Evenness of a `W`-valued form: `b(v, v) ∈ 2W` for every `v`. -/
def bilIsEven : ObjectProperty BilinFormsOverRings.{u} :=
  fun X ↦ ∀ v, ∃ w : X.fiber.value, X.fiber.formed.pairing v v = (2 : X.base) • w

/-- Unimodularity: the adjoint `L → Hom(L, W)` is bijective. -/
def bilIsUnimodular : ObjectProperty BilinFormsOverRings.{u} :=
  fun X ↦ Function.Bijective X.fiber.formed.adjoint

noncomputable def finiteClassifier := bilPropertyClassifier.{u} bilIsFinite
noncomputable def freeClassifier := bilPropertyClassifier.{u} bilIsFree
noncomputable def evenClassifier := bilPropertyClassifier.{u} bilIsEven
noncomputable def unimodularClassifier := bilPropertyClassifier.{u} bilIsUnimodular

/-- For `R`-valued forms, `2R` is the ideal `(2)`: `(∃ w, x = 2 • w) ↔ x ∈ (2)`. -/
theorem exists_two_smul_iff_mem_span {R : Type u} [CommRing R] (x : R) :
    (∃ w : R, x = (2 : R) • w) ↔ x ∈ Ideal.span {(2 : R)} := by
  rw [Ideal.mem_span_singleton']
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨y, by rw [smul_eq_mul, mul_comm]⟩
  · rintro ⟨y, rfl⟩
    exact ⟨y, by rw [smul_eq_mul, mul_comm]⟩

end LeanCategories.Lattices.Valued
