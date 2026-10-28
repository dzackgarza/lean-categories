/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Catalogue.Semantics.Modules.Bilinear.Valued.ChangeValueLifts
public meta import LeanCategories.Catalogue.Registry.Semantic
public meta import LeanCategories.Catalogue.Semantics.Modules.Bilinear.Valued.Catalogue

@[expose] public section

/-!
# The comparison for pullback of a selected value module

Let `a : W →ₗ[R] W'`, let `X` carry a `W`-valued bilinear form, and let
`i : K ⟶ (changeValue R W a).obj X` preserve the selected `W'`-valued forms.
The existing `ChangeValueLifts.pulledBackIso` compares the changed-value
pullback of `X` along `i` with the original formed object `K`. This module
publishes its two actual arrows, at those complete endpoints. Both underlying
linear maps are identities, while form preservation is supplied by `i`.

No monicity assumption is used. In particular, the comparison applies to a
cone with a nontrivial kernel, independently of any monomorphism-lift call.
The equations below are the inverse laws and defining triangle of this
already constructed isomorphism; the original pullback and lift are unchanged.

Sources: `ChangeValueLifts.pulledBackIso`, `BilinModuleCat.isoMk`, and
Mathlib `CategoryTheory.Iso.hom_inv_id` / `inv_hom_id`.
-/

open CategoryTheory
open LeanCategories.Modules.Bilinear.Valued

namespace CasCatalogue.Modules.Bilinear.Valued.ChangeValueLifts

universe u

variable (R : Type u) [CommRing R]
variable (W W' : Type u) [AddCommGroup W] [Module R W]
  [AddCommGroup W'] [Module R W']
variable (a : W →ₗ[R] W')

/-- The forward arrow of `pulledBackIso R W W' a X i`, from
`(changeValue R W a).obj (pulledBack R W W' a X i)` to the actual formed
object `K`. All selected scalar, value-module, form and input-arrow parameters
are retained. Its underlying map sends every `x : K.carrier` to itself.
The arrow exists for every formed `i`; it does not require `Mono i`. -/
def pulledBackForward (X : BilinModuleCat R W) {K : BilinModuleCat R W'}
    (i : K ⟶ (changeValue R W a).obj X) :
    (changeValue R W a).obj (pulledBack R W W' a X i) ⟶ K :=
  (pulledBackIso R W W' a X i).hom

/-- The inverse arrow of the same `pulledBackIso`, with exact source `K`
and target `(changeValue R W a).obj (pulledBack R W W' a X i)`.
Its underlying map is the identity on `K.carrier`, and its formed-map law
uses the form preserved by the supplied arrow `i`. No monicity is required. -/
def pulledBackBackward (X : BilinModuleCat R W) {K : BilinModuleCat R W'}
    (i : K ⟶ (changeValue R W a).obj X) :
    K ⟶ (changeValue R W a).obj (pulledBack R W W' a X i) :=
  (pulledBackIso R W W' a X i).inv

theorem pulledBackForward_underlying (X : BilinModuleCat R W) {K : BilinModuleCat R W'}
    (i : K ⟶ (changeValue R W a).obj X) :
    BilinModuleCat.underlyingMap (W := W') (pulledBackForward R W W' a X i) =
      LinearMap.id := rfl

theorem pulledBackBackward_underlying (X : BilinModuleCat R W) {K : BilinModuleCat R W'}
    (i : K ⟶ (changeValue R W a).obj X) :
    BilinModuleCat.underlyingMap (W := W') (pulledBackBackward R W W' a X i) =
      LinearMap.id := rfl

theorem pulledBackForward_backward (X : BilinModuleCat R W) {K : BilinModuleCat R W'}
    (i : K ⟶ (changeValue R W a).obj X) :
    pulledBackForward R W W' a X i ≫ pulledBackBackward R W W' a X i = 𝟙 _ :=
  (pulledBackIso R W W' a X i).hom_inv_id

theorem pulledBackBackward_forward (X : BilinModuleCat R W) {K : BilinModuleCat R W'}
    (i : K ⟶ (changeValue R W a).obj X) :
    pulledBackBackward R W W' a X i ≫ pulledBackForward R W W' a X i = 𝟙 _ :=
  (pulledBackIso R W W' a X i).inv_hom_id

/-- The comparison precedes the original arrow in the changed-value triangle. -/
theorem pulledBackForward_hom (X : BilinModuleCat R W) {K : BilinModuleCat R W'}
    (i : K ⟶ (changeValue R W a).obj X) :
    pulledBackForward R W W' a X i ≫ i =
      (changeValue R W a).map (pulledBackHom R W W' a X i) := by
  apply Quiver.Hom.unop_inj
  apply CategoryOfElements.ext
  apply Quiver.Hom.unop_inj
  apply ModuleCat.hom_ext
  rfl

end CasCatalogue.Modules.Bilinear.Valued.ChangeValueLifts

namespace CasCatalogue

normalized_registry .morphism
  { id := ⟨"mor.bilin_module.pulled_back_forward"⟩, category := CategoryId.bilinModule
    name := "pulled_back_forward"
    declaration :=
      `CasCatalogue.Modules.Bilinear.Valued.ChangeValueLifts.pulledBackForward }

normalized_registry .morphism
  { id := ⟨"mor.bilin_module.pulled_back_backward"⟩, category := CategoryId.bilinModule
    name := "pulled_back_backward"
    declaration :=
      `CasCatalogue.Modules.Bilinear.Valued.ChangeValueLifts.pulledBackBackward }

end CasCatalogue
