/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Catalogue.Semantics.Modules.Bilinear.Valued.Kernels
public import LeanCategories.Modules.Bilinear.Valued.ChangeValue
public meta import LeanCategories.Catalogue.Registry.Semantic
public meta import LeanCategories.Catalogue.Semantics.ConstructorCatalogue
public meta import LeanCategories.Catalogue.Semantics.Modules.Bilinear.Valued.Expressions

@[expose] public section

/-!
# Cartesian restriction along a change of values

For a selected linear map `a : W → W'`, the existing functor `changeValue a`
postcomposes a `W`-valued form. A formed arrow `i : K → changeValue a X`
pulls the original `W`-valued form back to the actual carrier of `K`.
Postcomposing the pulled-back form by `a` recovers the selected form on `K`,
because `i` preserves that form. The comparison has the identity carrier map.

This is a cartesian lift, including uniqueness for arbitrary compatible arrows.
It composes with the existing module-to-formed restriction by `MonoLift.comp`.
For `W = W₁ × W₂` and `a = fst`, this restricts the second chosen form after
the first formed restriction has already been computed.

Source: Mathlib `LinearMap.compl₁₂`; the existing `changeValue`, `homMk`, and
the full cartesian universal property in `CasCatalogue.MonoLift`.
-/

open CategoryTheory
open LeanCategories.Modules.Bilinear.Valued

namespace CasCatalogue.Modules.Bilinear.Valued.ChangeValueLifts

universe u

variable (R : Type u) [CommRing R]
variable (W W' : Type u) [AddCommGroup W] [Module R W]
  [AddCommGroup W'] [Module R W']
variable (a : W →ₗ[R] W')

/-- Pull back the original value-module form along the actual formed arrow. -/
def pulledBack (X : BilinModuleCat R W) {K : BilinModuleCat R W'}
    (i : K ⟶ (changeValue R W a).obj X) : BilinModuleCat R W :=
  BilinModuleCat.ofBilinMap
    (X.bilinMap.compl₁₂ (BilinModuleCat.underlyingMap (W := W') i)
      (BilinModuleCat.underlyingMap (W := W') i))

/-- The pulled-back form keeps the original values and actual arrow action. -/
theorem pulledBack_pairing (X : BilinModuleCat R W) {K : BilinModuleCat R W'}
    (i : K ⟶ (changeValue R W a).obj X) (x y : K.carrier) :
    (pulledBack R W W' a X i).pairing x y =
      X.pairing (BilinModuleCat.underlyingMap (W := W') i x)
        (BilinModuleCat.underlyingMap (W := W') i y) := rfl

/-- The defining map of the restriction has exactly the given carrier map. -/
def pulledBackHom (X : BilinModuleCat R W) {K : BilinModuleCat R W'}
    (i : K ⟶ (changeValue R W a).obj X) : pulledBack R W W' a X i ⟶ X :=
  BilinModuleCat.homMk (BilinModuleCat.underlyingMap (W := W') i) (fun _ _ => rfl)

/-- The original selected `W'`-form on `K` is recovered, not merely an isomorphic carrier. -/
def pulledBackIso (X : BilinModuleCat R W) {K : BilinModuleCat R W'}
    (i : K ⟶ (changeValue R W a).obj X) :
    (changeValue R W a).obj (pulledBack R W W' a X i) ≅ K :=
  BilinModuleCat.isoMk (LinearEquiv.refl R K.carrier)
    (fun x y => (BilinModuleCat.map_pairing i x y).symm)

/-- The actual cartesian lift for the existing change-of-values functor. -/
def changeValueMonoLift : MonoLift (changeValue R W a) where
  obj X _ i _ := pulledBack R W W' a X i
  hom X _ i _ := pulledBackHom R W W' a X i
  iso X _ i _ := pulledBackIso R W W' a X i
  fac X K i _ := by
    apply Quiver.Hom.unop_inj
    apply CategoryOfElements.ext
    apply Quiver.Hom.unop_inj
    apply ModuleCat.hom_ext
    rfl
  universal X K i _ Y g f hf := by
    have he (x : Y.carrier) :
        BilinModuleCat.underlyingMap f x =
          BilinModuleCat.underlyingMap (W := W') i
            (BilinModuleCat.underlyingMap (W := W') g x) :=
      congrArg (fun k : (changeValue R W a).obj Y ⟶ (changeValue R W a).obj X =>
        BilinModuleCat.underlyingMap (W := W') k x) hf
    let h : Y ⟶ pulledBack R W W' a X i :=
      BilinModuleCat.homMk (BilinModuleCat.underlyingMap (W := W') g) (by
        intro x y
        change X.pairing
          (BilinModuleCat.underlyingMap (W := W') i
            (BilinModuleCat.underlyingMap (W := W') g x))
          (BilinModuleCat.underlyingMap (W := W') i
            (BilinModuleCat.underlyingMap (W := W') g y)) = Y.pairing x y
        rw [← he x, ← he y]
        exact BilinModuleCat.map_pairing f x y)
    refine ⟨h, ⟨?_, ?_⟩, ?_⟩
    · apply Quiver.Hom.unop_inj
      apply CategoryOfElements.ext
      apply Quiver.Hom.unop_inj
      apply ModuleCat.hom_ext
      rfl
    · apply Quiver.Hom.unop_inj
      apply CategoryOfElements.ext
      apply Quiver.Hom.unop_inj
      apply ModuleCat.hom_ext
      ext x
      exact (he x).symm
    · intro k hk
      apply Quiver.Hom.unop_inj
      apply CategoryOfElements.ext
      apply Quiver.Hom.unop_inj
      apply ModuleCat.hom_ext
      ext x
      exact congrArg (fun l : (changeValue R W a).obj Y ⟶ K =>
        BilinModuleCat.underlyingMap (W := W') l x) hk.1

/-- Only the four required data components cross the computational interface. -/
def changeValueMonoLiftComputation : MonoLiftComputation (changeValue R W a) :=
  (changeValueMonoLift R W W' a).computation

end CasCatalogue.Modules.Bilinear.Valued.ChangeValueLifts

namespace CasCatalogue

normalized_registry .lift
  { id := ⟨"lift.bilin_module.change_value_restriction"⟩
    edge := .constructMap ConstructorId.arrow (.functor FunctorId.bilinModuleChangeValue)
    evidence := `CasCatalogue.Modules.Bilinear.Valued.ChangeValueLifts.changeValueMonoLift
    computation := some `CasCatalogue.Modules.Bilinear.Valued.ChangeValueLifts.changeValueMonoLiftComputation }

end CasCatalogue
