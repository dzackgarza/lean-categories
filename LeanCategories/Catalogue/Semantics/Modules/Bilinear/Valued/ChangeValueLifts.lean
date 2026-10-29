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

/-- For a commutative ring `R`, selected `R`-modules `W`, `W'`, a linear map
`a : W →ₗ[R] W'`, a `W`-valued formed module `X`, and a formed arrow
`i : K ⟶ (changeValue R W a).obj X`, the `W`-valued formed module on the
actual carrier of `K` with pairing `B(x,y) = X.pairing (i x) (i y)`.
Here `i x` denotes the underlying linear map of `i`; `pulledBack_pairing`
states this formula. No monicity condition is needed for this pullback object. -/
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

/-- With the parameters of `pulledBack`, the formed map from that
`W`-valued pullback to `X` whose underlying `R`-linear map is exactly the
underlying map of `i`. Its preservation equation is the defining formula
`(pulledBack R W W' a X i).pairing x y = X.pairing (i x) (i y)`. -/
def pulledBackHom (X : BilinModuleCat R W) {K : BilinModuleCat R W'}
    (i : K ⟶ (changeValue R W a).obj X) : pulledBack R W W' a X i ⟶ X :=
  BilinModuleCat.homMk (BilinModuleCat.underlyingMap (W := W') i) (fun _ _ => rfl)

/-- With the parameters of `pulledBack`, the isomorphism
`(changeValue R W a).obj (pulledBack R W W' a X i) ≅ K`.
Both underlying linear directions are the identity on `K.carrier`. The left pairing is
`a (X.pairing (i x) (i y))`, which equals `K.pairing x y` by the formed
arrow equation for `i`. Thus this comparison retains the actual selected
`W'`-valued form of `K`. -/
def pulledBackIso (X : BilinModuleCat R W) {K : BilinModuleCat R W'}
    (i : K ⟶ (changeValue R W a).obj X) :
    (changeValue R W a).obj (pulledBack R W W' a X i) ≅ K :=
  BilinModuleCat.isoMk (LinearEquiv.refl R K.carrier)
    (fun x y => (BilinModuleCat.map_pairing i x y).symm)

/-- Cartesian monomorphism lifts for the functor
`changeValue R W a : BilinModuleCat R W ⥤ BilinModuleCat R W'`, which
postcomposes each pairing by the selected linear map `a : W →ₗ[R] W'`.
For `X`, `K`, and a monomorphism `i : K ⟶ (changeValue R W a).obj X`,
the lifted object has carrier `K.carrier` and `W`-valued pairing
`(x,y) ↦ X.pairing (i x) (i y)`. Its defining arrow to `X` has underlying
map `i`; both comparison directions with `K` have the identity underlying map.
These components are `pulledBack`, `pulledBackHom` and `pulledBackIso`.
For `g : (changeValue R W a).obj Y ⟶ K` and `f : Y ⟶ X` with
`(changeValue R W a).map f = g ≫ i`, the unique factor
`Y ⟶ pulledBack R W W' a X i` has underlying map `g`. Its two equations
and uniqueness are the laws `MonoLift.factor_map`, `MonoLift.factor_hom`
and `MonoLift.factor_unique` of this selected lift. -/
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

/-- The four callable components for `changeValueMonoLift R W W' a`, at
the full selected parameters `R`, `W`, `W'`, `a`, `X`, `K`, and
`i : K ⟶ (changeValue R W a).obj X` with `Mono i`. The object is the
`R`-module `K.carrier` with pairing `X.pairing (i x) (i y)` valued in `W`; the defining
map to `X` has underlying map `i`; the forward and backward comparisons
between its changed-value object and `K` are identities on `K.carrier`.
`MonoLift.computation_fac`, `computation_forward_backward` and
`computation_backward_forward` are the formal laws for these data. The
separate canonical universal factor is supplied by `MonoLift.factorComputation`. -/
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
