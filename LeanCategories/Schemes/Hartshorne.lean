/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.Differentials.Presheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.Topology.Sheaves.Flasque
public import Mathlib.Topology.Sheaves.Stalks

/-!
# Hartshorne Chapters II--III routes

This file gives catalogue names for the existing Mathlib scheme, sheaf, and
differential constructions. It does not define Weil or Cartier divisors,
projective morphisms, formal schemes, dualizing sheaves, or other objects
which the pinned reference search does not provide.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

namespace LeanCategories.Schemes

universe u v w

/-! ### Schemes, sheaves, stalks, and fibres -/

/-- The category of locally ringed spaces used by Mathlib's scheme definition. -/
abbrev LocallyRingedSpaceObject : Type u := AlgebraicGeometry.LocallyRingedSpace.{u}

/-- Mathlib's scheme object, which extends a locally ringed space. -/
abbrev SchemeObject : Type u := AlgebraicGeometry.Scheme.{u}

/-- A presheaf valued in a category `A` on a small category `C`. -/
abbrev PresheafCategory (C : Type u) (A : Type v) [Category.{w} C] [Category.{w} A] :=
  Cᵒᵖ ⥤ A

/-- The category of sheaves valued in `A` for a Grothendieck topology `J`. -/
abbrev SheafCategory (C : Type u) (A : Type v) [Category.{w} C] [Category.{w} A]
    (J : GrothendieckTopology C) :=
  CategoryTheory.Sheaf J A

/-- The stalk of a presheaf on a topological space. -/
abbrev SheafStalk (X : TopCat.{u}) (A : Type v) [Category.{w} A]
    (F : X.Presheaf A) (x : X) : A :=
  TopCat.Presheaf.stalk F x

/-- The germ map from a section to the stalk. -/
abbrev SheafGerm (X : TopCat.{u}) (A : Type v) [Category.{w} A]
    (F : X.Presheaf A) (U : TopologicalSpace.Opens X) (x : X) (hx : x ∈ U) :
    F.obj (Opposite.op U) ⟶ SheafStalk X A F x :=
  TopCat.Presheaf.germ F U x hx

/-- The scheme-theoretic fibre of a scheme morphism at a point. -/
abbrev SchemeMorphismFiber {X Y : Scheme.{u}} (f : X ⟶ Y) (y : Y) : Scheme.{u} :=
  Scheme.Hom.fiber f y

/-! ### Sheaves of modules on schemes -/

/-- The category of sheaves of `𝒪_X`-modules. -/
abbrev SchemeModuleCategory (X : Scheme.{u}) := X.Modules

/-- The presheaf-of-modules category underlying `X.Modules`. -/
abbrev SchemeModulePresheafCategory (X : Scheme.{u}) := X.PresheafOfModules

/-- The forgetful functor from `X.Modules` to presheaves of modules. -/
abbrev SchemeModuleToPresheaf (X : Scheme.{u}) := X.Modules.toPresheafOfModules

/-- Pushforward of sheaves of modules along a scheme morphism. -/
abbrev SchemeModulePushforward {X Y : Scheme.{u}} (f : X ⟶ Y) :
    X.Modules ⥤ Y.Modules :=
  Scheme.Modules.pushforward f

/-- Pullback of sheaves of modules along a scheme morphism. -/
abbrev SchemeModulePullback {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Y.Modules ⥤ X.Modules :=
  Scheme.Modules.pullback f

/-- The pullback--pushforward adjunction for scheme module sheaves. -/
abbrev SchemeModulePullbackPushforwardAdjunction {X Y : Scheme.{u}} (f : X ⟶ Y) :
    SchemeModulePullback f ⊣ SchemeModulePushforward f :=
  Scheme.Modules.pullbackPushforwardAdjunction f

/-- The Mathlib predicate for a locally free sheaf of modules. -/
abbrev IsLocallyFreeSchemeModule {X : Scheme.{u}} (M : X.Modules) : Prop :=
  M.IsLocallyFree

/-- The Mathlib predicate for a quasi-coherent sheaf of modules. -/
abbrev IsQuasiCoherentSchemeModule {X : Scheme.{u}} (M : X.Modules) : Prop :=
  M.IsQuasicoherent

/-- The Mathlib predicate for a finitely presented sheaf of modules. -/
abbrev IsFinitePresentationSchemeModule {X : Scheme.{u}} (M : X.Modules) : Prop :=
  M.IsFinitePresentation

/-- A Mathlib presentation datum for a quasi-coherent module sheaf. -/
abbrev SchemeModuleQuasiCoherentData {X : Scheme.{u}} (M : X.Modules) :=
  M.QuasicoherentData

/-! ### Differentials -/

/-- The module of Kähler differentials of a morphism of commutative rings. -/
abbrev KahlerDifferentialModule {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) : ModuleCat.{u} S :=
  CommRingCat.KaehlerDifferential (CommRingCat.ofHom f)

/-- A relative derivation with values in a module. -/
abbrev ModuleRelativeDerivation {R S : Type u} [CommRing R] [CommRing S]
    (M : ModuleCat.{v} S) (f : CommRingCat.of R ⟶ CommRingCat.of S) :=
  ModuleCat.Derivation M f

/-- The relative differentials presheaf supplied by Mathlib. -/
abbrev RelativeDifferentialsPresheaf {D : Type u} [Category.{w} D]
    {S R : Dᵒᵖ ⥤ CommRingCat.{v}} (f : S ⟶ R) :=
  PresheafOfModules.DifferentialsConstruction.relativeDifferentials' f

end LeanCategories.Schemes
