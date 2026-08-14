/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Pseudofunctor
public import Mathlib.RingTheory.SimpleModule.Basic
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.Algebra.Module.Projective
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.Algebra.Category.ModuleCat.Injective
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.Algebra.Module.Torsion.Free
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Artinian.Module
public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.RingTheory.Support
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
public import Mathlib.Algebra.Ring.Opposite
public import Mathlib.CategoryTheory.Category.Cat
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import LeanCategories.Algebra.Concrete.Rings

@[expose] public section

/-!
# Mathlib module atoms

* `RingObjects` — `RingCat` as the category of base rings for `R ↦ Modules(R)`
* `ModulesOf` — fibre at an arbitrary ring object

* `free` — `Module.Free`
* `finitelyGenerated` — `Module.Finite`
* `finiteRank` — free with a **finite** basis index. This is **not** `Module.Finite`:
  finitely generated modules need not be free / finite-rank.
-/

namespace LeanCategories.Modules.Mathlib

open CategoryTheory
open LeanCategories
open LeanCategories.Foundation.Mathlib

universe u w

set_option linter.checkUnivs false

/-- Category of base rings for the family `R ↦ Modules(R)`. -/
def RingObjects : ObjCat.{u + 1, u} := Cat.of RingCat.{u}

/-- Fibre of the parameterized family at an arbitrary ring object. -/
noncomputable def ModulesOf (R : RingCat.{u}) : ObjCat.{max u (w + 1), w} :=
  Cat.of (ModuleCat.{w} R)

/-- Mathlib's contravariant module-family transport, with identity and composition comparison. -/
noncomputable def moduleCatRestrictScalarsPseudofunctor :
    Pseudofunctor (LocallyDiscrete RingCat.{u}ᵒᵖ)
      (Cat.{w, max u (w + 1)}) :=
  RingCat.moduleCatRestrictScalarsPseudofunctor.{w, u}

/-- The family value; this is not a covariant functor `RingCat ⥤ Cat`. -/
noncomputable def modulesFamilyValue (R : RingCat.{u}) :
    ObjCat.{max u (w + 1), w} :=
  (moduleCatRestrictScalarsPseudofunctor).obj (.mk (Opposite.op R))

example (R : RingCat.{u}) : modulesFamilyValue R = ModulesOf R := rfl

/-! ## Fibrewise classifiers -/

/-! ## Module invariants -/

/-- The annihilator ideal of an arbitrary `R`-module.

This is Mathlib's `Module.annihilator`; the alias keeps the invariant on the
module-family surface without adding a second definition.
-/
abbrev annihilator (R : RingCat.{u}) (M : ModuleCat.{w} R) : Ideal R :=
  Module.annihilator R M

/-- The prime-spectrum support of an arbitrary `R`-module.

This is Mathlib's `Module.support`, defined by nontrivial localization.
-/
abbrev support (R : RingCat.{u}) (M : ModuleCat.{w} R) : Set (PrimeSpectrum R) :=
  Module.support R M

/-- The associated-prime set of an arbitrary `R`-module.

This is Mathlib's `associatedPrimes`; no finiteness hypothesis is imposed.
-/
abbrev associatedPrimes (R : RingCat.{u}) (M : ModuleCat.{w} R) : Set (Ideal R) :=
  Module.associatedPrimes R M

/-- Free `R`-modules. -/
abbrev FreeModuleCat (R : RingCat.{u}) : Type (max u (w + 1)) :=
  ObjectProperty.FullSubcategory
    (C := ModuleCat.{w} R) (fun M : ModuleCat.{w} R => Module.Free R M)

/-- Finitely generated `R`-modules (`Module.Finite`). -/
abbrev FinitelyGeneratedModuleCat (R : RingCat.{u}) : Type (max u (w + 1)) :=
  ObjectProperty.FullSubcategory
    (C := ModuleCat.{w} R) (fun M : ModuleCat.{w} R => Module.Finite R M)

/-- Projective `R`-modules. -/
abbrev ProjectiveModuleCat (R : RingCat.{u}) : Type (max u (w + 1)) :=
  ObjectProperty.FullSubcategory
    (C := ModuleCat.{w} R) (fun M : ModuleCat.{w} R => Module.Projective R M)

/-- Injective `R`-modules. -/
abbrev InjectiveModuleCat (R : RingCat.{u}) : Type (max u (w + 1)) :=
  ObjectProperty.FullSubcategory
    (C := ModuleCat.{w} R) (fun M : ModuleCat.{w} R => Module.Injective R M)

/-- Simple `R`-modules, with no restriction on cardinality. -/
abbrev SimpleModuleCat (R : RingCat.{u}) : Type (max u (w + 1)) :=
  ObjectProperty.FullSubcategory
    (C := ModuleCat.{w} R) (fun M : ModuleCat.{w} R => IsSimpleModule R M)

/-- Torsion `R`-modules. -/
abbrev TorsionModuleCat (R : RingCat.{u}) : Type (max u (w + 1)) :=
  ObjectProperty.FullSubcategory
    (C := ModuleCat.{w} R) (fun M : ModuleCat.{w} R => Module.IsTorsion R M)

/-- Torsion-free `R`-modules. -/
abbrev TorsionFreeModuleCat (R : RingCat.{u}) : Type (max u (w + 1)) :=
  ObjectProperty.FullSubcategory
    (C := ModuleCat.{w} R) (fun M : ModuleCat.{w} R => Module.IsTorsionFree R M)

/-- Finitely presented `R`-modules. -/
abbrev FinitelyPresentedModuleCat (R : RingCat.{u}) : Type (max u (w + 1)) :=
  ObjectProperty.FullSubcategory
    (C := ModuleCat.{w} R) (fun M : ModuleCat.{w} R => Module.FinitePresentation R M)

/-- Flat `R`-modules, with no finiteness or cardinality restriction. -/
abbrev FlatModuleCat (R : RingCat.{u}) : Type (max u (w + 1)) :=
  ObjectProperty.FullSubcategory
    (C := ModuleCat.{w} R) (fun M : ModuleCat.{w} R => Module.Flat R M)

/-! ### Faithfully flat modules -/

/-- Faithfully flat `R`-modules, using Mathlib's unrestricted predicate. -/
abbrev FaithfullyFlatModuleCat (R : RingCat.{u}) : Type (max u (w + 1)) :=
  ObjectProperty.FullSubcategory
    (C := ModuleCat.{w} R) (fun M : ModuleCat.{w} R => Module.FaithfullyFlat R M)

/-! ### Noetherian and Artinian modules -/

/-- Noetherian `R`-modules, using Mathlib's unrestricted `IsNoetherian` predicate. -/
abbrev NoetherianModuleCat (R : RingCat.{u}) : Type (max u (w + 1)) :=
  ObjectProperty.FullSubcategory
    (C := ModuleCat.{w} R) (fun M : ModuleCat.{w} R => IsNoetherian R M)

/-- Artinian `R`-modules, using Mathlib's unrestricted `IsArtinian` predicate. -/
abbrev ArtinianModuleCat (R : RingCat.{u}) : Type (max u (w + 1)) :=
  ObjectProperty.FullSubcategory
    (C := ModuleCat.{w} R) (fun M : ModuleCat.{w} R => IsArtinian R M)

/-- Semisimple `R`-modules, using Mathlib's unrestricted `IsSemisimpleModule` predicate. -/
abbrev SemisimpleModuleCat (R : RingCat.{u}) : Type (max u (w + 1)) :=
  ObjectProperty.FullSubcategory
    (C := ModuleCat.{w} R) (fun M : ModuleCat.{w} R => IsSemisimpleModule R M)

/-! ### Faithful modules -/

/-- Modules whose scalar action is faithful, using Mathlib's `FaithfulSMul` class. -/
abbrev FaithfulModuleCat (R : RingCat.{u}) : Type (max u (w + 1)) :=
  ObjectProperty.FullSubcategory
    (C := ModuleCat.{w} R) (fun M : ModuleCat.{w} R => FaithfulSMul R M)

/-- Inclusion of free `R`-modules into all `R`-modules. -/
def freeInclusion (R : RingCat.{u}) : FreeModuleCat R ⥤ ModuleCat.{w} R :=
  ObjectProperty.ι (C := ModuleCat.{w} R) (fun M : ModuleCat.{w} R => Module.Free R M)

/-- Inclusion of finitely generated `R`-modules into all `R`-modules. -/
def finitelyGeneratedInclusion (R : RingCat.{u}) :
    FinitelyGeneratedModuleCat R ⥤ ModuleCat.{w} R :=
  ObjectProperty.ι (C := ModuleCat.{w} R) (fun M : ModuleCat.{w} R => Module.Finite R M)

/-- Inclusion of projective `R`-modules into all `R`-modules. -/
def projectiveInclusion (R : RingCat.{u}) : ProjectiveModuleCat R ⥤ ModuleCat.{w} R :=
  ObjectProperty.ι (C := ModuleCat.{w} R) (fun M : ModuleCat.{w} R => Module.Projective R M)

/-- Inclusion of injective `R`-modules into all `R`-modules. -/
def injectiveInclusion (R : RingCat.{u}) : InjectiveModuleCat R ⥤ ModuleCat.{w} R :=
  ObjectProperty.ι (C := ModuleCat.{w} R) (fun M : ModuleCat.{w} R => Module.Injective R M)

/-- Inclusion of simple `R`-modules into all `R`-modules. -/
def simpleInclusion (R : RingCat.{u}) : SimpleModuleCat R ⥤ ModuleCat.{w} R :=
  ObjectProperty.ι (C := ModuleCat.{w} R) (fun M : ModuleCat.{w} R => IsSimpleModule R M)

/-- Inclusion of torsion `R`-modules into all `R`-modules. -/
def torsionInclusion (R : RingCat.{u}) : TorsionModuleCat R ⥤ ModuleCat.{w} R :=
  ObjectProperty.ι (C := ModuleCat.{w} R) (fun M : ModuleCat.{w} R => Module.IsTorsion R M)

/-- Inclusion of torsion-free `R`-modules into all `R`-modules. -/
def torsionFreeInclusion (R : RingCat.{u}) :
    TorsionFreeModuleCat R ⥤ ModuleCat.{w} R :=
  ObjectProperty.ι (C := ModuleCat.{w} R)
    (fun M : ModuleCat.{w} R => Module.IsTorsionFree R M)

/-- Inclusion of finitely presented `R`-modules into all `R`-modules. -/
def finitelyPresentedInclusion (R : RingCat.{u}) :
    FinitelyPresentedModuleCat R ⥤ ModuleCat.{w} R :=
  ObjectProperty.ι (C := ModuleCat.{w} R)
    (fun M : ModuleCat.{w} R => Module.FinitePresentation R M)

/-- Inclusion of flat `R`-modules into all `R`-modules. -/
def flatInclusion (R : RingCat.{u}) : FlatModuleCat R ⥤ ModuleCat.{w} R :=
  ObjectProperty.ι (C := ModuleCat.{w} R)
    (fun M : ModuleCat.{w} R => Module.Flat R M)

/-- Inclusion of faithfully flat `R`-modules into all `R`-modules. -/
def faithfullyFlatInclusion (R : RingCat.{u}) :
    FaithfullyFlatModuleCat R ⥤ ModuleCat.{w} R :=
  ObjectProperty.ι (C := ModuleCat.{w} R)
    (fun M : ModuleCat.{w} R => Module.FaithfullyFlat R M)

/-- Inclusion of Noetherian `R`-modules into all `R`-modules. -/
def noetherianInclusion (R : RingCat.{u}) :
    NoetherianModuleCat R ⥤ ModuleCat.{w} R :=
  ObjectProperty.ι (C := ModuleCat.{w} R)
    (fun M : ModuleCat.{w} R => IsNoetherian R M)

/-- Inclusion of Artinian `R`-modules into all `R`-modules. -/
def artinianInclusion (R : RingCat.{u}) :
    ArtinianModuleCat R ⥤ ModuleCat.{w} R :=
  ObjectProperty.ι (C := ModuleCat.{w} R)
    (fun M : ModuleCat.{w} R => IsArtinian R M)

/-- Inclusion of semisimple `R`-modules into all `R`-modules. -/
def semisimpleInclusion (R : RingCat.{u}) :
    SemisimpleModuleCat R ⥤ ModuleCat.{w} R :=
  ObjectProperty.ι (C := ModuleCat.{w} R)
    (fun M : ModuleCat.{w} R => IsSemisimpleModule R M)

/-- Inclusion of faithful `R`-modules into all `R`-modules. -/
def faithfulInclusion (R : RingCat.{u}) : FaithfulModuleCat R ⥤ ModuleCat.{w} R :=
  ObjectProperty.ι (C := ModuleCat.{w} R)
    (fun M : ModuleCat.{w} R => FaithfulSMul R M)

/-- Finite free rank: free with a finite basis index. Not `Module.Finite`. -/
def IsFiniteRank (R : RingCat.{u}) (M : ModuleCat.{w} R) : Prop :=
  ∃ _ : Module.Free R M, Finite (Module.Free.ChooseBasisIndex R M)

abbrev FiniteRankModuleCat (R : RingCat.{u}) : Type (max u (w + 1)) :=
  ObjectProperty.FullSubcategory
    (C := ModuleCat.{w} R) (IsFiniteRank R)

/-- Free classifier on `Modules(R)`. -/
noncomputable def free (R : RingCat.{u}) : Classifier (ModulesOf R) where
  total := Cat.of (FreeModuleCat R)
  forget := (ObjectProperty.ι
    (C := ModuleCat.{w} R) (fun M : ModuleCat.{w} R => Module.Free R M)).toCatHom

/-- Finitely-generated classifier (`Module.Finite`). Not finite rank. -/
noncomputable def finitelyGenerated (R : RingCat.{u}) : Classifier (ModulesOf R) where
  total := Cat.of (FinitelyGeneratedModuleCat R)
  forget := (ObjectProperty.ι
    (C := ModuleCat.{w} R) (fun M : ModuleCat.{w} R => Module.Finite R M)).toCatHom

/-- Finite free rank classifier. -/
noncomputable def finiteRank (R : RingCat.{u}) : Classifier (ModulesOf R) where
  total := Cat.of (FiniteRankModuleCat R)
  forget := (ObjectProperty.ι (C := ModuleCat.{w} R) (IsFiniteRank R)).toCatHom

noncomputable def FreeModules (R : RingCat.{u}) :
    ObjCat.{max u (w + 1), w} := (free R).total

noncomputable def FinitelyGeneratedModules (R : RingCat.{u}) :
    ObjCat.{max u (w + 1), w} :=
  (finitelyGenerated R).total

noncomputable def FiniteRankModules (R : RingCat.{u}) :
    ObjCat.{max u (w + 1), w} :=
  (finiteRank R).total

/-- Forgetful `Modules(R) → Sets`. -/
noncomputable def modulesToSets (R : RingCat.{u}) : ModulesOf R ⟶ Sets.{u} :=
  (forget (ModuleCat.{u} R)).toCatHom

/-! ### Change of rings -/

section ChangeOfRings

variable {R S : Type*} [Ring R] [Ring S]

/-- Restriction of scalars along a ring homomorphism, via Mathlib's canonical functor. -/
noncomputable abbrev restrictScalars (f : R →+* S) :
    ModuleCat S ⥤ ModuleCat R :=
  ModuleCat.restrictScalars f

/-- Coextension of scalars, the right adjoint to restriction of scalars. -/
noncomputable abbrev coextendScalars (f : R →+* S) :
    ModuleCat R ⥤ ModuleCat S :=
  ModuleCat.coextendScalars f

/-- Restriction of scalars is left adjoint to coextension of scalars. -/
noncomputable abbrev restrictCoextendScalarsAdj (f : R →+* S) :
    restrictScalars f ⊣ coextendScalars f :=
  ModuleCat.restrictCoextendScalarsAdj f

end ChangeOfRings

section CommutativeChangeOfRings

variable {R S : Type*} [CommRing R] [CommRing S]

/-- Extension of scalars along a commutative-ring homomorphism, via tensor product. -/
noncomputable abbrev extendScalars (f : R →+* S) :
    ModuleCat R ⥤ ModuleCat S :=
  ModuleCat.extendScalars f

/-- Extension of scalars is left adjoint to restriction of scalars. -/
noncomputable abbrev extendRestrictScalarsAdj (f : R →+* S) :
    extendScalars f ⊣ restrictScalars f :=
  ModuleCat.extendRestrictScalarsAdj f

end CommutativeChangeOfRings

/-- Opposite-ring substitution for right-module family expressions. -/
noncomputable def oppositeRing (R : RingCat.{u}) : RingCat.{u} := RingCat.of Rᵐᵒᵖ

/-- Right `R`-modules, represented as left modules over the opposite ring. -/
noncomputable def RightModulesOf (R : RingCat.{u}) :
    ObjCat.{max u (w + 1), w} :=
  modulesFamilyValue (oppositeRing R)

example (R : RingCat.{u}) : RightModulesOf R = ModulesOf (oppositeRing R) := rfl

end LeanCategories.Modules.Mathlib
