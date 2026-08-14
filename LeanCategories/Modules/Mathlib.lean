/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Category.ModuleCat.Pseudofunctor
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.Algebra.Module.Projective
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.Algebra.Module.Torsion.Free
public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.RingTheory.Finiteness.Basic
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

/-- Opposite-ring substitution for right-module family expressions. -/
noncomputable def oppositeRing (R : RingCat.{u}) : RingCat.{u} := RingCat.of Rᵐᵒᵖ

/-- Right `R`-modules, represented as left modules over the opposite ring. -/
noncomputable def RightModulesOf (R : RingCat.{u}) :
    ObjCat.{max u (w + 1), w} :=
  modulesFamilyValue (oppositeRing R)

example (R : RingCat.{u}) : RightModulesOf R = ModulesOf (oppositeRing R) := rfl

end LeanCategories.Modules.Mathlib
