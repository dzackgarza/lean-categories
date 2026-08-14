/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Algebra.Ideals
public import LeanCategories.CategoryTheory.StandardConstructions
public import Mathlib.Algebra.Category.ModuleCat.Pseudofunctor
public import Mathlib.Algebra.Category.Ring.Under.Basic
public import Mathlib.CategoryTheory.FiberedCategory.Cocartesian
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-!
# Algebraic families over commutative rings

This module exposes the standard Grothendieck constructions for the basic algebraic
families used by the CAS surface.

The module family is Mathlib's extension-of-scalars pseudofunctor.  The ideal family
uses ideal extension.  Prime ideals use contraction, since contraction preserves
primality while extension does not do so for an arbitrary ring homomorphism.
Commutative algebra base change uses Mathlib's tensor-product functor on `Under`.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Functor
open CategoryTheory.Pseudofunctor
open Opposite

namespace LeanCategories.AlgebraicFamilies

universe u

/-! ## Commutative algebras -/

/** The total category of commutative algebra arrows over varying bases. */
abbrev CommAlgTotal := CategoryTheory.Arrow CommRingCat.{u}

/** The projection from commutative algebra arrows to their coefficient rings. */
abbrev commAlgProjection : CommAlgTotal.{u} ⥤ CommRingCat.{u} :=
  CategoryTheory.Arrow.leftFunc

/-! ## Ideals -/

/** The strict fiber functor of all ideals under ideal extension. */
def idealFamilyFunctor : CommRingCat.{u} ⥤ Cat.{u, u + 1} where
  obj R := Cat.of (LeanCategories.Algebra.Ideals R)
  map f := (LeanCategories.Algebra.idealMapFunctor f.hom).toCatHom
  map_id R := by
    ext I
    simp
  map_comp f g := by
    ext I
    simp [LeanCategories.Algebra.idealMapFunctor,
      LeanCategories.Algebra.idealMapOrderHom]

/** The pseudofunctor of all ideals under ideal extension. */
abbrev idealFamily : LocallyDiscrete CommRingCat.{u} ⥤ᵖ Cat.{u, u + 1} :=
  idealFamilyFunctor.toPseudofunctor'

/** The total category of ideals over commutative rings. */
abbrev IdealTotal := ∫ idealFamily

/** The projection from the total ideal category to commutative rings. */
abbrev idealProjection : IdealTotal.{u} ⥤ CommRingCat.{u} :=
  Pseudofunctor.Grothendieck.forget idealFamily

/** The fixed-base ideal fiber. */
abbrev idealFiber (R : CommRingCat.{u}) := LeanCategories.Algebra.Ideals R

/** The canonical inclusion of an ideal fiber into the total category. */
abbrev idealFiberInclusion (R : CommRingCat.{u}) :
    idealFiber R ⥤ IdealTotal :=
  Pseudofunctor.Grothendieck.ι idealFamily R

/** Base change of ideals along a commutative-ring morphism. */
abbrev idealBaseChange {R S : CommRingCat.{u}} (f : R ⟶ S) :
    idealFiber R ⥤ idealFiber S :=
  LeanCategories.Algebra.idealMapFunctor f.hom

/-! ## Modules -/

/** The standard module extension pseudofunctor from Mathlib. */
abbrev moduleFamily : LocallyDiscrete CommRingCat.{u} ⥤ᵖ Cat.{u, u + 1} :=
  CommRingCat.moduleCatExtendScalarsPseudofunctor

/** The total category of modules over varying commutative rings. */
abbrev ModuleTotal := ∫ moduleFamily

/** The projection from the total module category to commutative rings. */
abbrev moduleProjection : ModuleTotal.{u} ⥤ CommRingCat.{u} :=
  Pseudofunctor.Grothendieck.forget moduleFamily

/** The fixed-base module fiber. */
abbrev moduleFiber (R : CommRingCat.{u}) := ModuleCat.{u} R

/** The canonical inclusion of a module fiber into the total category. */
abbrev moduleFiberInclusion (R : CommRingCat.{u}) :
    moduleFiber R ⥤ ModuleTotal :=
  Pseudofunctor.Grothendieck.ι moduleFamily R

/** Scalar extension of modules along a commutative-ring morphism. */
abbrev moduleBaseChange {R S : CommRingCat.{u}} (f : R ⟶ S) :
    moduleFiber R ⥤ moduleFiber S :=
  ModuleCat.extendScalars f.hom

/-! ## Prime ideals -/

/** Contraction of prime ideals along a commutative-ring morphism. */
def primeIdealComapFunctor {R S : CommRingCat.{u}} (f : R ⟶ S) :
    LeanCategories.Algebra.PrimeIdealCat S ⥤ LeanCategories.Algebra.PrimeIdealCat R :=
  ObjectProperty.lift _ (LeanCategories.Algebra.idealComapFunctor f.hom) fun I =>
    Ideal.IsPrime.comap f.hom I.1

/** The strict contravariant fiber functor of prime ideals. */
def primeIdealFamilyFunctor : CommRingCat.{u}ᵒᵖ ⥤ Cat.{u, u + 1} where
  obj R := Cat.of (LeanCategories.Algebra.PrimeIdealCat R.unop)
  map f := (primeIdealComapFunctor f.unop).toCatHom
  map_id R := by
    ext I
    rfl
  map_comp f g := by
    ext I
    simp [primeIdealComapFunctor, LeanCategories.Algebra.idealComapFunctor,
      LeanCategories.Algebra.idealComapOrderHom]

/** The prime-ideal pseudofunctor under contraction. */
abbrev primeIdealFamily :
    LocallyDiscrete CommRingCat.{u}ᵒᵖ ⥤ᵖ Cat.{u, u + 1} :=
  primeIdealFamilyFunctor.toPseudofunctor'

/** The total category of prime ideals over commutative rings. */
abbrev PrimeIdealTotal := ∫ᶜ primeIdealFamily

/** The projection from the prime-ideal total category to commutative rings. */
abbrev primeIdealProjection : PrimeIdealTotal.{u} ⥤ CommRingCat.{u} :=
  Pseudofunctor.CoGrothendieck.forget primeIdealFamily

/** The fixed-base prime-ideal fiber. */
abbrev primeIdealFiber (R : CommRingCat.{u}) :=
  LeanCategories.Algebra.PrimeIdealCat R

/** The canonical inclusion of a prime-ideal fiber into the total category. */
abbrev primeIdealFiberInclusion (R : CommRingCat.{u}) :
    primeIdealFiber R ⥤ PrimeIdealTotal :=
  Pseudofunctor.CoGrothendieck.ι primeIdealFamily R

/** Contraction of prime ideals along a commutative-ring morphism. */
abbrev primeIdealBaseChange {R S : CommRingCat.{u}} (f : R ⟶ S) :
    primeIdealFiber S ⥤ primeIdealFiber R :=
  primeIdealComapFunctor f

/** The canonical CoGrothendieck morphism for prime-ideal contraction. */
def primeIdealBaseChangeHom (X : PrimeIdealTotal.{u})
    {R : CommRingCat.{u}} (f : R ⟶ X.base) :
    ⟨R, (primeIdealFamily.map f.op.toLoc).toFunctor.obj X.fiber⟩ ⟶ X :=
  { base := f, fiber := 𝟙 _ }

instance primeIdealBaseChangeHom_isStronglyCartesian (X : PrimeIdealTotal.{u})
    {R : CommRingCat.{u}} (f : R ⟶ X.base) :
    IsStronglyCartesian primeIdealProjection f (primeIdealBaseChangeHom X f) := by
  change IsStronglyCartesian primeIdealProjection f
    (Pseudofunctor.CoGrothendieck.cartesianLift X.fiber f)
  infer_instance

/** The category of commutative algebras over a fixed commutative ring. */
abbrev commAlgFiber (R : CommRingCat.{u}) := CommRingCat.Under R

/** Include a fixed-base algebra fiber into the total arrow category. */
def commAlgFiberInclusion (R : CommRingCat.{u}) :
    commAlgFiber R ⥤ CommAlgTotal :=
  { obj A := CategoryTheory.Arrow.mk A.hom
    map f := CategoryTheory.Arrow.homMk (𝟙 R) f.right }

/** The standard tensor-product base-change functor for commutative algebras. */
abbrev commAlgBaseChange {R S : CommRingCat.{u}} (f : R ⟶ S) :
    commAlgFiber R ⥤ commAlgFiber S :=
  CommRingCat.tensorProd R S

/** The total-category object obtained by extending a commutative algebra. */
abbrev commAlgBaseChangeObject {R S : CommRingCat.{u}}
    (A : commAlgFiber R) (f : R ⟶ S) : CommAlgTotal :=
  CategoryTheory.Arrow.mk (commAlgBaseChange f |>.obj A).hom

/** The canonical base-change square for a commutative algebra arrow. */
def commAlgBaseChangeHom {R S : CommRingCat.{u}}
    (A : commAlgFiber R) (f : R ⟶ S) :
    CategoryTheory.Arrow.mk A.hom ⟶ commAlgBaseChangeObject A f :=
  CategoryTheory.Arrow.homMk' f
    (CommRingCat.ofHom Algebra.TensorProduct.includeRight) (by
      apply CommRingCat.hom_ext
      ext x
      simp [CommRingCat.comp_apply])

/** The underlying algebra object of a commutative-algebra fiber object. */
abbrev commAlgCarrier {R : CommRingCat.{u}} (A : commAlgFiber R) : Type u := A.right

/-! ## Base-change morphisms for covariant pseudofamilies -/

/** The canonical Grothendieck morphism to transport along a base map. */
def covariantFamilyBaseChangeHom
    (F : LocallyDiscrete CommRingCat.{u} ⥤ᵖ Cat.{u, u + 1})
    (X : ∫ F) {S : CommRingCat.{u}} (f : X.base ⟶ S) :
    X ⟶ ⟨S, (F.map f.toLoc).toFunctor.obj X.fiber⟩ :=
  { base := f, fiber := 𝟙 _ }

abbrev idealBaseChangeHom (X : IdealTotal.{u})
    {S : CommRingCat.{u}} (f : X.base ⟶ S) :
    X ⟶ ⟨S, (idealFamily.map f.toLoc).toFunctor.obj X.fiber⟩ :=
  covariantFamilyBaseChangeHom idealFamily X f

abbrev moduleBaseChangeHom (X : ModuleTotal.{u})
    {S : CommRingCat.{u}} (f : X.base ⟶ S) :
    X ⟶ ⟨S, (moduleFamily.map f.toLoc).toFunctor.obj X.fiber⟩ :=
  covariantFamilyBaseChangeHom moduleFamily X f

end LeanCategories.AlgebraicFamilies
