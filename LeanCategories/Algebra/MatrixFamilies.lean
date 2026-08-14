/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.CategoryTheory.Discrete.Basic
public import Mathlib.CategoryTheory.Elements
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.Algebra.Polynomial.Derivative

@[expose] public section

open CategoryTheory

namespace LeanCategories.Algebra

universe u w

/-! ## Coefficient families -/

/-- The covariant family of underlying commutative rings. -/
abbrev commRingFamily : CommRingCat.{u} ⥤ Type u :=
  CategoryTheory.forget CommRingCat

/-- The covariant family of polynomial-ring elements.

The category-valued polynomial family is `LeanCategories.Algebra.polynomialFamily` in
`PolynomialPowerSeries`; this value-valued family is kept separate so both routes can
be exported together. -/
noncomputable def polynomialValueFamily : CommRingCat.{u} ⥤ Type u where
  obj R := Polynomial R
  map f := ↾fun p => Polynomial.map f.hom p
  map_id R := by
    apply ConcreteCategory.hom_ext
    intro p
    ext n
    simp
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro p
    ext n
    simp

/-! ## Matrix and vector families -/

/-- The covariant family of matrices with fixed finite row and column types. -/
def matrixFamily (ι κ : Type u) [Fintype ι] [Fintype κ] :
    CommRingCat.{u} ⥤ Type u where
  obj R := Matrix ι κ R
  map f := ↾fun A => Matrix.map A f.hom
  map_id R := by
    apply ConcreteCategory.hom_ext
    intro A
    ext i j
    simp
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro A
    ext i j
    simp

/-- The covariant family of vectors with a fixed finite index type. -/
def vectorFamily (ι : Type u) [Fintype ι] : CommRingCat.{u} ⥤ Type u where
  obj R := ι → R
  map f := ↾fun x i => f.hom (x i)
  map_id R := by
    apply ConcreteCategory.hom_ext
    intro x
    funext i
    exact CommRingCat.id_apply R (x i)
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro x
    funext i
    exact CommRingCat.comp_apply f g (x i)

/-- The covariant family of invertible square matrices. -/
def generalLinearFamily (ι : Type u) [Fintype ι] [DecidableEq ι] :
    CommRingCat.{u} ⥤ Type u where
  obj R := Matrix.GeneralLinearGroup ι R
  map f := ↾fun g => Matrix.GeneralLinearGroup.map f.hom g
  map_id R := by
    apply ConcreteCategory.hom_ext
    intro g
    ext i j
    simp
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro g
    ext i j
    simp

/-! ## Total categories and projections -/

abbrev MatrixFamilyCat (ι κ : Type u) [Fintype ι] [Fintype κ] :=
  (matrixFamily ι κ).Elements

abbrev VectorFamilyCat (ι : Type u) [Fintype ι] :=
  (vectorFamily ι).Elements

abbrev GeneralLinearFamilyCat (ι : Type u) [Fintype ι] [DecidableEq ι] :=
  (generalLinearFamily ι).Elements

/-- Projection of the total matrix category to its coefficient ring. -/
abbrev matrixProjection (ι κ : Type u) [Fintype ι] [Fintype κ] :
    MatrixFamilyCat ι κ ⥤ CommRingCat :=
  CategoryOfElements.π (matrixFamily ι κ)

/-- Projection of the total vector category to its coefficient ring. -/
abbrev vectorProjection (ι : Type u) [Fintype ι] :
    VectorFamilyCat ι ⥤ CommRingCat :=
  CategoryOfElements.π (vectorFamily ι)

/-- Projection of the total general-linear category to its coefficient ring. -/
abbrev generalLinearProjection (ι : Type u) [Fintype ι] [DecidableEq ι] :
    GeneralLinearFamilyCat ι ⥤ CommRingCat :=
  CategoryOfElements.π (generalLinearFamily ι)

/-! ## Fibers and base change -/

/-- The fixed-ring fiber of a type-valued family. -/
abbrev familyFiber (F : CommRingCat.{u} ⥤ Type w) (R : CommRingCat) :=
  Discrete (F.obj R)

/-- Include a fixed-ring fiber into the total category. -/
def familyFiberInclusion (F : CommRingCat.{u} ⥤ Type w) (R : CommRingCat) :
    familyFiber F R ⥤ F.Elements where
  obj X := ⟨R, X.as⟩
  map {X Y} f := ⟨𝟙 R, by
    rw [F.map_id]
    exact Discrete.eq_of_hom f⟩
  map_id := by
    intro X
    apply CategoryOfElements.ext
    rfl
  map_comp := by
    intro X Y Z f g
    apply CategoryOfElements.ext
    rfl

/-- Base change of a fixed-ring fiber along a commutative-ring morphism. -/
def familyFiberBaseChange {R S : CommRingCat} (f : R ⟶ S)
    (F : CommRingCat.{u} ⥤ Type w) : familyFiber F R ⥤ familyFiber F S where
  obj X := ⟨F.map f X.as⟩
  map {X Y} g := Discrete.eqToHom'
    (congrArg (F.map f) (Discrete.eq_of_hom g))
  map_id := by
    intro X
    apply Subsingleton.elim
  map_comp := by
    intro X Y Z f g
    apply Subsingleton.elim

/-- The canonical morphism from a family element to its transport along a base map. -/
def familyBaseChangeHom (F : CommRingCat.{u} ⥤ Type w) (X : F.Elements)
    {S : CommRingCat} (f : X.1 ⟶ S) : X ⟶ ⟨S, F.map f X.2⟩ :=
  CategoryOfElements.homMk _ _ f rfl

abbrev matrixFiber (R : CommRingCat) (ι κ : Type u) [Fintype ι] [Fintype κ] :=
  familyFiber (matrixFamily ι κ) R

abbrev vectorFiber (R : CommRingCat) (ι : Type u) [Fintype ι] :=
  familyFiber (vectorFamily ι) R

abbrev generalLinearFiber (R : CommRingCat) (ι : Type u)
    [Fintype ι] [DecidableEq ι] :=
  familyFiber (generalLinearFamily ι) R

abbrev matrixFiberInclusion (R : CommRingCat) (ι κ : Type u)
    [Fintype ι] [Fintype κ] : matrixFiber R ι κ ⥤ MatrixFamilyCat ι κ :=
  familyFiberInclusion (matrixFamily ι κ) R

abbrev vectorFiberInclusion (R : CommRingCat) (ι : Type u) [Fintype ι] :
    vectorFiber R ι ⥤ VectorFamilyCat ι :=
  familyFiberInclusion (vectorFamily ι) R

abbrev generalLinearFiberInclusion (R : CommRingCat) (ι : Type u)
    [Fintype ι] [DecidableEq ι] :
    generalLinearFiber R ι ⥤ GeneralLinearFamilyCat ι :=
  familyFiberInclusion (generalLinearFamily ι) R

abbrev matrixBaseChange {R S : CommRingCat} (f : R ⟶ S) (ι κ : Type u)
    [Fintype ι] [Fintype κ] : matrixFiber R ι κ ⥤ matrixFiber S ι κ :=
  familyFiberBaseChange f (matrixFamily ι κ)

abbrev vectorBaseChange {R S : CommRingCat} (f : R ⟶ S) (ι : Type u)
    [Fintype ι] : vectorFiber R ι ⥤ vectorFiber S ι :=
  familyFiberBaseChange f (vectorFamily ι)

abbrev generalLinearBaseChange {R S : CommRingCat} (f : R ⟶ S) (ι : Type u)
    [Fintype ι] [DecidableEq ι] :
    generalLinearFiber R ι ⥤ generalLinearFiber S ι :=
  familyFiberBaseChange f (generalLinearFamily ι)

/-- The canonical matrix-family base-change morphism. -/
abbrev matrixBaseChangeHom (X : MatrixFamilyCat ι κ)
    {S : CommRingCat} (f : X.1 ⟶ S) : X ⟶ ⟨S, matrixFamily ι κ |>.map f X.2⟩ :=
  familyBaseChangeHom (matrixFamily ι κ) X f

/-- The canonical vector-family base-change morphism. -/
abbrev vectorBaseChangeHom (X : VectorFamilyCat ι)
    {S : CommRingCat} (f : X.1 ⟶ S) : X ⟶ ⟨S, vectorFamily ι |>.map f X.2⟩ :=
  familyBaseChangeHom (vectorFamily ι) X f

/-- The canonical general-linear base-change morphism. -/
abbrev generalLinearBaseChangeHom (X : GeneralLinearFamilyCat ι)
    {S : CommRingCat} (f : X.1 ⟶ S) :
    X ⟶ ⟨S, generalLinearFamily ι |>.map f X.2⟩ :=
  familyBaseChangeHom (generalLinearFamily ι) X f

/-! ## The general-linear subfamily -/

/-- The inclusion of invertible matrices into all square matrices. -/
noncomputable def generalLinearToMatrixNatTrans (ι : Type u) [Fintype ι] [DecidableEq ι] :
    generalLinearFamily ι ⟶ matrixFamily ι ι :=
  { app := fun R =>
      letI := R.commRing
      ↾(fun g : Matrix.GeneralLinearGroup ι (R : Type u) =>
        (g : Matrix ι ι (R : Type u)))
    naturality := by
      intro R S f
      apply ConcreteCategory.hom_ext
      intro g
      rfl }

/-- The functor including the general-linear total category into the matrix total category. -/
noncomputable abbrev generalLinearToMatrix (ι : Type u) [Fintype ι] [DecidableEq ι] :
    GeneralLinearFamilyCat ι ⥤ MatrixFamilyCat ι ι :=
  NatTrans.mapElements (generalLinearToMatrixNatTrans ι)

/-! ## Canonical matrix invariants -/

/-- Determinant as a natural transformation of matrix and coefficient families. -/
noncomputable def determinantNatTrans (ι : Type u) [Fintype ι] [DecidableEq ι] :
    matrixFamily ι ι ⟶ commRingFamily :=
  { app := fun R =>
      letI := R.commRing
      ↾(fun A : Matrix ι ι (R : Type u) => Matrix.det A)
    naturality := by
      intro R S f
      apply ConcreteCategory.hom_ext
      intro A
      exact (RingHom.map_det f.hom A).symm }

/-- Trace as a natural transformation of matrix and coefficient families. -/
noncomputable def traceNatTrans (ι : Type u) [Fintype ι] :
    matrixFamily ι ι ⟶ commRingFamily :=
  { app := fun R =>
      letI := R.commRing
      ↾(fun A : Matrix ι ι (R : Type u) => Matrix.trace A)
    naturality := by
      intro R S f
      apply ConcreteCategory.hom_ext
      intro A
      exact (AddMonoidHom.map_trace f.hom A).symm }

/-- Characteristic polynomial as a natural transformation of matrix families. -/
noncomputable def characteristicPolynomialNatTrans (ι : Type u) [Fintype ι] [DecidableEq ι] :
    matrixFamily ι ι ⟶ polynomialValueFamily :=
  { app := fun R =>
      letI := R.commRing
      ↾(fun A : Matrix ι ι (R : Type u) => Matrix.charpoly A)
    naturality := by
      intro R S f
      apply ConcreteCategory.hom_ext
      intro A
      exact Matrix.charpoly_map A f.hom }

/-- Formal derivative as a natural transformation of polynomial families. -/
noncomputable def derivativeNatTrans : polynomialValueFamily ⟶ polynomialValueFamily :=
  { app := fun R =>
      letI := R.commRing
      ↾(fun p : Polynomial (R : Type u) => Polynomial.derivative p)
    naturality := by
      intro R S f
      apply ConcreteCategory.hom_ext
      intro p
      exact Polynomial.derivative_map p f.hom }

/-- The determinant functor between total element categories. -/
noncomputable abbrev determinantFunctor (ι : Type u) [Fintype ι] [DecidableEq ι] :
    MatrixFamilyCat ι ι ⥤ (commRingFamily).Elements :=
  NatTrans.mapElements (determinantNatTrans ι)

/-- The trace functor between total element categories. -/
noncomputable abbrev traceFunctor (ι : Type u) [Fintype ι] :
    MatrixFamilyCat ι ι ⥤ (commRingFamily).Elements :=
  NatTrans.mapElements (traceNatTrans ι)

/-- The characteristic-polynomial functor between total element categories. -/
noncomputable abbrev characteristicPolynomialFunctor (ι : Type u) [Fintype ι] [DecidableEq ι] :
    MatrixFamilyCat ι ι ⥤ (polynomialValueFamily).Elements :=
  NatTrans.mapElements (characteristicPolynomialNatTrans ι)

/-- The derivative functor between total polynomial element categories. -/
noncomputable abbrev derivativeFunctor :
    (polynomialValueFamily).Elements ⥤ (polynomialValueFamily).Elements :=
  NatTrans.mapElements (derivativeNatTrans)

end LeanCategories.Algebra
