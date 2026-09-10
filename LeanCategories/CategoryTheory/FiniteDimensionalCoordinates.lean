/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Category.FGModuleCat.Basic
public import Mathlib.CategoryTheory.Preadditive.Mat
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.StdBasis

@[expose] public noncomputable section

open _root_.CategoryTheory
open scoped Matrix

namespace LeanCategories.CategoryTheory

universe u

variable (k : Type u) [Field k]

/-- A finite-dimensional vector space over `k` equipped with a chosen finite basis.

This is Riehl's intermediate category `Vect_k^basis` in FC03-C01-U060.  Morphisms do not
have to preserve the chosen bases: they are arbitrary linear maps. -/
structure BasedFDVect where
  /-- The underlying finite-dimensional vector space. -/
  obj : FGModuleCat.{u} k
  /-- The finite indexing type of the chosen basis. -/
  ι : Type u
  [fintype : Fintype ι]
  /-- The chosen basis. -/
  basis : Module.Basis ι k obj

attribute [instance] BasedFDVect.fintype

namespace BasedFDVect

instance : _root_.CategoryTheory.Category (BasedFDVect k) where
  Hom X Y := X.obj ⟶ Y.obj
  id X := 𝟙 X.obj
  comp f g := f ≫ g
  id_comp := by intros; simp
  comp_id := by intros; simp
  assoc := by intros; simp

/-- Forget the chosen basis.  This is Riehl's `Vect_k^basis → Vect_k^fd`. -/
def forget : BasedFDVect k ⥤ FGModuleCat.{u} k where
  obj X := X.obj
  map f := f
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Choose Mathlib's canonical classical basis on each finite-dimensional vector space.
This is a quasi-inverse to `forget`. -/
def chooseBasis : FGModuleCat.{u} k ⥤ BasedFDVect k where
  obj V :=
    { obj := V
      ι := Module.Basis.ofVectorSpaceIndex k V
      basis := Module.Basis.ofVectorSpace k V }
  map f := f
  map_id _ := rfl
  map_comp _ _ := rfl

/-- An isomorphism of underlying finitely generated modules induces an isomorphism of based
spaces.  Morphisms in `BasedFDVect` are arbitrary linear maps, so no basis-preservation
condition is imposed. -/
def isoOfUnderlyingIso {X Y : BasedFDVect k} (e : X.obj ≅ Y.obj) : X ≅ Y where
  hom := e.hom
  inv := e.inv
  hom_inv_id := e.hom_inv_id
  inv_hom_id := e.inv_hom_id

/-- The identity is naturally isomorphic to forgetting and then choosing a basis.  Only the
basis datum changes. -/
def unitIso : 𝟭 (BasedFDVect k) ≅ forget k ⋙ chooseBasis k :=
  NatIso.ofComponents (fun X => isoOfUnderlyingIso k (Iso.refl X.obj)) (by
    intro X Y f
    change f ≫ 𝟙 Y.obj = 𝟙 X.obj ≫ f
    apply FGModuleCat.hom_ext
    change f.hom.hom = f.hom.hom
    rfl)

/-- Choosing a basis and then forgetting it is naturally isomorphic to the identity. -/
def counitIso : chooseBasis k ⋙ forget k ≅ 𝟭 (FGModuleCat.{u} k) :=
  NatIso.ofComponents (fun X => Iso.refl X) (by
    intro X Y f
    change f ≫ 𝟙 Y = 𝟙 X ≫ f
    simp)

/-- The explicit equivalence between based and unbased finite-dimensional vector spaces.
The inverse is the chosen-basis functor above. -/
def equivalenceForget : BasedFDVect k ≌ FGModuleCat.{u} k where
  functor := forget k
  inverse := chooseBasis k
  unitIso := unitIso k
  counitIso := counitIso k

local instance (I : _root_.CategoryTheory.Mat k) : Fintype I :=
  FintypeCat.fintype

local instance (I : _root_.CategoryTheory.Mat k) : DecidableEq I :=
  Classical.decEq I

/-- The standard based vector space attached to a finite indexing type. -/
def standard (I : _root_.CategoryTheory.Mat k) : BasedFDVect k where
  obj := FGModuleCat.of k (I → k)
  ι := I
  basis := Pi.basisFun k I

/-- A matrix acts on row vectors by right multiplication, giving a linear map between the
corresponding standard based vector spaces.  This orientation matches `Mat k` composition. -/
def matrixToBased : _root_.CategoryTheory.Mat k ⥤ BasedFDVect k where
  obj I := standard k I
  map {I J} A := FGModuleCat.ofHom A.toLinearMapRight'
  map_id I := by
    apply FGModuleCat.hom_ext
    change (1 : Matrix I I k).toLinearMapRight' = LinearMap.id
    exact Matrix.toLinearMapRight'_one
  map_comp {I J K} A B := by
    apply FGModuleCat.hom_ext
    change
      ((show Matrix I J k from A) * (show Matrix J K k from B)).toLinearMapRight' =
        (show Matrix J K k from B).toLinearMapRight'.comp
          (show Matrix I J k from A).toLinearMapRight'
    exact Matrix.toLinearMapRight'_mul (show Matrix I J k from A) (show Matrix J K k from B)

local instance (X : BasedFDVect k) : DecidableEq X.ι :=
  Classical.decEq X.ι

/-- Coordinate matrix of a linear map between based finite-dimensional vector spaces.
We transpose Mathlib's column-vector `LinearMap.toMatrix` convention so that the result uses
Riehl/`Mat k` row-vector composition. -/
def coordinates : BasedFDVect k ⥤ _root_.CategoryTheory.Mat k where
  obj X := (show _root_.CategoryTheory.Mat k from _root_.FintypeCat.of X.ι)
  map {X Y} f :=
    (LinearMap.toMatrix X.basis Y.basis f.hom.hom)ᵀ
  map_id X := by
    ext i j
    change (LinearMap.toMatrix X.basis X.basis LinearMap.id) j i =
      (1 : Matrix X.ι X.ι k) i j
    classical
    by_cases h : i = j
    · subst j
      simp [LinearMap.toMatrix_apply]
    · simp [LinearMap.toMatrix_apply, h]
  map_comp {X Y Z} f g := by
    rw [show (f ≫ g).hom.hom = g.hom.hom.comp f.hom.hom from rfl]
    rw [_root_.CategoryTheory.Mat.comp_def]
    ext i j
    simp only [Matrix.transpose_apply]
    rw [LinearMap.toMatrix_comp X.basis Y.basis Z.basis]
    rw [Matrix.mul_apply]
    have huniv :
        (@Finset.univ Y.ι Y.fintype) =
          (@Finset.univ Y.ι (@FintypeCat.fintype (FintypeCat.of Y.ι))) := by
      ext y
      simp
    rw [huniv]
    apply Finset.sum_congr rfl
    intro y hy
    exact mul_comm _ _

end BasedFDVect

end LeanCategories.CategoryTheory
