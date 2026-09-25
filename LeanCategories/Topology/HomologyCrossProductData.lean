/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Topology.SingularCrossProduct
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Category.ModuleCat.Products
public import Mathlib.AlgebraicTopology.SingularHomology.Basic
public import Mathlib.Data.Finsupp.ToDFinsupp
public import Mathlib.LinearAlgebra.Finsupp.LSum

/-!
# Singular-homology cross-product data

Definition-level realization of Hatcher FC07-C03-U081.

The later source unit FC07-C03-U089 already records Hatcher's signed shuffle
formula on raw singular chains. Mathlib's singular-chain complex uses the
categorical coproduct of one coefficient module per singular simplex.
For ModuleCat that coproduct is canonically the direct sum, constant-family
DirectSum is canonically Finsupp, and TopCat.toSSetObjEquiv identifies the
singular-set simplex index with the same Euclidean standard-simplex maps used
by U089.

This file records those canonical carrier identifications and specifies the
homology cross product by its representative-level graph. It does not prove
the signed boundary identity, that the raw product of cycles is a cycle,
naturality, or representative independence. Those are result-layer content.
-/

@[expose] public noncomputable section

namespace LeanCategories.Topology

open AlgebraicTopology CategoryTheory CategoryTheory.Limits MonoidalCategory

/-- Singular n-simplices in Mathlib's singular-set model. -/
abbrev NativeSingularSimplexData (X : TopCat.{0}) (n : ℕ) : Type :=
  (TopCat.toSSet.obj X).obj (Opposite.op (SimplexCategory.mk n))

/-- Mathlib's singular chain complex with coefficients in R. -/
abbrev nativeSingularChainComplexData
    (R : Type) [CommRing R] (X : TopCat.{0}) :
    ChainComplex (ModuleCat.{0} R) ℕ :=
  ((singularChainComplexFunctor (ModuleCat.{0} R)).obj
    (ModuleCat.of R R)).obj X

/-- The degree-n native singular-chain module is the direct sum of one copy of
R for every native singular simplex. -/
noncomputable def nativeSingularChainIsoDirectSumData
    (R : Type) [CommRing R] (X : TopCat.{0}) (n : ℕ) :
    (nativeSingularChainComplexData R X).X n ≅
      ModuleCat.of R (⨁ _ : NativeSingularSimplexData X n, R) :=
  letI := Classical.decEq (NativeSingularSimplexData X n)
  ModuleCat.coprodIsoDirectSum
    (fun _ : NativeSingularSimplexData X n => ModuleCat.of R R)

/-- Canonical linear equivalence from Mathlib's native degree-n singular
chains to the Finsupp carrier used by FC07-C03-U089. -/
noncomputable def nativeSingularChainEquivRawData
    (R : Type) [CommRing R] (X : TopCat.{0}) (n : ℕ) :
    (nativeSingularChainComplexData R X).X n ≃ₗ[R]
      RawSingularChain R X n :=
  letI := Classical.decEq (NativeSingularSimplexData X n)
  (nativeSingularChainIsoDirectSumData R X n).toLinearEquiv |>.trans
    (finsuppLequivDFinsupp R).symm |>.trans
    (Finsupp.domLCongr
      (TopCat.toSSetObjEquiv X (Opposite.op (SimplexCategory.mk n))))

/-- Singular homology as the homology object of the native singular-chain
complex. -/
abbrev singularHomologyModuleData
    (R : Type) [CommRing R] (X : TopCat.{0}) (n : ℕ) : ModuleCat.{0} R :=
  (nativeSingularChainComplexData R X).homology n

/-- Type of a degree-(i,j) homology cross-product candidate. -/
abbrev SingularHomologyCrossProductHomData
    (R : Type) [CommRing R] (X Y : TopCat.{0}) (i j : ℕ) :=
  singularHomologyModuleData R X i ⊗ singularHomologyModuleData R Y j ⟶
    singularHomologyModuleData R (X ⨯ Y) (i + j)

/-- Representative-level specification saying that a homology pairing is
induced by Hatcher's signed shuffle product on singular chains.

For cycle representatives x and y, the raw shuffle product must be represented
by some cycle z in the product space, and the candidate homology map sends the
classes of x and y to the class of z. Existence of z is deliberately not
proved here. -/
def IsSingularHomologyCrossProductData
    (R : Type) [CommRing R] (X Y : TopCat.{0}) (i j : ℕ)
    (mu : SingularHomologyCrossProductHomData R X Y i j) : Prop :=
  let KX := nativeSingularChainComplexData R X
  let KY := nativeSingularChainComplexData R Y
  let KXY := nativeSingularChainComplexData R (X ⨯ Y)
  ∀ (x : KX.cycles i) (y : KY.cycles j),
    ∃ z : KXY.cycles (i + j),
      (KXY.iCycles (i + j)).hom z =
          (nativeSingularChainEquivRawData R (X ⨯ Y) (i + j)).symm
            (singularCrossProduct R
              (nativeSingularChainEquivRawData R X i ((KX.iCycles i).hom x))
              (nativeSingularChainEquivRawData R Y j ((KY.iCycles j).hom y))) ∧
        mu.hom
            (((KX.homologyπ i).hom x) ⊗ₜ[R] ((KY.homologyπ j).hom y)) =
          (KXY.homologyπ (i + j)).hom z

/-- Hatcher's homology cross product selected from its exact
representative-level shuffle-product specification. -/
def singularHomologyCrossProductData
    (R : Type) [CommRing R] (X Y : TopCat.{0}) (i j : ℕ) :
    SingularHomologyCrossProductHomData R X Y i j :=
  Classical.epsilon (IsSingularHomologyCrossProductData R X Y i j)

end LeanCategories.Topology
