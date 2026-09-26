/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Topology.SingularCupProduct
public import LeanCategories.Topology.SingularCapProduct
public import Mathlib.Algebra.DirectSum.Basic
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.CategoryTheory.Abelian.Ext
public import Mathlib.LinearAlgebra.TensorProduct.Basic

/-!
# Singular cohomology-ring data

Definition-level realization of Hatcher FC07-C03-U019, following the pinned
ATLAS singular-cohomology construction.

The additive carrier is the direct sum

`H^*(X;R) = ⨁ n, H^n(X;R)`,

where singular cohomology is the homology of the linear-Yoneda cochain complex
of singular chains.  The cup pairing on cochains and its descent to
cohomology are represented as supplied candidates satisfying Hatcher's exact
front-face/back-face and representative-level graphs.  No arbitrary candidate
is selected before the corresponding existence/descent results.

No cocycle-closure, representative-independence, associativity, unit,
distributivity, or graded-commutativity theorem is proved here.  Those are
result content beyond Sweep III.
-/

@[expose] public noncomputable section

namespace LeanCategories.Topology

open AlgebraicTopology CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped TensorProduct

/-- The singular cochain complex
`S^*(X;G) = Hom_R(S_*(X;R),G)`. -/
def singularCochainComplexData (R : Type) [CommRing R]
    (X : TopCat.{0}) (G : ModuleCat.{0} R) :
    CochainComplex (ModuleCat.{0} R) ℕ :=
  (((singularChainComplexFunctor.{0} (ModuleCat.{0} R)).obj
    (ModuleCat.of R R)).obj X).linearYonedaObj R G

/-- Singular cohomology `H^n(X;G)` as the homology of the singular
cochain complex. -/
def singularCohomologyModuleData (R : Type) [CommRing R]
    (X : TopCat.{0}) (G : ModuleCat.{0} R) (n : ℕ) : ModuleCat.{0} R :=
  (singularCochainComplexData R X G).homology n

/-- The graded family `n ↦ H^n(X;R)` of coefficient-ring singular
cohomology groups. -/
abbrev singularCohomologyFamilyData (R : Type) [CommRing R]
    (X : TopCat.{0}) : ℕ → Type :=
  fun n => (singularCohomologyModuleData R X (ModuleCat.of R R) n : Type)

instance (R : Type) [CommRing R] (X : TopCat.{0}) (n : ℕ) :
    AddCommGroup (singularCohomologyFamilyData R X n) :=
  ModuleCat.isAddCommGroup _

/-- Hatcher's additive carrier `⊕_{n≥0} H^n(X;R)` for the cohomology ring. -/
abbrev cohomologyRingCarrierData (R : Type) [CommRing R] (X : TopCat.{0}) :=
  DirectSum ℕ (singularCohomologyFamilyData R X)

/-- Singular `n`-simplices in the simplicial-set model used by singular
chains. -/
abbrev singularCohomologySimplexData (X : TopCat.{0}) (n : ℕ) : Type :=
  (TopCat.toSSet.obj X).obj (Opposite.op (SimplexCategory.mk n))

/-- Evaluation of a singular cochain at a singular simplex. -/
def singularCochainEvalData (R : Type) [CommRing R]
    {n : ℕ} (X : TopCat.{0}) (σ : singularCohomologySimplexData X n) :
    (singularCochainComplexData R X (ModuleCat.of R R)).X n →ₗ[R] R where
  toFun φ :=
    (Sigma.ι
      (fun (_ : singularCohomologySimplexData X n) => ModuleCat.of R R) σ ≫ φ).hom 1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Front face of a singular `(p+q)`-simplex. -/
def singularCupFrontSimplexData (X : TopCat.{0}) (p q : ℕ)
    (σ : singularCohomologySimplexData X (p + q)) :
    singularCohomologySimplexData X p :=
  (TopCat.toSSet.obj X).map (singularCapFrontFace p q).op σ

/-- Back face of a singular `(p+q)`-simplex. -/
def singularCupBackSimplexData (X : TopCat.{0}) (p q : ℕ)
    (σ : singularCohomologySimplexData X (p + q)) :
    singularCohomologySimplexData X q :=
  (TopCat.toSSet.obj X).map (singularCapBackFace p q).op σ

/-- Type of a degree-`(p,q)` cochain cup-pairing candidate. -/
abbrev SingularCochainCupPairingHomData
    (R : Type) [CommRing R] (X : TopCat.{0}) (p q : ℕ) :=
  (singularCochainComplexData R X (ModuleCat.of R R)).X p ⊗
      (singularCochainComplexData R X (ModuleCat.of R R)).X q ⟶
    (singularCochainComplexData R X (ModuleCat.of R R)).X (p + q)

/-- Hatcher's exact front-face/back-face graph for a bundled cochain
cup pairing. -/
def IsSingularCochainCupPairingData
    (R : Type) [CommRing R] (X : TopCat.{0}) (p q : ℕ)
    (μ : SingularCochainCupPairingHomData R X p q) : Prop :=
  ∀ (φ : (singularCochainComplexData R X (ModuleCat.of R R)).X p)
      (ψ : (singularCochainComplexData R X (ModuleCat.of R R)).X q)
      (σ : singularCohomologySimplexData X (p + q)),
    singularCochainEvalData R X σ (μ.hom (φ ⊗ₜ[R] ψ)) =
      singularCochainEvalData R X (singularCupFrontSimplexData X p q σ) φ *
        singularCochainEvalData R X (singularCupBackSimplexData X p q σ) ψ

/-- Source-faithful cochain cup-pairing data: a bundled linear candidate
together with Hatcher's exact raw evaluation graph. -/
abbrev SingularCochainCupPairingData
    (R : Type) [CommRing R] (X : TopCat.{0}) (p q : ℕ) :
    Type :=
  {μ : SingularCochainCupPairingHomData R X p q //
    IsSingularCochainCupPairingData R X p q μ}

/-- Type of a cup-product candidate on singular cohomology. -/
abbrev SingularCohomologyCupProductHomData
    (R : Type) [CommRing R] (X : TopCat.{0}) (p q : ℕ) :=
  singularCohomologyModuleData R X (ModuleCat.of R R) p ⊗
      singularCohomologyModuleData R X (ModuleCat.of R R) q ⟶
    singularCohomologyModuleData R X (ModuleCat.of R R) (p + q)

/-- Representative-level graph saying that a cohomology pairing is the
descent of the selected cochain cup pairing.

For cocycle representatives `x` and `y`, a cocycle `z` representing
their cochain cup is required to map to the value of `μ` on the two
cohomology classes.  The existence of such `z` and independence of all
representatives are deliberately not proved here. -/
def IsSingularCohomologyCupProductData
    (R : Type) [CommRing R] (X : TopCat.{0}) (p q : ℕ)
    (μC : SingularCochainCupPairingData R X p q)
    (μ : SingularCohomologyCupProductHomData R X p q) : Prop :=
  let K := singularCochainComplexData R X (ModuleCat.of R R)
  ∀ (x : K.cycles p) (y : K.cycles q),
    ∃ z : K.cycles (p + q),
      (K.iCycles (p + q)).hom z =
          μC.1.hom (((K.iCycles p).hom x) ⊗ₜ[R] ((K.iCycles q).hom y)) ∧
        μ.hom
            (((K.homologyπ p).hom x) ⊗ₜ[R] ((K.homologyπ q).hom y)) =
          (K.homologyπ (p + q)).hom z

/-- Source-faithful singular-cohomology cup-product data: a candidate
homogeneous product together with its exact representative-level descent
graph from supplied cochain cup data. -/
abbrev SingularCohomologyCupProductData
    (R : Type) [CommRing R] (X : TopCat.{0}) (p q : ℕ) :
    SingularCochainCupPairingData R X p q → Type :=
  fun μC =>
    {μ : SingularCohomologyCupProductHomData R X p q //
      IsSingularCohomologyCupProductData R X p q μC μ}

/-- A coherent family of exact cup-product construction data in all
bidegrees.  The fields are data, not proofs manufactured in Sweep III. -/
structure SingularCohomologyCupData
    (R : Type) [CommRing R] (X : TopCat.{0}) where
  cochain (p q : ℕ) : SingularCochainCupPairingData R X p q
  cohomology (p q : ℕ) :
    SingularCohomologyCupProductData R X p q (cochain p q)

/-- Homogeneous cup multiplication
`H^p(X;R) × H^q(X;R) → H^{p+q}(X;R)`. -/
def singularCohomologyCupMulData
    (R : Type) [CommRing R] (X : TopCat.{0})
    (D : SingularCohomologyCupData R X) {p q : ℕ}
    (x : singularCohomologyFamilyData R X p)
    (y : singularCohomologyFamilyData R X q) :
    singularCohomologyFamilyData R X (p + q) :=
  (D.cohomology p q).1.hom (x ⊗ₜ[R] y)

/-- The total cup multiplication on
`H^*(X;R) = ⨁ n, H^n(X;R)`, obtained by finite distributive extension of
the homogeneous cup products.

This is only the multiplication data.  No unit, associativity,
distributivity, or graded-commutativity theorem is used to define it. -/
def cohomologyRingCarrierMulData
    (R : Type) [CommRing R] (X : TopCat.{0})
    (D : SingularCohomologyCupData R X)
    (x y : cohomologyRingCarrierData R X) :
    cohomologyRingCarrierData R X := by
  classical
  exact
    ∑ p ∈ x.support, ∑ q ∈ y.support,
      DirectSum.of (singularCohomologyFamilyData R X) (p + q)
        (singularCohomologyCupMulData R X D (x p) (y q))

/-- Hatcher's total cohomology-ring carrier, as a wrapper around the direct
sum of singular cohomology groups.  The source multiplication is supplied by
`SingularCohomologyRingData.mul` below.

The wrapper intentionally carries no `Ring` instance in Sweep III: those
law fields are proposition/result content. -/
structure SingularCohomologyRingData
    (R : Type) [CommRing R] (X : TopCat.{0}) where
  toDirectSum : cohomologyRingCarrierData R X

namespace SingularCohomologyRingData

/-- Total cup multiplication on Hatcher's cohomology-ring carrier. -/
def mul
    (R : Type) [CommRing R] (X : TopCat.{0})
    (D : SingularCohomologyCupData R X)
    (x y : SingularCohomologyRingData R X) :
    SingularCohomologyRingData R X :=
  ⟨cohomologyRingCarrierMulData R X D x.toDirectSum y.toDirectSum⟩

/-- A homogeneous cohomology class included into the total cohomology-ring
carrier in its degree. -/
def of
    (R : Type) [CommRing R] (X : TopCat.{0}) {n : ℕ}
    (x : singularCohomologyFamilyData R X n) :
    SingularCohomologyRingData R X :=
  ⟨DirectSum.of (singularCohomologyFamilyData R X) n x⟩

end SingularCohomologyRingData

end LeanCategories.Topology
