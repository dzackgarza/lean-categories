/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Modules.Bilinear.Valued.Witt
public import LeanCategories.Modules.Quadratic.Valued.Subcategories
public import LeanCategories.Modules.Quadratic.Valued.Witt
public import Mathlib.LinearAlgebra.BilinearForm.TensorProduct
public import Mathlib.LinearAlgebra.QuadraticForm.Basis
public import Mathlib.LinearAlgebra.QuadraticForm.Dual
public import Mathlib.LinearAlgebra.QuadraticForm.Prod
public import Mathlib.RingTheory.Finiteness.Prod

/-!
# Quadratic Witt-ring data

Definition-level data for Peters--Sterk FC11-C07-U021.

The source first declares stable isometry after adjoining split quadratic
inner-product spaces, then forms equivalence classes and equips them with
orthogonal-sum and tensor-product operations. Sweep III records the objects,
the stable-isometry relation, the raw quotient carrier, and the representative
operation formulas. It does not prove that stable isometry is an equivalence
relation, that orthogonal sum or tensor product preserve the source class, that
the formulas descend to the quotient, or that the descended operations satisfy
the commutative-ring laws.

In particular, no arbitrary choice of quotient operations is introduced here.
Those descended operations are result-layer constructions once the required
well-definedness statements have been established.
-/

@[expose] public noncomputable section

open CategoryTheory
open TensorProduct

namespace LeanCategories.Modules.Quadratic.Valued

universe u

variable (R : Type u) [CommRing R]

/-- Orthogonal sum of finite free scalar-valued quadratic modules. -/
def finiteFreeQuadOrthogonalSum
    (Q P : FiniteFreeQuadModuleCat R R) :
    FiniteFreeQuadModuleCat R R := by
  letI : Module.Free R Q.obj.carrier := Q.property.1
  letI : Module.Finite R Q.obj.carrier := Q.property.2
  letI : Module.Free R P.obj.carrier := P.property.1
  letI : Module.Finite R P.obj.carrier := P.property.2
  refine ⟨QuadModuleCat.ofQuadraticMap (Q.obj.form.prod P.obj.form), ?_⟩
  change Module.Free R (Q.obj.carrier × P.obj.carrier) ∧
    Module.Finite R (Q.obj.carrier × P.obj.carrier)
  constructor <;> infer_instance

/-- A finite free quadratic inner-product space, in the source sense that its
polar correlation map is an isomorphism. -/
structure QuadraticInnerProductSpaceData where
  formed : FiniteFreeQuadModuleCat R R
  isPerfect : formed.obj.IsPerfect

/-- The bilinear module obtained from the polar form of a quadratic module. -/
def quadraticPolarBilinModule
    (Q : FiniteFreeQuadModuleCat R R) :
    LeanCategories.Modules.Bilinear.Valued.BilinModuleCat R R :=
  LeanCategories.Modules.Bilinear.Valued.BilinModuleCat.ofBilinMap
    Q.obj.polarBilin

/-- Data exhibiting a quadratic inner-product space as split.

The source uses split spaces, rather than only sums of standard hyperbolic
planes, in the non-invertible-two setting. The datum therefore records a
Lagrangian on which the quadratic form itself vanishes. -/
structure SplitQuadraticInnerProductSpaceData where
  innerProduct : QuadraticInnerProductSpaceData R
  lagrangian : Submodule R innerProduct.formed.obj.carrier
  isotropic : innerProduct.formed.obj.IsTotallyIsotropic lagrangian
  polarSelfOrthogonal :
    (quadraticPolarBilinModule R innerProduct.formed).orthogonalSubmodule
        lagrangian = lagrangian

/-- The standard hyperbolic quadratic space of Witt rank `n`, represented by
the form `(f,x) ↦ f(x)` on the dual-product of `R^n`.

This is one source of split spaces; split spaces are not defined to be only
objects of this form. -/
def hyperbolicFiniteFreeQuadraticSpace (n : ℕ) :
    FiniteFreeQuadModuleCat R R := by
  let M := Fin n → R
  letI : AddCommGroup M := inferInstance
  letI : Module R M := inferInstance
  letI : Module.Free R M := inferInstance
  letI : Module.Finite R M := inferInstance
  refine ⟨QuadModuleCat.ofQuadraticMap (QuadraticForm.dualProd R M), ?_⟩
  change Module.Free R (Module.Dual R M × M) ∧
    Module.Finite R (Module.Dual R M × M)
  constructor <;> infer_instance

/-- The additive inverse representative of a finite free quadratic space. -/
def negativeFiniteFreeQuadraticSpace
    (Q : FiniteFreeQuadModuleCat R R) :
    FiniteFreeQuadModuleCat R R :=
  ⟨QuadModuleCat.ofQuadraticMap (-Q.obj.form), Q.property⟩

/-- The rank-one unit quadratic space `x ↦ x²`. -/
def unitFiniteFreeQuadraticSpace : FiniteFreeQuadModuleCat R R := by
  refine ⟨QuadModuleCat.ofQuadraticMap (QuadraticMap.sq (R := R)), ?_⟩
  change Module.Free R R ∧ Module.Finite R R
  constructor <;> infer_instance

/-- Stable isometry after adjoining (possibly different) split quadratic
inner-product spaces. -/
structure QuadraticWittStableIsometry
    (Q P : QuadraticInnerProductSpaceData R) where
  leftSplit : SplitQuadraticInnerProductSpaceData R
  rightSplit : SplitQuadraticInnerProductSpaceData R
  isometry :
    finiteFreeQuadOrthogonalSum R Q.formed leftSplit.innerProduct.formed ≅
      finiteFreeQuadOrthogonalSum R P.formed rightSplit.innerProduct.formed

/-- Peters--Sterk Witt equivalence for finite free quadratic inner-product
spaces. -/
def IsQuadraticWittEquivalent
    (Q P : QuadraticInnerProductSpaceData R) : Prop :=
  Nonempty (QuadraticWittStableIsometry R Q P)

/-- Raw quotient carrier for the quadratic Witt construction.

`Quot` does not require a proof that the relation is an equivalence relation;
that proof and the comparison with genuine equivalence classes belong to
Sweep IV. -/
abbrev QuadraticWittClass :=
  Quot (IsQuadraticWittEquivalent R)

/-- Send a finite free quadratic space to its raw Witt class. -/
def quadraticWittClassMk
    (Q : QuadraticInnerProductSpaceData R) : QuadraticWittClass R :=
  Quot.mk _ Q

/-- A bilinear companion selected for a quadratic form on a free module.

Mathlib proves that `BilinMap.toQuadraticMap` is surjective on free modules,
including in characteristic two. Selecting a preimage avoids dividing by two
and supplies the data needed for the source tensor-product formula. -/
noncomputable def quadraticCompanionData
    (Q : FiniteFreeQuadModuleCat R R) :
    LinearMap.BilinForm R Q.obj.carrier := by
  letI : Module.Free R Q.obj.carrier := Q.property.1
  exact Classical.choose
    (LinearMap.BilinMap.toQuadraticMap_surjective Q.obj.form)

/-- The source tensor-product quadratic form, constructed from selected
bilinear companions and the native bilinear tensor product.

Changing the selected companions/bases and proving independence up to Witt
equivalence are result-layer statements. -/
noncomputable def quadraticTensorProductFormData
    (Q P : FiniteFreeQuadModuleCat R R) :
    QuadraticForm R (Q.obj.carrier ⊗[R] P.obj.carrier) :=
  LinearMap.BilinMap.toQuadraticMap
    ((quadraticCompanionData R Q).tmul (quadraticCompanionData R P))

/-- Finite-free representative carrying the tensor-product quadratic form. -/
noncomputable def finiteFreeQuadraticTensorProductData
    (Q P : FiniteFreeQuadModuleCat R R) :
    FiniteFreeQuadModuleCat R R := by
  letI : Module.Free R Q.obj.carrier := Q.property.1
  letI : Module.Finite R Q.obj.carrier := Q.property.2
  letI : Module.Free R P.obj.carrier := P.property.1
  letI : Module.Finite R P.obj.carrier := P.property.2
  refine ⟨QuadModuleCat.ofQuadraticMap
    (quadraticTensorProductFormData R Q P), ?_⟩
  change Module.Free R (Q.obj.carrier ⊗[R] P.obj.carrier) ∧
    Module.Finite R (Q.obj.carrier ⊗[R] P.obj.carrier)
  constructor <;> infer_instance

/-- Orthogonal-sum representative prescribed for addition in the Witt group. -/
def quadraticWittAddRepresentativeData
    (Q P : QuadraticInnerProductSpaceData R) :
    FiniteFreeQuadModuleCat R R :=
  finiteFreeQuadOrthogonalSum R Q.formed P.formed

/-- Negated-form representative prescribed for the additive inverse. -/
def quadraticWittNegRepresentativeData
    (Q : QuadraticInnerProductSpaceData R) :
    FiniteFreeQuadModuleCat R R :=
  negativeFiniteFreeQuadraticSpace R Q.formed

/-- Rank-one representative prescribed for the multiplicative unit. -/
def quadraticWittOneRepresentativeData :
    FiniteFreeQuadModuleCat R R :=
  unitFiniteFreeQuadraticSpace R

/-- Zero-dimensional split representative prescribed for the additive zero. -/
def quadraticWittZeroRepresentativeData :
    FiniteFreeQuadModuleCat R R :=
  hyperbolicFiniteFreeQuadraticSpace R 0

/-- Tensor-product representative prescribed for multiplication in the Witt
ring. -/
noncomputable def quadraticWittMulRepresentativeData
    (Q P : QuadraticInnerProductSpaceData R) :
    FiniteFreeQuadModuleCat R R :=
  finiteFreeQuadraticTensorProductData R Q.formed P.formed

/-- A raw Witt class admits the displayed finite-free quadratic form as a
representative.

This is intentionally a relation rather than a selected representative.  It
does not require proving that the displayed form is perfect: a witness is an
actual quadratic inner-product space whose underlying formed module is the
displayed one. -/
def IsQuadraticWittRepresentativeData
    (x : QuadraticWittClass R)
    (Q : FiniteFreeQuadModuleCat R R) : Prop :=
  ∃ P : QuadraticInnerProductSpaceData R,
    quadraticWittClassMk R P = x ∧ P.formed = Q

/-- Exact graph of the additive zero on the raw Witt quotient. -/
def IsQuadraticWittZeroData
    (z : QuadraticWittClass R) : Prop :=
  IsQuadraticWittRepresentativeData R z
    (quadraticWittZeroRepresentativeData R)

/-- Exact representative graph of orthogonal-sum addition on the raw Witt
quotient.

Sweep IV proves that this graph is total and single-valued, hence descends to
an actual binary operation. -/
def IsQuadraticWittAddData
    (x y z : QuadraticWittClass R) : Prop :=
  ∃ Q P : QuadraticInnerProductSpaceData R,
    quadraticWittClassMk R Q = x ∧
    quadraticWittClassMk R P = y ∧
    IsQuadraticWittRepresentativeData R z
      (quadraticWittAddRepresentativeData R Q P)

/-- Exact representative graph of additive inversion on the raw Witt
quotient. -/
def IsQuadraticWittNegData
    (x z : QuadraticWittClass R) : Prop :=
  ∃ Q : QuadraticInnerProductSpaceData R,
    quadraticWittClassMk R Q = x ∧
    IsQuadraticWittRepresentativeData R z
      (quadraticWittNegRepresentativeData R Q)

/-- Exact representative graph of the multiplicative unit on the raw Witt
quotient. -/
def IsQuadraticWittOneData
    (z : QuadraticWittClass R) : Prop :=
  IsQuadraticWittRepresentativeData R z
    (quadraticWittOneRepresentativeData R)

/-- Exact representative graph of tensor-product multiplication on the raw
Witt quotient.

No quotient descent, independence-of-companion assertion, or ring law is
proved here. -/
noncomputable def IsQuadraticWittMulData
    (x y z : QuadraticWittClass R) : Prop :=
  ∃ Q P : QuadraticInnerProductSpaceData R,
    quadraticWittClassMk R Q = x ∧
    quadraticWittClassMk R P = y ∧
    IsQuadraticWittRepresentativeData R z
      (quadraticWittMulRepresentativeData R Q P)

end LeanCategories.Modules.Quadratic.Valued
