/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Schemes.PicardGroupData
public import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# Relative degree-zero Picard data

Definition-level realization of Hartshorne FC06-C04-U081.

For a curve X over k and a test k-scheme T, Hartshorne defines Pic^0(X/T)
from invertible sheaves on X × T whose restrictions to the fibres have degree
zero, modulo tensoring by invertible sheaves pulled back from T.

The repository already owns invertible O-modules, their tensor product,
scheme-module pullback, fibre products, and the curve-degree predicate. What
is not yet theorem-free is packaging their isomorphism classes as a quotient
group: equivalence laws for the base-twist relation and the Picard group laws
are result content.

This file therefore records the exact quotient presentation. The actual
product scheme and its projections are supplied by the native fibre-product
owner. A supplied fibre-degree map records the already-defined restriction
and degree operation. Candidate relative-Picard data consist only of a carrier
and a class map. The source quotient is characterized propositionally by
surjectivity and by the exact base-twist equality graph; no quotient carrier
is selected before those quotient facts are established.

No quotient equivalence laws, Picard group laws, representability, or
Jacobian theorem are proved in Sweep III.
-/

@[expose] public noncomputable section

open CategoryTheory
open LeanCategories.AlgebraicGeometry
open AlgebraicGeometry

namespace LeanCategories.Schemes

universe u

/-- The already-constructed geometric inputs needed to state fibrewise degree
zero on X × T.

In the source application, product is the native fibre product of X and T
over Spec k, fst and snd are its projections, and fibreDegree t L is the
degree of the restriction of L to the curve fibre over t. Construction and
comparison of that degree map are earlier obligations; this record does not
prove them. -/
structure RelativePicardFibreDegreeData
    (X T product : Scheme.{u}) where
  fst : product ⟶ X
  snd : product ⟶ T
  fibreDegree : T → product.Modules → ℤ

/-- An invertible sheaf on X × T whose restriction has degree zero on every
fibre. -/
structure RelativePicardZeroSheafData
    {X T product : Scheme.{u}}
    (D : RelativePicardFibreDegreeData X T product) where
  sheaf : product.Modules
  invertible : IsTensorInvertible sheaf
  fibre_degree_zero : ∀ t : T, D.fibreDegree t sheaf = 0

/-- The source relation saying that two fibrewise-degree-zero invertible
sheaves differ by an invertible sheaf pulled back from the test scheme.

That this relation is an equivalence relation is deliberately not proved here.
-/
def RelativePicardBaseTwistData
    {X T product : Scheme.{u}}
    (D : RelativePicardFibreDegreeData X T product)
    (L M : RelativePicardZeroSheafData D) : Prop :=
  ∃ (N : T.Modules) (_hN : IsTensorInvertible N),
    Nonempty
      (M.sheaf ≅
        schemeModuleTensor L.sheaf
          ((Scheme.Modules.pullback D.snd).obj N))

/-- Candidate data for the quotient defining Pic^0(X/T): a carrier together
with the class of every fibrewise-degree-zero invertible sheaf. -/
structure RelativePicardZeroCandidateData
    {X T product : Scheme.{u}}
    (D : RelativePicardFibreDegreeData X T product) where
  carrier : Type u
  classOf : RelativePicardZeroSheafData D → carrier

/-- Exact source specification of the relative degree-zero Picard quotient.

Every candidate class is represented by a fibrewise-degree-zero invertible
sheaf, and two representatives have equal classes exactly when they differ by
tensoring with a pullback from T. -/
def IsRelativePicardZeroData
    {X T product : Scheme.{u}}
    (D : RelativePicardFibreDegreeData X T product)
    (P : RelativePicardZeroCandidateData D) : Prop :=
  Function.Surjective P.classOf ∧
    ∀ L M : RelativePicardZeroSheafData D,
      P.classOf L = P.classOf M ↔ RelativePicardBaseTwistData D L M

/-- The source-facing carrier of supplied Pic^0(X/T) candidate data.
Source-faithfulness is recorded separately by `IsRelativePicardZeroData`. -/
abbrev RelativePicardZeroData
    {X T product : Scheme.{u}}
    {D : RelativePicardFibreDegreeData X T product}
    (P : RelativePicardZeroCandidateData D) : Type u :=
  P.carrier

end LeanCategories.Schemes
