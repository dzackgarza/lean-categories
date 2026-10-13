/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-!
# Reduction data for curves over arithmetic bases

Definition-level realization of Neukirch FC09-C03-U049.

For a curve over the generic field of an arithmetic base, reduction at a
finite prime is the special fibre of an integral model.  The source calls the
reduction good when this special fibre is smooth.

Sweep III records this at the data/predicate level:

* a model candidate is a scheme equipped with its structural morphism;
* a model of the given generic curve is a proper flat candidate whose generic
  fibre is identified with that curve over the generic residue field;
* reduction at the chosen prime is literally the scheme-theoretic fibre;
* good reduction means that the fibre morphism to the residue field is smooth.

No existence of models, independence of the chosen model, comparison of
different models, preservation of relative dimension, or smooth-proper-model
criterion is proved here.  Those are result-layer statements.
-/

@[expose] public noncomputable section

open CategoryTheory
open AlgebraicGeometry

namespace LeanCategories.Schemes

universe u

/-- Raw arithmetic model data over a base scheme.

The defining data are only the total space and its structural morphism.  All
geometric conditions are kept as separate predicates so constructing a model
candidate requires no proof-valued fields. -/
structure CurveModelCandidateData (S : Scheme.{u}) where
  totalSpace : Scheme.{u}
  toBase : totalSpace ⟶ S

/-- The reduction of a supplied model candidate at a point of the base:
its scheme-theoretic fibre. -/
def curveReductionData {S : Scheme.{u}}
    (M : CurveModelCandidateData S) (s : S) : Scheme.{u} :=
  M.toBase.fiber s

/-- The canonical morphism from the reduction to the residue field of the
chosen base point. -/
def curveReductionToResidueFieldData {S : Scheme.{u}}
    (M : CurveModelCandidateData S) (s : S) :
    curveReductionData M s ⟶ Spec (S.residueField s) :=
  M.toBase.fiberToSpecResidueField s

/-- Predicate saying that a model candidate is a proper flat model of a
specified curve over the residue field at a designated generic point.

The isomorphism and its compatibility equation occur only inside the
predicate; they are not constructor fields of the raw model data. -/
def IsCurveModelData {S X : Scheme.{u}} (η : S)
    (XtoGeneric : X ⟶ Spec (S.residueField η))
    (M : CurveModelCandidateData S) : Prop :=
  Flat M.toBase ∧
    IsProper M.toBase ∧
    ∃ e : M.toBase.fiber η ≅ X,
      e.hom ≫ XtoGeneric = M.toBase.fiberToSpecResidueField η

/-- A supplied model has smooth reduction at the chosen base point exactly
when its special-fibre morphism to the residue field is smooth. -/
def HasSmoothReductionData {S : Scheme.{u}}
    (M : CurveModelCandidateData S) (s : S) : Prop :=
  Smooth (curveReductionToResidueFieldData M s)

/-- Neukirch's good-reduction predicate at a finite prime, formulated over a
base scheme with designated generic and special points.

It asserts the existence of a proper flat model of the given generic curve
whose reduction at the special point is smooth.  Model existence and
model-independence are not bundled into any constructor. -/
def HasGoodReductionAtData {S X : Scheme.{u}} (η s : S)
    (XtoGeneric : X ⟶ Spec (S.residueField η)) : Prop :=
  ∃ M : CurveModelCandidateData S,
    IsCurveModelData η XtoGeneric M ∧ HasSmoothReductionData M s

end LeanCategories.Schemes
