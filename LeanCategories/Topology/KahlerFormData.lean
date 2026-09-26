/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Group.Defs

/-!
# Kähler-form data

Definition-level realization of Peters--Sterk FC11-B-U001 and FC11-B-U002.

The source starts with a Hermitian metric and its associated real `(1,1)`-form
`κ`; the metric is Kähler exactly when `κ` is closed.  The pinned Atlas
reference packages the same closedness clause in its Kähler-form interface.

Sweep III records only that defining predicate.  The construction of the
fundamental form from a Hermitian metric, the assertion that it is real of type
`(1,1)`, nondegenerate/positive, and the equivalence between the metric and
form presentations are separate inputs or comparison/result content.  In
particular this file does not introduce a replacement differential-form or
complex-manifold theory.
-/

@[expose] public section

namespace LeanCategories.Topology

/-- The Peters--Sterk Kähler condition for a Hermitian metric (FC11-B-U001).

`fundamentalForm g` is the already supplied real `(1,1)`-form associated to
the Hermitian metric `g`.  The only new definitional clause is that this form
is closed. -/
def IsKahlerMetric
    {HermitianMetric TwoForm ThreeForm : Type*}
    [Zero ThreeForm]
    (fundamentalForm : HermitianMetric → TwoForm)
    (exteriorDerivative : TwoForm → ThreeForm)
    (g : HermitianMetric) : Prop :=
  exteriorDerivative (fundamentalForm g) = 0

/-- The type of Kähler Hermitian metrics for fixed fundamental-form and
exterior-derivative constructions. -/
def KahlerMetricData
    {HermitianMetric TwoForm ThreeForm : Type*}
    [Zero ThreeForm]
    (fundamentalForm : HermitianMetric → TwoForm)
    (exteriorDerivative : TwoForm → ThreeForm) :=
  {g : HermitianMetric //
    IsKahlerMetric fundamentalForm exteriorDerivative g}

/-- The corresponding Kähler-form predicate at the same data boundary.

`IsHermitianFundamentalForm κ` supplies the pre-existing condition that `κ`
is a real `(1,1)`-form arising from Hermitian data.  This definition adds
exactly the closedness condition, without proving the metric/form comparison. -/
def IsKahlerForm
    {TwoForm ThreeForm : Type*}
    [Zero ThreeForm]
    (IsHermitianFundamentalForm : TwoForm → Prop)
    (exteriorDerivative : TwoForm → ThreeForm)
    (κ : TwoForm) : Prop :=
  IsHermitianFundamentalForm κ ∧ exteriorDerivative κ = 0

/-- The type of Kähler forms at the same source data boundary. -/
def KahlerFormData
    {TwoForm ThreeForm : Type*}
    [Zero ThreeForm]
    (IsHermitianFundamentalForm : TwoForm → Prop)
    (exteriorDerivative : TwoForm → ThreeForm) :=
  {κ : TwoForm //
    IsKahlerForm IsHermitianFundamentalForm exteriorDerivative κ}

/-- A complex manifold is Kähler when it admits a Kähler Hermitian metric
(Peters--Sterk FC11-B-U002).

The carrier of complex manifolds, the family of Hermitian metrics on each
manifold, their fundamental forms, and exterior derivatives are supplied by
their respective owners.  This predicate records only the source's existential
definition. -/
def IsKahlerManifold
    {ComplexManifold : Type*}
    (HermitianMetric : ComplexManifold → Type*)
    (TwoForm : ComplexManifold → Type*)
    (ThreeForm : ComplexManifold → Type*)
    [∀ X, Zero (ThreeForm X)]
    (fundamentalForm : ∀ X, HermitianMetric X → TwoForm X)
    (exteriorDerivative : ∀ X, TwoForm X → ThreeForm X)
    (X : ComplexManifold) : Prop :=
  ∃ g : HermitianMetric X,
    IsKahlerMetric (fundamentalForm X) (exteriorDerivative X) g

/-- The type of complex manifolds equipped with the source property of
admitting a Kähler metric. -/
def KahlerManifoldData
    {ComplexManifold : Type*}
    (HermitianMetric : ComplexManifold → Type*)
    (TwoForm : ComplexManifold → Type*)
    (ThreeForm : ComplexManifold → Type*)
    [∀ X, Zero (ThreeForm X)]
    (fundamentalForm : ∀ X, HermitianMetric X → TwoForm X)
    (exteriorDerivative : ∀ X, TwoForm X → ThreeForm X) :=
  {X : ComplexManifold //
    IsKahlerManifold HermitianMetric TwoForm ThreeForm
      fundamentalForm exteriorDerivative X}

end LeanCategories.Topology
