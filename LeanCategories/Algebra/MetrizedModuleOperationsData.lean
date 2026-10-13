/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Star.Basic
public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.LinearAlgebra.ExteriorPower.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Basic

/-!
# Induced metric data on module operations

Definition-level realization of Neukirch FC09-C03-U082.

For metrized modules `M` and `N`, Neukirch equips the direct sum, tensor
product, dual and exterior powers with the pairings determined by

* `⟨x ⊕ x', y ⊕ y'⟩ = ⟨x,y⟩ + ⟨x',y'⟩`;
* `⟨x ⊗ x', y ⊗ y'⟩ = ⟨x,y⟩ ⟨x',y'⟩`;
* `⟨x̌,y̌⟩ = star ⟨x,y⟩`, where `x̌ = ⟨-,x⟩`;
* the determinant formula on decomposable exterior-power elements.

Sweep III records those formulas only.  Extending the generator formulas to
well-defined sesquilinear pairings, proving the selected pairings satisfy their
specifications, Hermitian symmetry, positive definiteness, `F`-invariance,
and identifying the complexifications with the corresponding algebraic
operations are result-layer obligations.
-/

@[expose] public noncomputable section

namespace LeanCategories.Algebra

universe uR uM uN

/-- Raw pairing data on a module carrier.  Sesquilinearity, Hermitian symmetry,
positivity and Frobenius invariance are deliberately separate predicates/results. -/
abbrev MetricPairingData (R : Type uR) (M : Type uM) := M → M → R

variable
  {R : Type uR} [CommRing R] [Star R]
  {M : Type uM} [AddCommGroup M] [Module R M]
  {N : Type uN} [AddCommGroup N] [Module R N]

/-- Orthogonal direct-sum metric:
`⟨x ⊕ x',y ⊕ y'⟩ = ⟨x,y⟩ + ⟨x',y'⟩`. -/
def directSumMetricData
    (hM : MetricPairingData R M) (hN : MetricPairingData R N) :
    MetricPairingData R (M × N) :=
  fun x y => hM x.1 y.1 + hN x.2 y.2

/-- Characterization of the tensor-product metric by its values on pure
tensors, exactly as displayed in FC09-C03-U082. -/
def IsTensorProductMetricData
    (hM : MetricPairingData R M) (hN : MetricPairingData R N)
    (h : MetricPairingData R (TensorProduct R M N)) : Prop :=
  ∀ x y : M, ∀ x' y' : N,
    h (x ⊗ₜ[R] x') (y ⊗ₜ[R] y') = hM x y * hN x' y'

/-- Tensor-product pairing selected by the pure-tensor formula.

The later specification theorem proves that, for the Hermitian metrics of the
source, this selection satisfies `IsTensorProductMetricData`. -/
def tensorProductMetricData
    (hM : MetricPairingData R M) (hN : MetricPairingData R N) :
    MetricPairingData R (TensorProduct R M N) :=
  Classical.epsilon (IsTensorProductMetricData hM hN)

/-- Characterization of the metric-dual map `x ↦ x̌ = ⟨-,x⟩`. -/
def IsMetricDualMapData
    (hM : MetricPairingData R M)
    (flat : M → Module.Dual R M) : Prop :=
  ∀ x y : M, flat x y = hM y x

/-- The source's metric-dual assignment `x ↦ ⟨-,x⟩`, selected by its
pointwise formula.  Linearity in the first argument of a genuine Hermitian
metric proves the later specification. -/
def metricDualMapData
    (hM : MetricPairingData R M) : M → Module.Dual R M :=
  Classical.epsilon (IsMetricDualMapData hM)

/-- Characterization of the dual metric by
`⟨x̌,y̌⟩ = star ⟨x,y⟩`. -/
def IsDualMetricData
    (hM : MetricPairingData R M)
    (hDual : MetricPairingData R (Module.Dual R M)) : Prop :=
  ∀ x y : M,
    hDual (metricDualMapData hM x) (metricDualMapData hM y) = star (hM x y)

/-- Dual pairing selected by Neukirch's metric-dual formula.

Surjectivity/nondegeneracy of the metric-dual map and the assertion that this
selection is Hermitian and positive are result content. -/
def dualMetricData
    (hM : MetricPairingData R M) :
    MetricPairingData R (Module.Dual R M) :=
  Classical.epsilon (IsDualMetricData hM)

/-- Characterization of the exterior-power metric by the determinant formula
on decomposable elements. -/
def IsExteriorPowerMetricData
    (n : ℕ) (hM : MetricPairingData R M)
    (hExterior : MetricPairingData R (⋀[R]^n M)) : Prop :=
  ∀ x y : Fin n → M,
    hExterior (exteriorPower.ιMulti R n x) (exteriorPower.ιMulti R n y) =
      Matrix.det (fun i j => hM (x i) (y j))

/-- Exterior-power pairing selected by
`⟨x₁∧⋯∧xₙ,y₁∧⋯∧yₙ⟩ = det(⟨xᵢ,yⱼ⟩)`.

This declaration does not prove that the determinant prescription extends to
a Hermitian positive pairing; that is precisely the result-layer obligation
left open by the current complex exterior-power API. -/
def exteriorPowerMetricData
    (n : ℕ) (hM : MetricPairingData R M) :
    MetricPairingData R (⋀[R]^n M) :=
  Classical.epsilon (IsExteriorPowerMetricData n hM)

end LeanCategories.Algebra
