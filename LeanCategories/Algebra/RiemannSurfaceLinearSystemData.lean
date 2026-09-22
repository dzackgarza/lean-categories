/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Definition-level adaptation of work by Rado Kirov, copyright (c) 2026,
released under Apache 2.0 in LeanPool.
-/
module

public import LeanCategories.Algebra.RiemannSurfaceDivisorData
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.Order.Filter.Germ.Basic
public import Mathlib.Topology.DiscreteSubset

/-!
# Riemann--Roch space data on a complex curve

The supporting owner for Peters--Sterk FC11-C16-U031 is LeanPool's
`RS.LinSys` and `RS.l`, not a dimension supplied as an additional input.
The reference is Vilin97/lean-pool at
3fc79f0a795f19fffcc59eee3efaf5faa52de3c3, Apache-2.0,
`LeanPool/JacobianDiffgeo/Meromorphic/{GermSpace,LinearSystem}.lean`.

The reference first takes meromorphic classes in the native codiscrete
germ module, then imposes `-D(p) ≤ ord_p(f)`. This adaptation combines those
two carrier conditions inside the same native ambient module. In particular,
it does not take the dimension of a space of pointwise representatives:
changing finitely many irrelevant values must not create extra sections.
The zero meromorphic germ is included, with order `⊤`.

The submodule is selected by this exact carrier. Closure, representative
independence, the selection specification, finite dimensionality and the
comparison with sheaf cohomology remain result content. No new germ algebra,
quotient framework, module laws, or Riemann--Roch theorem is introduced.
-/

@[expose] public noncomputable section

open scoped Manifold ContDiff

namespace LeanCategories.Algebra

universe u

variable {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X]

/-- A meromorphic representative of a section of `O(D)`: its pole order
at each point is bounded by that point's coefficient in `D`.
The inequality is in `WithTop ℤ`, so it also admits the zero germ. -/
def IsCurveLinearSystemRepresentativeData (D : CurveDivisorData X)
    (f : X → ℂ) : Prop :=
  (∀ p : X, curveMeromorphicAtData f p) ∧
    ∀ p : X,
      ((-FreeAbelianGroup.coeff p D : ℤ) : WithTop ℤ) ≤
        curveOrderAtData p f

/-- The source Riemann--Roch space carrier, with meromorphic
representatives identified in the native codiscrete germ module. -/
def curveLinearSystemCarrierData (D : CurveDivisorData X) :
    Set (Filter.Germ (Filter.codiscrete X) ℂ) :=
  {γ | ∃ f : X → ℂ, IsCurveLinearSystemRepresentativeData D f ∧
    γ = (f : Filter.Germ (Filter.codiscrete X) ℂ)}

/-- The intrinsic carrier condition specifying the subspace `L(D)`. -/
def IsCurveLinearSystemData (D : CurveDivisorData X)
    (L : Submodule ℂ (Filter.Germ (Filter.codiscrete X) ℂ)) : Prop :=
  (L : Set (Filter.Germ (Filter.codiscrete X) ℂ)) =
    curveLinearSystemCarrierData D

variable [T1Space X] [IsManifold 𝓘(ℂ) ω X]

/-- `L(D)`, selected from its source-defined meromorphic germ carrier.
The selection specification and submodule-closure results are not proved here. -/
def curveLinearSystemData (D : CurveDivisorData X) :
    Submodule ℂ (Filter.Germ (Filter.codiscrete X) ℂ) :=
  Classical.epsilon (IsCurveLinearSystemData D)

/-- The source dimension `h⁰(C,D) = l(D)`, computed from `L(D)` rather
than supplied by the caller. As in the reference, `Module.finrank` is total;
finite dimensionality on compact curves is a separate result. -/
def curveSectionDimensionData (D : CurveDivisorData X) : ℕ :=
  Module.finrank ℂ (curveLinearSystemData D)

end LeanCategories.Algebra
