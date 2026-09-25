/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Topology.LocalHomology
public import Mathlib.Data.PNat.Basic
public import Mathlib.Topology.Instances.AddCircle.Defs

/-!
# Singular linking-number data

Definition-level realization of Peters--Sterk FC11-C04-U044.

For torsion one-cycles `γ, γ'`, the source chooses a positive integer `t`,
a two-chain `Σ` with boundary `tγ`, and a transverse representative `γ'`.
Its linking number is the class of `(Σ · γ') / t` in `ℚ / ℤ`.

Mathlib currently has no manifold-chain transversality/intersection-number API,
so the geometric transversality predicate and integer intersection operation are
parameters of the representative-level datum below.  Sweep III records the
source construction and formula only.  Independence of representatives and
bounding chain, and hence descent to torsion homology classes, are result-layer
statements.
-/

@[expose] public noncomputable section

open AlgebraicTopology CategoryTheory

namespace LeanCategories.Topology

variable (X : Type) [TopologicalSpace X]

/-- Integral singular chains in degree `n`. -/
abbrev IntegralSingularChain (n : ℕ) : Type :=
  ((singularChainFunctor ℤ).obj (TopCat.of X)).X n

/-- The singular boundary on integral chains. -/
def integralSingularBoundary {n : ℕ} :
    IntegralSingularChain X (n + 1) →+ IntegralSingularChain X n :=
  (((singularChainFunctor ℤ).obj (TopCat.of X)).d (n + 1) n).hom.toAddMonoidHom

/-- A degree-one integral singular cycle. -/
def IsIntegralSingularOneCycle (γ : IntegralSingularChain X 1) : Prop :=
  integralSingularBoundary X γ = 0

/-- Geometric input for an oriented intersection number between singular
chains in prescribed degrees. Mathlib does not currently supply the
manifold-chain transversality layer, so Sweep III keeps that geometric
operation explicit and uses it only through source formulas. -/
structure SingularChainIntersectionDataInDegrees (p q : ℕ) where
  Transverse : IntegralSingularChain X p → IntegralSingularChain X q → Prop
  intersectionNumber :
    ∀ sigma gamma, Transverse sigma gamma → ℤ

/-- The degree-(2,1) specialization used by the linking-number construction. -/
abbrev SingularChainIntersectionData :=
  SingularChainIntersectionDataInDegrees X 2 1

/-- Representative data entering the chain-level definition of a linking
number.  The proof-valued fields state the hypotheses of the source
construction; no instance of this structure is constructed in Sweep III. -/
structure SingularLinkingRepresentativeData
    (I : SingularChainIntersectionData X) where
  torsionOrder : ℕ+
  γ : IntegralSingularChain X 1
  γ' : IntegralSingularChain X 1
  isCycle_γ : IsIntegralSingularOneCycle X γ
  isCycle_γ' : IsIntegralSingularOneCycle X γ'
  boundingChain : IntegralSingularChain X 2
  boundary_boundingChain :
    integralSingularBoundary X boundingChain = (torsionOrder : ℕ) • γ
  transverse : I.Transverse boundingChain γ'

/-- The representative-level linking value `(Σ · γ') / t` in `ℚ / ℤ`.

The statement that this value depends only on the two torsion homology classes
is deliberately not part of this definition. -/
def singularLinkingRepresentativeValue
    (I : SingularChainIntersectionData X)
    (d : SingularLinkingRepresentativeData X I) : AddCircle (1 : ℚ) :=
  (((I.intersectionNumber d.boundingChain d.γ' d.transverse : ℚ) /
    (d.torsionOrder : ℚ) : ℚ) : AddCircle (1 : ℚ))

end LeanCategories.Topology
