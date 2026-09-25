/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Residue-sum trace data

Definition-level realization of Hartshorne FC06-C03-U107.

For a complete nonsingular curve, Hartshorne's flasque-resolution calculation
presents first cohomology of the differential sheaf as a quotient of the
module of local principal parts.  If

* `δ : Ω → V` is the map from rational differentials to principal parts, and
* `residueSum : V → k` is the sum of the local residue maps,

then the source trace is the map on `V / range δ` whose composite with the
quotient map is `residueSum`.

Constructing that factorization directly with `Submodule.liftQ` would require
the residue theorem as a proof argument.  Sweep III must not prove or import
that result.  This file therefore records the quotient carrier and the exact
factorization graph, then names the source trace by `Classical.epsilon`.

The residue theorem, the fact that the selected trace satisfies the graph, and
the comparison of this quotient model with native sheaf `H^1` are all
result-layer statements.
-/

@[expose] public noncomputable section

namespace LeanCategories.Homological

universe u v w

/-- Algebraic data entering Hartshorne's residue presentation of curve
cohomology.

`Ω` is the rational-differential module and `V` is the direct sum of local
principal-part modules in the source application.  Their geometric
construction and the local residue maps are supplied by the preceding source
results; no such theorem is bundled here. -/
structure ResidueTracePresentationData
    (k : Type u) [Field k]
    (Ω : Type v) [AddCommGroup Ω] [Module k Ω]
    (V : Type w) [AddCommGroup V] [Module k V] where
  principalPartMap : Ω →ₗ[k] V
  residueSum : V →ₗ[k] k

/-- Hartshorne's principal-parts quotient presenting
`H^1(X, Ω_X)`: the cokernel of the rational-differential map, represented
concretely as `V / range δ`.

The theorem identifying this quotient with native sheaf cohomology is not
asserted by this abbreviation. -/
abbrev residueCohomologyQuotientData
    {k : Type u} [Field k]
    {Ω : Type v} [AddCommGroup Ω] [Module k Ω]
    {V : Type w} [AddCommGroup V] [Module k V]
    (D : ResidueTracePresentationData k Ω V) :=
  V ⧸ LinearMap.range D.principalPartMap

/-- The canonical principal-parts map into the residue cohomology quotient. -/
def residueCohomologyQuotientMapData
    {k : Type u} [Field k]
    {Ω : Type v} [AddCommGroup Ω] [Module k Ω]
    {V : Type w} [AddCommGroup V] [Module k V]
    (D : ResidueTracePresentationData k Ω V) :
    V →ₗ[k] residueCohomologyQuotientData D :=
  (LinearMap.range D.principalPartMap).mkQ

/-- Type of a candidate trace on Hartshorne's principal-parts quotient. -/
abbrev DualityTraceFromResiduesHomData
    {k : Type u} [Field k]
    {Ω : Type v} [AddCommGroup Ω] [Module k Ω]
    {V : Type w} [AddCommGroup V] [Module k V]
    (D : ResidueTracePresentationData k Ω V) :=
  residueCohomologyQuotientData D →ₗ[k] k

/-- Exact graph expressing that `trace` is the descent of the sum of local
residues to Hartshorne's principal-parts quotient.

Existence of such a trace is precisely where the residue theorem is used in the
source; Sweep III only records this predicate. -/
def IsDualityTraceFromResiduesData
    {k : Type u} [Field k]
    {Ω : Type v} [AddCommGroup Ω] [Module k Ω]
    {V : Type w} [AddCommGroup V] [Module k V]
    (D : ResidueTracePresentationData k Ω V)
    (trace : DualityTraceFromResiduesHomData D) : Prop :=
  trace.comp (residueCohomologyQuotientMapData D) = D.residueSum

/-- Hartshorne's residue trace, selected from its exact quotient-factorization
graph.

The later theorem layer proves that this selected linear map satisfies
`IsDualityTraceFromResiduesData D`; no residue theorem or quotient-descent
proof is required to name it here. -/
def dualityTraceFromResiduesData
    {k : Type u} [Field k]
    {Ω : Type v} [AddCommGroup Ω] [Module k Ω]
    {V : Type w} [AddCommGroup V] [Module k V]
    (D : ResidueTracePresentationData k Ω V) :
    DualityTraceFromResiduesHomData D :=
  Classical.epsilon (IsDualityTraceFromResiduesData D)

end LeanCategories.Homological
