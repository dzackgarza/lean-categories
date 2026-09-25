/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.AlgebraicGeometry.AlgebraicGroupRankData
public import LeanCategories.AlgebraicGeometry.RadicalData

/-!
# Semisimple and reductive rank data

Definition-level realization of Humphreys FC16-C09-U021.

The source defines semisimple rank as the rank of G/R(G), and reductive rank
as the rank of G/R_u(G).  The present repository does not yet prove that the
relevant fppf quotient sheaves are representable by affine algebraic groups.
That representability statement is result-layer bridge work, not part of the
definition.

Accordingly this file takes the two quotient algebraic groups, together with
a supplied maximal-torus presentation for each quotient, as construction
data.  Once those objects are supplied, both source ranks are exactly the
already-realized algebraic-group rank of the corresponding quotient.
-/

@[expose] public noncomputable section

namespace LeanCategories.AlgebraicGeometry

universe u

/-- Rank presentation for a supplied affine algebraic group: a torus supplied
in the source role of a maximal torus.  Maximality and independence of choice
are result-layer facts, exactly as in FC16-C08-U007. -/
structure MaximalTorusRankPresentationData
    {K : Type u} [Field K] [IsAlgClosed K]
    (Q : AffineAlgebraicGroup K) where
  torus : AffineAlgebraicGroup K
  isTorus : IsTorusData torus

/-- The rank attached to a supplied maximal-torus presentation. -/
noncomputable def rankOfMaximalTorusPresentationData
    {K : Type u} [Field K] [IsAlgClosed K]
    (Q : AffineAlgebraicGroup K)
    (D : MaximalTorusRankPresentationData Q) : WithBot ℕ∞ :=
  algebraicGroupRankFromMaximalTorusData D.torus D.isTorus

/-- Supplied quotient presentations needed for Humphreys' semisimple and
reductive ranks.  The first quotient is to be G/R(G), the second G/R_u(G). -/
structure SemisimpleReductiveRankPresentationData
    (K : Type u) [Field K] [IsAlgClosed K] where
  solvableRadicalQuotient : AffineAlgebraicGroup K
  solvableRadicalQuotientRank :
    MaximalTorusRankPresentationData solvableRadicalQuotient
  unipotentRadicalQuotient : AffineAlgebraicGroup K
  unipotentRadicalQuotientRank :
    MaximalTorusRankPresentationData unipotentRadicalQuotient

/-- Humphreys' semisimple rank rank_s G = rank(G/R(G)), from a supplied
representable quotient presentation. -/
noncomputable def semisimpleRankData
    {K : Type u} [Field K] [IsAlgClosed K]
    (D : SemisimpleReductiveRankPresentationData K) : WithBot ℕ∞ :=
  rankOfMaximalTorusPresentationData
    D.solvableRadicalQuotient D.solvableRadicalQuotientRank

/-- Humphreys' reductive rank rank_red G = rank(G/R_u(G)), from a supplied
representable quotient presentation. -/
noncomputable def reductiveRankData
    {K : Type u} [Field K] [IsAlgClosed K]
    (D : SemisimpleReductiveRankPresentationData K) : WithBot ℕ∞ :=
  rankOfMaximalTorusPresentationData
    D.unipotentRadicalQuotient D.unipotentRadicalQuotientRank

end LeanCategories.AlgebraicGeometry
