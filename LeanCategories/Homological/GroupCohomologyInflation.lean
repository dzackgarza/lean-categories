/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality

/-!
# Inflation in group cohomology

Serre, *Local Fields*, Chapter VII (FC10-C07-U028).

Pinned Mathlib already contains the exact ingredients of inflation inside
`groupCohomology.H1InfRes`: the quotient homomorphism `G → G/S`, the
quotient representation on `S`-invariants, and generic group-cohomology
functoriality.  This file gives that same map a source-level name in every
nonnegative degree.

Compatibility with connecting morphisms and inflation-restriction exactness
are theorem-layer statements and are not part of this Sweep-III construction.
-/

@[expose] public noncomputable section

namespace LeanCategories.Homological

open CategoryTheory Rep

universe u

variable {k G : Type u} [CommRing k] [Group G]

/-- Serre's inflation map
`H^n(G/S, A^S) → H^n(G, A)` for a normal subgroup `S ≤ G`
(FC10-C07-U028). -/
noncomputable abbrev groupCohomologyInflation
    (A : Rep k G) (S : Subgroup G) [S.Normal] (n : ℕ) :
    groupCohomology (A.quotientToInvariants S) n ⟶ groupCohomology A n :=
  groupCohomology.map (QuotientGroup.mk' S)
    (Rep.ofHom <| A.ρ.quotientToInvariants_lift S) n

end LeanCategories.Homological
