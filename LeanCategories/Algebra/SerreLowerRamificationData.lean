/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Algebra.SerreFiniteExtensionData

/-!
# Serre lower ramification-group data

Definition-level realization of Serre FC10-C04-U005.

For `i ≥ 0`, Serre's preceding Lemma/Proposition identifies `G_i` with the
automorphisms acting trivially on `A_L / p_L^(i+1)`; `G_{-1}` is the full
Galois group.  In a local extension the unique extended valuation identifies
that Galois group with the decomposition subgroup of its valuation ring.

Sweep III records the literal congruence locus and exact graphs for candidate
subgroups and subgroup-valued families.  Showing that each locus is a normal
subgroup, that the family is decreasing, that `G_0` is inertia, and that the
family is eventually trivial is Proposition 1 (FC10-C04-U004).  The quotient
identification `G/G_0 ≃ Gal(\bar L/\bar K)` is likewise result content.
-/

@[expose] public noncomputable section

namespace LeanCategories.Algebra

universe u v

variable (K : Type u) {L : Type v} [Field K] [Field L] [Algebra K L]

/-- The image in `L` of the `n`-th power of the maximal ideal of a valuation
subring. -/
def valuationMaximalIdealPowerImage
    (B : ValuationSubring L) (n : ℕ) : Set L :=
  (fun b : B => (b : L)) ''
    (((IsLocalRing.maximalIdeal B) ^ n : Ideal B) : Set B)

/-- Serre's raw lower ramification locus.

For every nonnegative integer `i`, this is condition (a) of Lemma 1 written
without a quotient action: `σ(a)-a ∈ p_L^(i+1)` for every integral `a`.
For `i ≤ -1` it is the full decomposition subgroup; the source only uses the
boundary value `i=-1` in this range. -/
def serreLowerRamificationSetData
    (B : ValuationSubring L) (i : ℤ) : Set (B.decompositionSubgroup K) :=
  if i ≤ -1 then
    Set.univ
  else
    {σ | ∀ a : B,
      σ.1 (a : L) - (a : L) ∈
        valuationMaximalIdealPowerImage B (i.toNat + 1)}

/-- Exact graph for the `i`-th ramification group.

Existence of a subgroup with this carrier is exactly the subgroup-closure part
of FC10-C04-U004 and is not assumed by the declaration. -/
def IsSerreLowerRamificationGroupData
    (B : ValuationSubring L) (i : ℤ)
    (H : Subgroup (B.decompositionSubgroup K)) : Prop :=
  (H : Set (B.decompositionSubgroup K)) = serreLowerRamificationSetData K B i

/-- Exact graph for Serre's integer-indexed lower ramification filtration.

The predicate is restricted to the source range `i ≥ -1`; no monotonicity or
normality theorem is included in the data. -/
def IsSerreLowerRamificationFiltrationData
    (B : ValuationSubring L)
    (F : ℤ → Subgroup (B.decompositionSubgroup K)) : Prop :=
  ∀ i : ℤ, -1 ≤ i → IsSerreLowerRamificationGroupData K B i (F i)

end LeanCategories.Algebra
