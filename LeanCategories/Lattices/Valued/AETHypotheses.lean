/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Lattices.Valued.FanCoarsening
public import LeanCategories.Lattices.Valued.WeylChambers
public import Mathlib.Data.Int.Interval

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Hypothesis interface for AET Proposition 4.17(1) with infinite standard parabolic

Alexeev–Engel–Thompson, arXiv:1903.09742v3, Proposition 4.17(1) states that the Wythoff
chamber `L = ⋃_{h ∈ W_J} h(K)` of Definition 4.16 is the intersection of the active
transformed half-spaces.  The repository theorem
`generalizedChamber_eq_activeHalfspaceIntersection` proves this for a *finite* standard
parabolic `W_J`, because its reflection-descent argument minimizes the height functional
`x ↦ B.form ρ x` over the whole parabolic orbit `W_J • x`, which a finite orbit permits.

This file carries out the hypothesis bookkeeping for the infinite case.  The single
ingredient the finite proof takes from `[Finite (irrelevantReflectionSubgroup P J)]` is that
the part of the parabolic orbit whose height does not exceed the height of the point under
consideration is finite:

`NorthcottHeightFinitenessAt P B J ρ x : {h : W_J | B.form ρ (h • x) ≤ B.form ρ x}.Finite`.

The hypothesis must be *pointwise in `x`*: quantified over all `x` it would be equivalent to
finiteness of `W_J`, since at `x = 0` the set is all of `W_J`.  Pointwise it is exactly the
orbit-level form of the Northcott finiteness argument that the source uses in place of
finiteness of `W_J`: on an integral lattice with hyperbolic invariant form, `ρ` in the open
negative cone of the irrelevant simple coroots and `W` discrete, only finitely many lattice
points have bounded height (AET, proof of Proposition 4.17(1)).  It is *not* the conclusion:
it mentions no cone, no chamber and no half-space, and it is consistent with an infinite
parabolic whose orbit has infinitely many points of unbounded height.

What is proved here:

* `northcottHeightFinitenessAt_of_finite_parabolic`: the finite-parabolic hypothesis of the
  existing theorem implies the pointwise interface hypothesis, so the interface is strictly
  weaker than `[Finite (irrelevantReflectionSubgroup P J)]` and no existing consumer is
  narrowed.
* `exists_minimal_height`: the height-minimizer that the descent argument needs, with no
  finiteness of `W_J` and no finiteness of the orbit.
* `exists_mem_fundamentalChamber_of_mem_activeHalfspaceIntersection`: every point of the
  active half-space intersection outside the chamber lies in some `W_J`-translate of the
  chamber (AET Proposition 4.17(1), reverse inclusion), from the pointwise hypothesis only.
* `generalizedChamber_eq_activeHalfspaceIntersection_of_northcott`: the full statement of
  Proposition 4.17(1) for an arbitrary `Finset` of irrelevant roots `J`, with no finiteness
  of `W_J`; an infinite `W_J` is allowed.
* `convex_generalizedChamber_of_northcott`: convexity of the generalized chamber, the
  Proposition 4.17(1) conclusion.
* `generalizedChamber_smul_mem`, `generalizedChamber_mono`,
  `irrelevantReflectionSubgroup_mono` and `generalizedChamber_eq_iff_covers`: unconditional
  `W_J`-stability and monotonicity of `L`, and the equivalence between the chamber-covering
  property and the half-space description.
* `activeHalfspaceIntersection_eq_iInter`: the half-space description as an intersection
  indexed by the pairs (active simple root, element of `W_J`); a finite intersection exactly
  in the finite-parabolic case, which is the facet presentation needed by a polyhedrality
  argument.
* `generalizedChamber_eq_activeHalfspaceIntersection_of_finite_parabolic`: the existing
  finite-parabolic theorem recovered as a corollary.

## Mirror-arrangement local finiteness

* `mirrorsMeeting`, `MirrorMeetFinite`, `MirrorsLocallyFinite`, `MirrorsLocallyFiniteOn`: the
  standard local-finiteness predicate for a hyperplane arrangement (finitely many distinct
  mirrors meet every test set), bornology and ambient sheet as parameters.
* `mirrorsLocallyFinite_bounded_iff_compact`: the bounded-set equivalence — in a pseudo-metric
  space in which every bounded set sits inside a compact set, local finiteness for bounded sets
  is equivalent to local finiteness for compact sets; `MirrorsLocallyFinite.closedBall` is the
  pointwise consequence, `mirrorsLocallyFinite_of_finite` the trivial end, `mono_born` the
  bornology comparison.
* `aetRootMirrorSet`, `aetRootMirrorSet_locallyFinite`: the root mirrors of a `RootPairing` with
  finite root index set, locally finite in every bornology.
* `weylchamberMirrorSet`, `weylchamberMirrors_locallyFiniteOn_sheet`: the integral-lattice
  discharge, recorded from `WeylChambers.rootMirror_meet_finite` (Bourbaki V §3 no. 1, Lemma 1,
  p. 77) as an instance of `MirrorsLocallyFiniteOn` on the sheet of the positive cone, with
  provenance in the section docstring.

## Positive cone, salience and the semifan consumer

* `AETChamberHypotheses.positiveCone`, `chamber_subset_positiveCone`, `positiveCone_smul_mem`,
  `positiveCone_salient`: AET's positive cone `C`, in which the fundamental chamber is cut out,
  stable under `W_J` and salient.
* `AETChamberHypotheses.generalizedChamber_inter_positiveCone`: Definition 4.16 read with the
  positive cone, `L ∩ C = ⋃_{h ∈ W_J} h(K ∩ C)`;
  `AETChamberHypotheses.generalizedChamber_inter_positiveCone_eq_activeHalfspaces`: Proposition
  4.17(1) relativized to `C`; `AETChamberHypotheses.eq_zero_of_mem_inter_neg`: pointedness from
  salience.
* `aetFundamentalChamberConvexCone`, `aetActiveHalfspaceConvexCone`,
  `AETChamberHypotheses.chamberConvexCone` (`coe_chamberConvexCone`: its carrier is `L`): the
  maximal cone as a `ConvexCone ℝ M`, the shape a `Semifan`/`Fan` consumer takes.
* `image_smul_generalizedChamber_weylGroup`: the maximal cones of the semifan are the
  `W`-translates of `L`, as the identity a cone-family consumer indexes them by.
* `generalizedChamber_eq_activeHalfspaceIntersection_of_subset` and
  `AETChamberHypotheses.of_subset`: with a trivial covering the half-space description holds with
  **no** hypothesis on `W_J` at all, so no finiteness is implied by the conical part of the
  statement; only the Northcott field can carry information about `W_J`.

Nothing here asserts finiteness of `W_J`, finiteness of the cone family, rational finite
generation, or the semifan axioms; those are separate obligations of #24.

## Scope warning

`P.IsRootSystem` is not an instance of `[P.IsCrystallographic] [P.IsReduced]`; but when it is
assumed together with `[Finite ι]`, the Weyl group embeds in `Equiv.Perm ι` and the standard
parabolic is automatically finite (this is proved in the swarm's
`m4/FiniteIndexParabolic.lean`, `finite_irrelevantReflectionSubgroup`).  Consequently the
`Finite W_J`-free statements below exhibit a genuinely new case only in the
`IsRootSystem`-free regime; under `IsRootSystem` the finiteness hypothesis of the pre-existing
theorem `generalizedChamber_eq_activeHalfspaceIntersection` was redundant anyway.  A literal
infinite-parabolic instance must be built outside the finite-index `RootPairing` formalism (for
example from a generalized Cartan matrix), and this file makes no such instance claim.

## Reference

V. Alexeev, P. Engel, A. Thompson, *Stable pair compactification of moduli of K3 surfaces
of degree 2*, arXiv:1903.09742v3, Definition 4.16, Proposition 4.17(1) and (2).

## LC-09 search record

Searches were run with `scripts/formalization_corpus.py search` and `rg` over the repository
and the pinned Mathlib; the queries and hits are recorded in the accompanying `report.md`.
No existing declaration of the pointwise Northcott height finiteness hypothesis or of the
infinite-parabolic case of Proposition 4.17(1) was found.  The reused declarations are those
of `LeanCategories.Lattices.Valued.FanCoarsening` itself
(`generalizedChamber_subset_activeHalfspaceIntersection`, `fundamentalChamber`,
`activeHalfspaceIntersection`, `irrelevantReflectionSubgroup`) together with Mathlib's
`Set.Finite.exists_minimalFor`, `RootPairing.InvariantForm.isOrthogonal_reflection`,
`RootPairing.reflection_apply`, `RootPairing.reflection_same` and
`RootPairing.weylGroup.ofIdx`.
-/

@[expose] public section

namespace LeanCategories.Lattices.Valued

open scoped Pointwise

variable {ι M N : Type*} [DecidableEq ι] [Finite ι]
  [AddCommGroup M] [Module ℝ M] [AddCommGroup N] [Module ℝ N]
  (P : RootPairing ι ℝ M N) [P.IsCrystallographic] [P.IsReduced]
  (b : P.Base) (B : P.InvariantForm) (J : Finset ι)

/-- **Northcott height finiteness at a point.**  Only finitely many elements of the standard
parabolic `W_J` carry a given point `x` to a point whose `ρ`-height does not exceed the height
of `x`.  This is the pointwise form of the Northcott finiteness argument that
Alexeev–Engel–Thompson use in the proof of Proposition 4.17(1) in place of finiteness of `W_J`:
on an integral lattice with hyperbolic invariant form and `ρ` in the open negative cone over
the irrelevant simple coroots, only finitely many lattice points have bounded height.

The hypothesis must be pointwise.  Quantified over every `x` it would be equivalent to
finiteness of `W_J`, since at `x = 0` the set is all of `W_J`; pointwise it holds for an
infinite parabolic as soon as the orbit is infinite with heights tending away from `0`
downwards, which is the situation the source is in.  The statement mentions neither a cone,
nor a chamber, nor a half-space, so it is not the conclusion of Proposition 4.17(1). -/
def NorthcottHeightFinitenessAt (ρ x : M) : Prop :=
  {h : irrelevantReflectionSubgroup P J | B.form ρ (h • x) ≤ B.form ρ x}.Finite

/-- A finite standard parabolic satisfies the pointwise Northcott height finiteness
hypothesis: this is the only use the finite-parabolic proof makes of finiteness. -/
lemma northcottHeightFinitenessAt_of_finite_parabolic
    [Finite (irrelevantReflectionSubgroup P J)] (ρ x : M) :
    NorthcottHeightFinitenessAt P B J ρ x :=
  Set.toFinite _

omit [Finite ι] in
/-- The height minimizer of the reflection-descent argument, from the pointwise Northcott
height finiteness hypothesis alone. -/
lemma exists_minimal_height (ρ : M) {x : M}
    (hfin : NorthcottHeightFinitenessAt P B J ρ x) :
    ∃ h : irrelevantReflectionSubgroup P J,
      ∀ g : irrelevantReflectionSubgroup P J, B.form ρ (h • x) ≤ B.form ρ (g • x) := by
  obtain ⟨h, hmin⟩ := Set.Finite.exists_minimalFor
    (fun h : irrelevantReflectionSubgroup P J ↦ B.form ρ (h • x))
    {h | B.form ρ (h • x) ≤ B.form ρ x} hfin ⟨1, by simp⟩
  refine ⟨h, fun g ↦ ?_⟩
  by_contra hcon
  rw [not_le] at hcon
  have hgs : g ∈ {h : irrelevantReflectionSubgroup P J | B.form ρ (h • x) ≤ B.form ρ x} :=
    le_trans hcon.le hmin.1
  exact absurd (hmin.2 hgs hcon.le) (not_le.mpr hcon)

omit [Finite ι] in
/-- **Reverse inclusion of AET Proposition 4.17(1), pointwise form.**  A point of the
intersection of the active transformed half-spaces which does not already lie in the chamber
is carried into the fundamental chamber by an element of the standard parabolic `W_J`, provided
the height-bounded part of its parabolic orbit is finite.  No finiteness of `W_J` is assumed
and no finiteness of the orbit is assumed. -/
lemma exists_mem_fundamentalChamber_of_mem_activeHalfspaceIntersection
    (ρ : M) (hρ : ∀ j ∈ J, P.toLinearMap.flip (P.coroot j) ρ < 0)
    {x : M} (hx : x ∈ activeHalfspaceIntersection P b B J)
    (hfin : x ∉ fundamentalChamber P b B → NorthcottHeightFinitenessAt P B J ρ x) :
    ∃ h : irrelevantReflectionSubgroup P J, h • x ∈ fundamentalChamber P b B := by
  by_cases hxK : x ∈ fundamentalChamber P b B
  · exact ⟨1, by simpa using hxK⟩
  obtain ⟨h, hmin⟩ := exists_minimal_height P B J ρ (hfin hxK)
  refine ⟨h, fun j hj ↦ ?_⟩
  by_cases hjJ : j ∈ J
  · by_contra hneg
    have hlt : B.form ρ
        ((⟨RootPairing.weylGroup.ofIdx P j * (h : P.weylGroup),
          mul_mem (Subgroup.subset_closure ⟨j, hjJ, rfl⟩) h.property⟩ :
            irrelevantReflectionSubgroup P J) • x) < B.form ρ (h • x) := by
      change B.form ρ
        ((RootPairing.weylGroup.ofIdx P j * (h : P.weylGroup)) • x) < B.form ρ (h • x)
      change B.form ρ (P.reflection j (h • x)) < B.form ρ (h • x)
      have hInv := B.isOrthogonal_reflection j ρ (P.reflection j (h • x))
      rw [P.reflection_same] at hInv
      rw [P.reflection_apply] at hInv
      simp only [LinearMap.map_sub, LinearMap.map_smul, LinearMap.sub_apply,
        LinearMap.smul_apply, smul_eq_mul] at hInv
      have hc : P.toLinearMap.flip (P.coroot j) ρ < 0 := hρ j hjJ
      have hr : B.form (P.root j) (h • x) < 0 := lt_of_not_ge hneg
      nlinarith
    exact absurd (hmin _) (not_le.mpr hlt)
  · exact hx j (Finset.mem_filter.mpr ⟨hj, hjJ⟩) h

/-- The chamber-covering property of the generalized chamber: every point of the active
half-space intersection lies in a `W_J`-translate of the fundamental chamber.  This is the
exact hypothesis AET Proposition 4.17(1) turns into the half-space description. -/
def GeneralizedChamberCovers : Prop :=
  ∀ x ∈ activeHalfspaceIntersection P b B J,
    ∃ h : irrelevantReflectionSubgroup P J, h • x ∈ fundamentalChamber P b B

omit [Finite ι] in
/-- The active half-space description is equivalent to the chamber-covering property, the
forward inclusion being unconditional. -/
lemma generalizedChamber_eq_iff_covers (hJ : J ⊆ b.support) :
    generalizedChamber P b B J = activeHalfspaceIntersection P b B J ↔
      GeneralizedChamberCovers P b B J := by
  constructor
  · intro heq x hx
    have hmem : x ∈ generalizedChamber P b B J := heq ▸ hx
    simp only [generalizedChamber, Set.mem_iUnion, Set.mem_image] at hmem
    obtain ⟨h, y, hy, rfl⟩ := hmem
    exact ⟨(h⁻¹ : irrelevantReflectionSubgroup P J), by simpa using hy⟩
  · intro hcov
    refine Set.Subset.antisymm
      (generalizedChamber_subset_activeHalfspaceIntersection P b B J hJ) ?_
    intro x hx
    obtain ⟨h, hh⟩ := hcov x hx
    exact Set.mem_iUnion.mpr
      ⟨(h⁻¹ : irrelevantReflectionSubgroup P J), h • x, hh, inv_smul_smul h x⟩

omit [Finite ι] in
/-- **Alexeev–Engel–Thompson, Proposition 4.17(1), infinite standard parabolic case.**  The
union of the chambers indexed by the standard parabolic of an arbitrary finite set `J` of
irrelevant simple roots is exactly the intersection of the transformed active half-spaces.
The only hypothesis standing in for finiteness of `W_J` is the pointwise Northcott height
finiteness of the parabolic orbit, required only outside the chamber; `ρ` is a point of the
open negative cone over the irrelevant simple coroots, as in the finite case. -/
theorem generalizedChamber_eq_activeHalfspaceIntersection_of_northcott
    (ρ : M) (hρ : ∀ j ∈ J, P.toLinearMap.flip (P.coroot j) ρ < 0)
    (hfin : ∀ x ∈ activeHalfspaceIntersection P b B J, x ∉ fundamentalChamber P b B →
      NorthcottHeightFinitenessAt P B J ρ x) (hJ : J ⊆ b.support) :
    generalizedChamber P b B J = activeHalfspaceIntersection P b B J :=
  (generalizedChamber_eq_iff_covers P b B J hJ).mpr (fun x hx ↦
    exists_mem_fundamentalChamber_of_mem_activeHalfspaceIntersection P b B J ρ hρ hx
      (hfin x hx))

/-- The existing finite-parabolic theorem is the special case of
`generalizedChamber_eq_activeHalfspaceIntersection_of_northcott` in which the Northcott
hypothesis is discharged by finiteness of `W_J`; no consumer of the finite statement is
narrowed by the interface. -/
theorem generalizedChamber_eq_activeHalfspaceIntersection_of_finite_parabolic
    [Finite (irrelevantReflectionSubgroup P J)] (ρ : M)
    (hρcoroot : ∀ j ∈ J, P.toLinearMap.flip (P.coroot j) ρ < 0) (hJ : J ⊆ b.support) :
    generalizedChamber P b B J = activeHalfspaceIntersection P b B J :=
  generalizedChamber_eq_activeHalfspaceIntersection_of_northcott P b B J ρ hρcoroot
    (fun x _ _ ↦ northcottHeightFinitenessAt_of_finite_parabolic P B J ρ x) hJ

omit [Finite ι] in
/-- `L` is stable under the standard parabolic: it is a union of `W_J`-translates.  No
finiteness of `W_J` is used. -/
lemma generalizedChamber_smul_mem {x : M} (hx : x ∈ generalizedChamber P b B J)
    (g : irrelevantReflectionSubgroup P J) :
    g • x ∈ generalizedChamber P b B J := by
  simp only [generalizedChamber, Set.mem_iUnion, Set.mem_image] at hx ⊢
  obtain ⟨h, y, hy, rfl⟩ := hx
  exact ⟨g * h, y, hy, mul_smul g h y⟩

omit [Finite ι] in
/-- The active half-space intersection is convex: it is cut out by linear inequalities.  No
hypothesis on `W_J` is used. -/
lemma convex_activeHalfspaceIntersection :
    Convex ℝ (activeHalfspaceIntersection P b B J) := by
  intro x hx y hy a b ha hb hab i hi h
  have hx' : 0 ≤ B.form (P.root i) (h • x) := hx i hi h
  have hy' : 0 ≤ B.form (P.root i) (h • y) := hy i hi h
  change 0 ≤ B.form (P.root i) (h • (a • x + b • y))
  rw [show B.form (P.root i) (h • (a • x + b • y)) =
      a * B.form (P.root i) (h • x) + b * B.form (P.root i) (h • y) from by
    change B.form (P.root i) ((h : P.weylGroup) • (a • x + b • y)) =
        a * B.form (P.root i) ((h : P.weylGroup) • x) +
          b * B.form (P.root i) ((h : P.weylGroup) • y)
    rw [eval_root_apply_eq_inv_smul (P := P) (B := B) (i := i) (h := (h : P.weylGroup)),
      eval_root_apply_eq_inv_smul (P := P) (B := B) (i := i) (h := (h : P.weylGroup)) x,
      eval_root_apply_eq_inv_smul (P := P) (B := B) (i := i) (h := (h : P.weylGroup)) y]
    simp only [map_add, map_smul, smul_eq_mul]]
  have h1 : 0 ≤ a * B.form (P.root i) (h • x) := mul_nonneg ha hx'
  have h2 : 0 ≤ b * B.form (P.root i) (h • y) := mul_nonneg hb hy'
  linarith

omit [Finite ι] in
/-- **Convexity of the generalized chamber, AET Proposition 4.17(1), infinite `W_J` case.** -/
theorem convex_generalizedChamber_of_northcott
    (ρ : M) (hρ : ∀ j ∈ J, P.toLinearMap.flip (P.coroot j) ρ < 0)
    (hfin : ∀ x ∈ activeHalfspaceIntersection P b B J, x ∉ fundamentalChamber P b B →
      NorthcottHeightFinitenessAt P B J ρ x) (hJ : J ⊆ b.support) :
    Convex ℝ (generalizedChamber P b B J) := by
  rw [generalizedChamber_eq_activeHalfspaceIntersection_of_northcott P b B J ρ hρ hfin hJ]
  exact convex_activeHalfspaceIntersection P b B J

/-- The active half-space intersection is stable under the standard parabolic: replacing `x` by
`g • x` only composes the quantified `W_J`-element with `g`.  No finiteness of `W_J` is used. -/
lemma activeHalfspaceIntersection_smul_mem {x : M}
    (hx : x ∈ activeHalfspaceIntersection P b B J)
    (g : irrelevantReflectionSubgroup P J) :
    g • x ∈ activeHalfspaceIntersection P b B J := by
  intro i hi h
  have := hx i hi (h * g)
  change 0 ≤ B.form (P.root i) (h • (g • x))
  rw [← mul_smul]
  exact this

omit [Finite ι] in
/-- The standard parabolic is monotone in the set of irrelevant simple roots. -/
lemma irrelevantReflectionSubgroup_mono {J J' : Finset ι} (h : J ⊆ J') :
    irrelevantReflectionSubgroup P J ≤ irrelevantReflectionSubgroup P J' :=
  Subgroup.closure_mono (Set.image_mono (Finset.coe_subset.mpr h))

omit [Finite ι] in
/-- The generalized chamber is monotone in the set of irrelevant simple roots: enlarging the
parabolic enlarges the union of chambers.  No finiteness of `W_J` is used. -/
lemma generalizedChamber_mono {J J' : Finset ι} (h : J ⊆ J') :
    generalizedChamber P b B J ⊆ generalizedChamber P b B J' := by
  intro x hx
  simp only [generalizedChamber, Set.mem_iUnion, Set.mem_image] at hx ⊢
  obtain ⟨k, y, hy, rfl⟩ := hx
  exact ⟨⟨k, irrelevantReflectionSubgroup_mono P h k.property⟩, y, hy, rfl⟩

/-- The active half-space intersection as an intersection of half-spaces indexed by the pairs
consisting of an active simple root and an element of the standard parabolic.  In the
finite-parabolic case this is a finite intersection, i.e. the facet presentation of a
polyhedral cone; in general it is the possibly infinite inequality description. -/
lemma activeHalfspaceIntersection_eq_iInter :
    activeHalfspaceIntersection P b B J =
      ⋂ (i : ι) (_ : i ∈ b.support.filter (fun i ↦ i ∉ J)),
        ⋂ _h : irrelevantReflectionSubgroup P J,
          {x : M | 0 ≤ B.form (P.root i) (_h • x)} := by
  ext x
  simp [activeHalfspaceIntersection]

/-- **Northcott finiteness from a discrete bounded height grid.**  A checkable form of the
pointwise height finiteness hypothesis, matching the source's integrality input: if the heights
of the parabolic orbit lie in an arithmetic progression `t + ℤ·δ` with `δ > 0`, are bounded
below by `t`, and every level is attained finitely often, then only finitely many orbit points
have height at most the height of `x`.  This is the form in which an integral lattice with
`ρ` a lattice vector discharges the hypothesis: heights are integers
(`t = 0`, `δ = 1`). -/
lemma northcottHeightFinitenessAt_of_discrete_bounded {ρ x : M} {t δ : ℝ} (hδ : 0 < δ)
    (hlow : ∀ h : irrelevantReflectionSubgroup P J, t ≤ B.form ρ (h • x))
    (hgrid : ∀ h : irrelevantReflectionSubgroup P J,
      ∃ n : ℤ, B.form ρ (h • x) = t + n * δ)
    (hfib : ∀ s : ℝ, {h : irrelevantReflectionSubgroup P J | B.form ρ (h • x) = s}.Finite) :
    NorthcottHeightFinitenessAt P B J ρ x := by
  obtain ⟨N, hN⟩ := hgrid 1
  have hxN : B.form ρ x = t + N * δ := by simpa using hN
  have hfin : (⋃ (n : ℤ) (_ : n ∈ Finset.Icc (0 : ℤ) N),
      {h : irrelevantReflectionSubgroup P J | B.form ρ (h • x) = t + n * δ}).Finite :=
    Set.Finite.biUnion (Finset.finite_toSet (Finset.Icc (0 : ℤ) N)) (fun n _ ↦ hfib _)
  refine hfin.subset ?_
  intro h hh
  obtain ⟨n, hn⟩ := hgrid h
  have h1 : t ≤ B.form ρ (h • x) := hlow h
  have h2 : B.form ρ (h • x) ≤ B.form ρ x := hh
  have h0 : (0 : ℝ) ≤ δ * (n : ℝ) := by nlinarith
  have hn0R : (0 : ℝ) ≤ (n : ℝ) := nonneg_of_mul_nonneg_right h0 hδ
  have hle : (n : ℝ) * δ ≤ (N : ℝ) * δ := by linarith
  have hnNR : (n : ℝ) ≤ (N : ℝ) := le_of_mul_le_mul_right hle hδ
  have hn0 : (0 : ℤ) ≤ n := by exact_mod_cast hn0R
  have hnN : n ≤ N := by exact_mod_cast hnNR
  exact Set.mem_iUnion₂.mpr ⟨n, Finset.mem_Icc.mpr ⟨hn0, hnN⟩, hn⟩

omit [Finite ι] in
/-- **The AET chamber hypothesis bundle.**  The source-matched hypotheses under which the
half-space description of the generalized chamber is proved here for an arbitrary finite set
`J` of inactive simple roots:

* `rho_neg`: `ρ` lies in the open negative cone over the inactive simple coroots (AET's
  `ρ ∈ interior of K`, i.e. `ρ · r_k > 0` for `k ∈ K`, read with `ρ` negated);
* `J_subset`: the inactive set consists of simple roots;
* `northcott`: the pointwise Northcott height finiteness of the parabolic orbit outside the
  chamber (AET's integrality plus discreteness argument, p. 27);
* `positiveCone`, `chamber_subset_positiveCone`, `positiveCone_smul_mem`,
  `positiveCone_salient`: AET's positive cone `C` of the hyperbolic lattice, in which the
  fundamental chamber is cut out (`K = ⋂_k H⁺_{r_k} ∩ C`), which is stable under the standard
  parabolic and salient (it contains no line).  Salience is what makes the cones pointed, i.e.
  the half of `IsToricCone` that `RationalPolyhedralCone.Fan` requires besides rationality.

None of the numerical fields mentions a cone, a chamber, a half-space or a semifan. -/
structure AETChamberHypotheses where
  /-- A point of the open negative cone over the inactive simple coroots. -/
  rho : M
  /-- The inactive simple coroots pair negatively with `rho`. -/
  rho_neg : ∀ j ∈ J, P.toLinearMap.flip (P.coroot j) rho < 0
  /-- The inactive set consists of simple roots. -/
  J_subset : J ⊆ b.support
  /-- Northcott height finiteness of the parabolic orbit, pointwise outside the chamber. -/
  northcott : ∀ x ∈ activeHalfspaceIntersection P b B J, x ∉ fundamentalChamber P b B →
    NorthcottHeightFinitenessAt P B J rho x
  /-- AET's positive cone `C`. -/
  positiveCone : ConvexCone ℝ M
  /-- AET's chamber is cut out inside the positive cone. -/
  chamber_subset_positiveCone : fundamentalChamber P b B ⊆ (positiveCone : Set M)
  /-- The positive cone is stable under the standard parabolic. -/
  positiveCone_smul_mem : ∀ (h : irrelevantReflectionSubgroup P J) ⦃x : M⦄,
    x ∈ positiveCone → h • x ∈ positiveCone
  /-- The positive cone is salient: it contains no line. -/
  positiveCone_salient : positiveCone.Salient

/-- The source hypotheses from finiteness of the standard parabolic (the form in which the
pre-existing repository theorem `generalizedChamber_eq_activeHalfspaceIntersection` supplies
the height input), together with the positive-cone data. -/
noncomputable def AETChamberHypotheses.of_finiteParabolic
    [Finite (irrelevantReflectionSubgroup P J)] (ρ : M)
    (hρ : ∀ j ∈ J, P.toLinearMap.flip (P.coroot j) ρ < 0) (hJ : J ⊆ b.support)
    (C : ConvexCone ℝ M) (hKC : fundamentalChamber P b B ⊆ (C : Set M))
    (hCstable : ∀ (h : irrelevantReflectionSubgroup P J) ⦃x : M⦄, x ∈ C → h • x ∈ C)
    (hsal : C.Salient) :
    AETChamberHypotheses P b B J where
  rho := ρ
  rho_neg := hρ
  J_subset := hJ
  northcott := fun x _ _ ↦ northcottHeightFinitenessAt_of_finite_parabolic P B J ρ x
  positiveCone := C
  chamber_subset_positiveCone := hKC
  positiveCone_smul_mem := hCstable
  positiveCone_salient := hsal

/-- The bundle assembled with a **vacuous** Northcott field: when every point of the active
half-space intersection already lies in the fundamental chamber, the covering is trivial, the
height descent is never invoked, and no finiteness of `W_J` enters anywhere.  This separates the
finiteness assumption from the conical part of Proposition 4.17(1); the only field of the bundle
that can force information about `W_J` is `northcott`. -/
noncomputable def AETChamberHypotheses.of_subset (ρ : M)
    (hρ : ∀ j ∈ J, P.toLinearMap.flip (P.coroot j) ρ < 0) (hJ : J ⊆ b.support)
    (hsub : activeHalfspaceIntersection P b B J ⊆ fundamentalChamber P b B)
    (C : ConvexCone ℝ M) (hKC : fundamentalChamber P b B ⊆ (C : Set M))
    (hCstable : ∀ (h : irrelevantReflectionSubgroup P J) ⦃x : M⦄, x ∈ C → h • x ∈ C)
    (hsal : C.Salient) :
    AETChamberHypotheses P b B J where
  rho := ρ
  rho_neg := hρ
  J_subset := hJ
  northcott := fun _ hx hxK ↦ absurd (hsub hx) hxK
  positiveCone := C
  chamber_subset_positiveCone := hKC
  positiveCone_smul_mem := hCstable
  positiveCone_salient := hsal

omit [Finite ι] in
/-- **Alexeev–Engel–Thompson, Proposition 4.17(1), from the hypothesis bundle**, for an
arbitrary finite set `J` of inactive simple roots and an arbitrary standard parabolic `W_J`. -/
theorem generalizedChamber_eq_activeHalfspaceIntersection_of_hypotheses
    (H : AETChamberHypotheses P b B J) :
    generalizedChamber P b B J = activeHalfspaceIntersection P b B J :=
  generalizedChamber_eq_activeHalfspaceIntersection_of_northcott P b B J H.rho H.rho_neg
    H.northcott H.J_subset

omit [Finite ι] in
/-- **Convexity of the generalized chamber from the hypothesis bundle** (AET Proposition
4.17(1): "In particular, `L` is convex"). -/
theorem convex_generalizedChamber_of_hypotheses (H : AETChamberHypotheses P b B J) :
    Convex ℝ (generalizedChamber P b B J) :=
  by
  rw [generalizedChamber_eq_activeHalfspaceIntersection_of_hypotheses P b B J H]
  exact convex_activeHalfspaceIntersection P b B J

/-! ## Local finiteness of a mirror arrangement

AET Proposition 4.17(1) asserts that the generalized chamber is convex *and locally finite*.  The
predicate formalized here is the standard one for a hyperplane arrangement in a bornological
ambient space: only finitely many distinct mirrors meet each test set.  Nothing about a cone, a
chamber or a semifan enters, so the predicate cannot be mistaken for (or assumed to be) the
conclusion of Proposition 4.17(1). -/

section MirrorArrangement

variable {E : Type*}

/-- The mirrors of the arrangement `𝓗` which meet the set `s`. -/
def mirrorsMeeting (𝓗 : Set (Set E)) (s : Set E) : Set (Set E) :=
  {H ∈ 𝓗 | (H ∩ s).Nonempty}

/-- Only finitely many mirrors of the arrangement `𝓗` meet the set `s`. -/
def MirrorMeetFinite (𝓗 : Set (Set E)) (s : Set E) : Prop := (mirrorsMeeting 𝓗 s).Finite

/-- **Local finiteness of a mirror arrangement**: finitely many distinct mirrors meet every
`Born`-set.  The bornology is a parameter so that the same predicate covers bounded sets,
compact sets and the relative version on a sheet of the positive cone. -/
def MirrorsLocallyFinite (𝓗 : Set (Set E)) (Born : Set E → Prop) : Prop :=
  ∀ s, Born s → MirrorMeetFinite 𝓗 s

/-- Local finiteness relative to a subset `U`, the form in which the integral-lattice theorem
`WeylChambers.rootMirror_meet_finite` is available (Bourbaki's lemma is stated for compact
subsets of the chosen sheet of the positive cone). -/
def MirrorsLocallyFiniteOn (𝓗 : Set (Set E)) (U : Set E) (Born : Set E → Prop) : Prop :=
  ∀ s, Born s → s ⊆ U → MirrorMeetFinite 𝓗 s

theorem mirrorsMeeting_mono {𝓗 𝓗' : Set (Set E)} (h : 𝓗' ⊆ 𝓗) (s : Set E) :
    mirrorsMeeting 𝓗' s ⊆ mirrorsMeeting 𝓗 s :=
  fun _ hH ↦ ⟨h hH.1, hH.2⟩

theorem MirrorMeetFinite.mono {𝓗 𝓗' : Set (Set E)} {s : Set E}
    (h : MirrorMeetFinite 𝓗 s) (hsub : 𝓗' ⊆ 𝓗) : MirrorMeetFinite 𝓗' s :=
  h.subset (mirrorsMeeting_mono hsub s)

theorem MirrorMeetFinite.mono_set {𝓗 : Set (Set E)} {s t : Set E}
    (h : MirrorMeetFinite 𝓗 s) (hsub : t ⊆ s) : MirrorMeetFinite 𝓗 t := by
  refine h.subset ?_
  rintro _ ⟨hH, x, hxH, hxt⟩
  exact ⟨hH, x, hxH, hsub hxt⟩

theorem MirrorsLocallyFinite.mono {𝓗 𝓗' : Set (Set E)} {Born : Set E → Prop}
    (h : MirrorsLocallyFinite 𝓗 Born) (hsub : 𝓗' ⊆ 𝓗) : MirrorsLocallyFinite 𝓗' Born :=
  fun s hs ↦ (h s hs).mono hsub

theorem MirrorsLocallyFiniteOn.mono {𝓗 𝓗' : Set (Set E)} {U : Set E} {Born : Set E → Prop}
    (h : MirrorsLocallyFiniteOn 𝓗 U Born) (hsub : 𝓗' ⊆ 𝓗) :
    MirrorsLocallyFiniteOn 𝓗' U Born :=
  fun s hs hsU ↦ (h s hs hsU).mono hsub

theorem MirrorsLocallyFinite.mono_born {𝓗 : Set (Set E)} {Born Born' : Set E → Prop}
    (h : MirrorsLocallyFinite 𝓗 Born) (hle : ∀ s, Born' s → Born s) :
    MirrorsLocallyFinite 𝓗 Born' :=
  fun s hs ↦ h s (hle s hs)

/-- A finite arrangement is locally finite for every bornology. -/
theorem mirrorsLocallyFinite_of_finite {𝓗 : Set (Set E)} (h : 𝓗.Finite)
    (Born : Set E → Prop) : MirrorsLocallyFinite 𝓗 Born :=
  fun _ _ ↦ h.subset fun _ hH ↦ hH.1

/-- **The bounded-set equivalence.**  In a pseudo-metric space in which every bounded set is
contained in a compact set (in particular in finite-dimensional real vector spaces, the AET
setting), finitely many mirrors meeting every *bounded* set is equivalent to finitely many
mirrors meeting every *compact* set. -/
theorem mirrorsLocallyFinite_bounded_iff_compact [PseudoMetricSpace E]
    (hbdd : ∀ s : Set E, Bornology.IsBounded s → ∃ K : Set E, IsCompact K ∧ s ⊆ K)
    {𝓗 : Set (Set E)} :
    MirrorsLocallyFinite 𝓗 (fun s ↦ Bornology.IsBounded s) ↔
      MirrorsLocallyFinite 𝓗 IsCompact := by
  constructor
  · intro h s hs
    exact h s hs.isBounded
  · intro h s hs
    obtain ⟨K, hK, hsK⟩ := hbdd s hs
    exact (h K hK).mono_set hsK

/-- Pointwise consequence: only finitely many mirrors meet a closed ball. -/
theorem MirrorsLocallyFinite.closedBall [PseudoMetricSpace E] {𝓗 : Set (Set E)}
    (h : MirrorsLocallyFinite 𝓗 (fun s ↦ Bornology.IsBounded s)) (x : E) (r : ℝ) :
    MirrorMeetFinite 𝓗 (Metric.closedBall x r) :=
  h _ Metric.isBounded_closedBall

end MirrorArrangement

/-! ## The root mirrors of a root pairing

For a `RootPairing` with finite root index set the arrangement has finitely many mirrors, so it is
locally finite for every bornology; this is the degenerate end of the scale, and it is recorded so
that the predicate is visibly non-vacuous.  The mathematically substantive discharge is the
integral-lattice one in the next section. -/

section RootPairingMirrors

variable {ι M N : Type*} [DecidableEq ι] [Finite ι]
  [AddCommGroup M] [Module ℝ M] [AddCommGroup N] [Module ℝ N]
  (P : RootPairing ι ℝ M N) (B : P.InvariantForm)

/-- The mirror of the `i`-th root: the `B`-orthogonal hyperplane. -/
def aetRootMirror (i : ι) : Set M :=
  {x | B.form (P.root i) x = 0}

/-- The mirror arrangement of the simple roots, as a set of hyperplanes. -/
def aetRootMirrorSet : Set (Set M) :=
  {H | ∃ i : ι, H = aetRootMirror P B i}

theorem aetRootMirrorSet_finite : (aetRootMirrorSet P B).Finite :=
  (Set.finite_range (aetRootMirror P B)).subset fun _ hH ↦ by
    obtain ⟨i, rfl⟩ := hH
    exact ⟨i, rfl⟩

/-- With finitely many roots the arrangement is locally finite in every bornology. -/
theorem aetRootMirrorSet_locallyFinite (Born : Set M → Prop) :
    MirrorsLocallyFinite (aetRootMirrorSet P B) Born :=
  mirrorsLocallyFinite_of_finite (aetRootMirrorSet_finite P B) Born

end RootPairingMirrors

/-! ## Integral-lattice discharge of the local-finiteness predicate

`LeanCategories/Lattices/Valued/WeylChambers.lean` proves Bourbaki's lemma (Ch. V §3 no. 1,
Lemma 1, p. 77) as `rootMirror_meet_finite`: only finitely many root mirrors meet a compact
subset of the chosen sheet of the positive cone of a Lorentzian lattice.  That theorem is stated
for the `IntegralLatticeCat`/`realForm` carriers, not for `RootPairing`; the port below states it
as an instance of `MirrorsLocallyFiniteOn` for the mirror arrangement of the negative reflective
roots, which is the hypothesis a local-finiteness argument for the AET semifan consumes.

Provenance: `LeanCategories/Lattices/Valued/WeylChambers.lean`, theorem
`rootMirror_meet_finite` (repository #129), together with `negativeReflectiveRoots`,
`rootMirror`, `realForm`, `realFormQuadratic`, `sigPos` and `positiveCone.upper` from the same
file; the file's own provenance records Bourbaki, *Groupes et algèbres de Lie*, Ch. V §3 no. 1,
Lemma 1, p. 77, and the repository's `realFormOrthogonal_finite_of_compact` (#128).  Both files
are Apache 2.0, © Dzack Garza. -/

section IntegralLatticeMirrors

variable (L : FiniteProjectiveLatticeCat ℤ ℤ)

/-- The mirror arrangement of the negative reflective roots of an integral lattice, as a set of
hyperplanes of the real form. -/
def weylchamberMirrorSet : Set (Set (realForm L).obj.carrier) :=
  {H | ∃ r ∈ negativeReflectiveRoots L, rootMirror L r = H}

/-- **Bourbaki's local finiteness, as an instance of `MirrorsLocallyFiniteOn`.**  For a
nondegenerate Lorentzian integral lattice with `sigPos = 1`, a point `t` of positive square and a
`ℤ`-basis of the lattice, only finitely many mirrors of negative reflective roots meet a compact
subset of the sheet `positiveCone.upper t`.  No finiteness of any reflection group or of a
standard parabolic is involved: the finiteness comes from compactness of the set of reflections
moving a compact set into itself (`realFormOrthogonal_finite_of_compact`). -/
theorem weylchamberMirrors_locallyFiniteOn_sheet
    (hL : L.obj.obj.IsNondegenerate) (h2 : IsRegular (2 : ℤ))
    (hpos : sigPos (realFormQuadratic L) = 1)
    (t : (realForm L).obj.carrier) (ht : 0 < realFormQuadratic L t)
    {I : Type} [Fintype I] [DecidableEq I] (i₀ : I) (b : Module.Basis I ℤ L.obj.obj.carrier) :
    MirrorsLocallyFiniteOn (weylchamberMirrorSet L)
      (positiveCone.upper (realFormQuadratic L) t) IsCompact := by
  intro s hscomp hs
  rcases s.eq_empty_or_nonempty with rfl | hne
  · simp [MirrorMeetFinite, mirrorsMeeting]
  · refine (rootMirror_meet_finite L hL h2 hpos t ht hscomp hne hs i₀ b).subset ?_
    rintro H ⟨⟨r, hr, rfl⟩, hH⟩
    exact ⟨r, hr, rfl, hH⟩

end IntegralLatticeMirrors

/-! ## The positive cone, salience, and the semifan consumer -/

section PositiveCone

variable {ι M N : Type*} [DecidableEq ι] [Finite ι]
  [AddCommGroup M] [Module ℝ M] [AddCommGroup N] [Module ℝ N]
  (P : RootPairing ι ℝ M N) [P.IsCrystallographic] [P.IsReduced]
  (b : P.Base) (B : P.InvariantForm) (J : Finset ι)

omit [Finite ι] in
/-- The fundamental chamber as a convex cone. -/
noncomputable def aetFundamentalChamberConvexCone : ConvexCone ℝ M where
  carrier := fundamentalChamber P b B
  smul_mem' := by
    intro c hc x hx i hi
    have h := hx i hi
    change 0 ≤ B.form (P.root i) (c • x)
    rw [map_smul, smul_eq_mul]
    exact mul_nonneg hc.le h
  add_mem' := by
    intro x hx y hy i hi
    have h1 := hx i hi
    have h2 := hy i hi
    change 0 ≤ B.form (P.root i) (x + y)
    rw [map_add]
    exact add_nonneg h1 h2

@[simp] theorem coe_aetFundamentalChamberConvexCone :
    (aetFundamentalChamberConvexCone P b B : Set M) = fundamentalChamber P b B := rfl

omit [Finite ι] in
/-- The active half-space cone of AET Proposition 4.17(1) as a convex cone. -/
noncomputable def aetActiveHalfspaceConvexCone : ConvexCone ℝ M where
  carrier := activeHalfspaceIntersection P b B J
  smul_mem' := by
    intro c hc x hx i hi g
    have h := hx i hi g
    have hval : B.form (P.root i) (g • (c • x)) = c * B.form (P.root i) (g • x) := by
      rw [show g • (c • x) = c • (g • x) from smul_comm ((g : P.weylGroup) : P.Aut) c x,
        map_smul, smul_eq_mul]
    change 0 ≤ B.form (P.root i) (g • (c • x))
    rw [hval]
    exact mul_nonneg hc.le h
  add_mem' := by
    intro x hx y hy i hi g
    have h1 := hx i hi g
    have h2 := hy i hi g
    have hval : B.form (P.root i) (g • (x + y)) = B.form (P.root i) (g • x)
        + B.form (P.root i) (g • y) := by
      rw [show g • (x + y) = g • x + g • y from smul_add g x y, map_add]
    change 0 ≤ B.form (P.root i) (g • (x + y))
    rw [hval]
    exact add_nonneg h1 h2

@[simp] theorem coe_aetActiveHalfspaceConvexCone :
    (aetActiveHalfspaceConvexCone P b B J : Set M) =
      activeHalfspaceIntersection P b B J := rfl

/-- **The generalized chamber as a convex cone**, i.e. the maximal cone `L` of the semifan that a
`Semifan`/`ConvexCone`-based consumer receives.  Its carrier is the active half-space
intersection, which equals `L` by `AETChamberHypotheses.coe_chamberConvexCone`. -/
noncomputable def AETChamberHypotheses.chamberConvexCone
    (_H : AETChamberHypotheses P b B J) : ConvexCone ℝ M :=
  aetActiveHalfspaceConvexCone P b B J

/-- The carrier of `chamberConvexCone` is the generalized chamber `L` itself. -/
theorem AETChamberHypotheses.coe_chamberConvexCone
    (H : AETChamberHypotheses P b B J) :
    (H.chamberConvexCone P b B J : Set M) = generalizedChamber P b B J := by
  rw [AETChamberHypotheses.chamberConvexCone, coe_aetActiveHalfspaceConvexCone,
    generalizedChamber_eq_activeHalfspaceIntersection_of_hypotheses P b B J H]

/-- **AET Definition 4.16 with the positive cone**: the chamber is cut out inside `C`, so
`L ∩ C` is the union of the `W_J`-translates of `K ∩ C`. -/
theorem AETChamberHypotheses.generalizedChamber_inter_positiveCone
    (H : AETChamberHypotheses P b B J) :
    generalizedChamber P b B J ∩ (H.positiveCone : Set M) =
      ⋃ h : irrelevantReflectionSubgroup P J,
        (fun x ↦ h • x) ''
          (fundamentalChamber P b B ∩ (H.positiveCone : Set M)) := by
  rw [generalizedChamber]
  ext x
  simp only [Set.mem_inter_iff, Set.mem_iUnion, Set.mem_image]
  constructor
  · rintro ⟨⟨h, y, hyK, rfl⟩, hxC⟩
    refine ⟨h, y, ⟨hyK, ?_⟩, rfl⟩
    have := H.positiveCone_smul_mem (h⁻¹) hxC
    simpa using this
  · rintro ⟨h, y, ⟨hyK, hyC⟩, rfl⟩
    exact ⟨⟨h, y, hyK, rfl⟩, H.positiveCone_smul_mem h hyC⟩

/-- **AET Proposition 4.17(1) inside the positive cone**: `L ∩ C` is the intersection of the
transformed active half-spaces with `C`. -/
theorem AETChamberHypotheses.generalizedChamber_inter_positiveCone_eq_activeHalfspaces
    (H : AETChamberHypotheses P b B J) :
    generalizedChamber P b B J ∩ (H.positiveCone : Set M) =
      activeHalfspaceIntersection P b B J ∩ (H.positiveCone : Set M) := by
  rw [generalizedChamber_eq_activeHalfspaceIntersection_of_hypotheses P b B J H]

/-- Salience of the positive cone: a point of the chamber lying in `C` together with its negative
is zero.  This is the pointedness input a toric-cone consumer needs. -/
theorem AETChamberHypotheses.eq_zero_of_mem_inter_neg
    (H : AETChamberHypotheses P b B J) {x : M}
    (hx : x ∈ fundamentalChamber P b B ∩ (H.positiveCone : Set M))
    (hx' : -x ∈ fundamentalChamber P b B ∩ (H.positiveCone : Set M)) : x = 0 := by
  by_contra hne
  exact H.positiveCone_salient x hx.2 hne hx'.2

/-- The maximal cones of the semifan are the `W`-translates of `L`: the definitional identity a
`Semifan` consumer uses to index them (`m8`'s `wythoffConeSets`, `m7`'s `semifanCone`). -/
theorem image_smul_generalizedChamber_weylGroup (g : P.weylGroup) :
    (fun x ↦ g • x) '' generalizedChamber P b B J =
      ⋃ h : irrelevantReflectionSubgroup P J,
        (fun y ↦ (g * (h : P.weylGroup)) • y) '' fundamentalChamber P b B := by
  rw [generalizedChamber, Set.image_iUnion]
  refine Set.iUnion_congr fun h ↦ ?_
  ext z
  simp only [Set.mem_image]
  constructor
  · rintro ⟨a, ⟨b, hb, rfl⟩, rfl⟩
    exact ⟨b, hb, (mul_smul g (h : P.weylGroup) b).symm⟩
  · rintro ⟨b, hb, rfl⟩
    exact ⟨_, ⟨b, hb, rfl⟩, mul_smul g (h : P.weylGroup) b⟩

end PositiveCone

/-- **Where no finiteness of `W_J` is needed at all.**  If every point of the active half-space
intersection already lies in the fundamental chamber, then the generalized chamber is that
intersection with no hypothesis on `W_J` whatsoever: the covering of AET Proposition 4.17(1) is
trivial and the height descent is not invoked.  In particular this shows that the finiteness of
`W_J` occurring in the pre-existing theorem is not implied by the conical part of the statement;
the only place finiteness can enter is the Northcott height field. -/
theorem generalizedChamber_eq_activeHalfspaceIntersection_of_subset
    (hJ : J ⊆ b.support)
    (hsub : activeHalfspaceIntersection P b B J ⊆ fundamentalChamber P b B) :
    generalizedChamber P b B J = activeHalfspaceIntersection P b B J :=
  Set.Subset.antisymm (generalizedChamber_subset_activeHalfspaceIntersection P b B J hJ)
    fun x hx ↦ Set.mem_iUnion.mpr ⟨1, x, hsub hx, one_smul _ _⟩

end LeanCategories.Lattices.Valued
