/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Lattices.Valued.ConicalMember
public import LeanCategories.Lattices.Valued.Semifan

/-!
# Admissible members as cones of the conical locus

E. Looijenga, *Compactifications defined by arrangements II: the locally symmetric varieties of
type IV*, arXiv math/0201218v2 (2002), text version `.tmp-sources/looijenga-math0201218v2.md`:
Definition 2.1,
p. 10 (text line 279, the conical locus as the union of the cones `C_I` over the `ℚ`-isotropic
subspaces `I`), Definition 6.1, p. 28 (text line 769, admissible decompositions, the `Σ`-support
space `V_σ` in its two cases, the isotropic centre `I(σ) = V_σ ∩ V_σ^⊥`) and Example 6.2, p. 29
(text line 783, the Baily–Borel decomposition, "the support spaces are `{0}` and the orthogonal
complements of the nontrivial `ℚ`-isotropic subspaces").

`ConicalMember` carries the three shapes of a member of the conical locus, and
`ConicalMember.vSigma`/`isotropicCenter` the two cases of Definition 6.1. This file makes that
member-level assignment usable as the source intends it (lean-categories#166).

* **The two degenerate shapes of Definition 6.1 (i) are reconciled and excluded**
  (`IsCaseIFibre`). The zero member of a fibre *is* the apex `C_{{0}}` of Definition 2.1 — the same
  point `{0}` of `⋀²V(ℝ)` (`ConicalMember.carrier_fibre_bot`) — so it carries the apex's support
  space `{0}`, not the `lineSpan F` the span formula returns at `σ = ⊥`
  (`ConicalMember.vSigma_fibre_bot_eq_zero`, `ConicalMember.fibreVSigma`). An isotropic half line is
  not a case-(i) member (`not_isCaseIFibre_isotropicHalfLine`): the span formula applied to it
  returns the *plane* (`vSigma_fibreRay_eq_realify_plane`), whereas the support space the source
  assigns it is the one Definition 6.1 (ii) gives the plane
  (`ConicalMember.vSigma_plane_bailyBorel`, the orthogonal complement of the plane).
* **The members of a decomposition are cones of the conical locus, with distinct roles**
  (`memberSet`, `conicalLocusClosedSet`): the open stratum `C_I` is blunt
  (`zero_not_mem_openStratum`), the pointed cone `C_I⁺ = PointedCone.hull C_I` is the role
  Definition 2.1 carries into `⋀²V(ℝ)`, and the members of a decomposition of `C_{I,+}` are closed
  cones inside its rational closure, whose carriers lie in the closed conical locus
  (`member_carrier_subset_closedSet`).
* **Presentations**: a plane's carrier does not depend on the witnessing line
  (`ConicalMember.carrier_plane_eq_of_witness_member`), nor its support space
  (`ConicalMember.vSigma_plane_witness`, Condition (ii)); the fibre's line is a presentation-free
  part of the support space (`lineSpan_eq_of_line_eq`); and a negated generator carries the
  *antipodal* set (`wedgeLeft_neg`), which is not identified with the carrier of the opposite
  orientation.
* **The Baily–Borel decomposition at this object**: its supports are `{0}`, `I^⊥` and `J^⊥` in the
  source's cases (`ConicalMember.vSigma_fibre_closure`,
  `ConicalMember.vSigma_plane_bailyBorel`) and its isotropic centres are exactly `{0}`, `I` and `J`
  (`ConicalMember.isotropicCenter_fibre_closure`,
  `ConicalMember.isotropicCenter_plane_bailyBorel`), by nondegeneracy and the double orthogonal
  complement.

## LC-09 search record (2026-11-21)

`content:semifan` and `content:IsIsotropicHalfLine` found no file. `content:conical locus member
support space` found only Mathlib's own import list, and `content:isotropic center` only the centre
of a Clifford algebra (TauCeti, `TauCeti/LinearAlgebra/CliffordAlgebra/Center.lean`), unrelated.
`content:double orthogonal complement nondegenerate` and `content:orthogonal_orthogonal` return
Mathlib's `LinearMap.BilinForm.orthogonal_orthogonal` — used directly here, and by atlas-lean's
`LinearCode.dual_dual` — which is the lemma the exactness of `I(C_{I,+})` consumes. Nothing in the
corpus formalises Looijenga's conical locus, its members or their support spaces, so the
declarations below are new rather than ported; the existing whole-fibre support lemmas
(`ConicalLine.vSigma_closure_eq_ker`, `Semifan.vSigmaPlane_eq_ker_inf_ker`,
`ConicalMember.carrier_plane_eq_of_witness`) are the inputs.

## Scope

`ConicalLocus.vSigma` and `Semifan.vSigmaPlane_le_of_refines` are Definition 6.1 (i)'s span formula
and the case-(ii) space; neither is asserted here for the other case. The member-level support
`ConicalMember.fibreVSigma` carries the reconciliation of item 2 above. What is *not* formalised
here is recorded in the docstring of `wedgeLeft_neg`: a plane with the opposite orientation
(`ConicalPlane` with the basis in the other order) would contribute the antipodal half line, and the
identification of that carrier needs the vanishing of `x ↦ x ∧ a` on a line, which is not available.
-/

@[expose] public section

open PointedCone QuadraticMap

open scoped TensorProduct

namespace LeanCategories.Lattices.Valued

variable {V : Type} [AddCommGroup V] [Module ℚ V] [Module.Finite ℚ V]
variable {BQ : LinearMap.BilinForm ℚ V} {Q : QuadraticForm ℝ (realified V)}

/-! ## Case (i) of Definition 6.1 and its two degenerate shapes -/

/-- **Definition 6.1 (i)'s shape** (Looijenga, Definition 6.1, p. 28): a member of the fibre of a
`ℚ`-isotropic line to which the source assigns the span formula for `V_σ`. The source's case (i) is
"if `σ` lies in `C_{I,+}` ... but is not an isotropic half-line"; the zero member of a fibre is
not a member of the conical locus at that fibre at all, being the apex `C_{{0}}` of Definition 2.1
and carried to the same point `{0}` of `⋀²V(ℝ)` as `ConicalMember.zero`
(`ConicalMember.carrier_fibre_bot`). Both shapes are excluded here, which is what lets a carrier
determine its support space. -/
def IsCaseIFibre (F : ConicalLine BQ Q) (σ : PointedCone ℝ (realified ↥F.space)) : Prop :=
  σ ≠ ⊥ ∧ ¬ IsIsotropicHalfLine (fibreForm Q F.space) σ

omit [Module.Finite ℚ V] in
/-- The zero member of a fibre is not a case-(i) member: it is the apex. -/
theorem not_isCaseIFibre_bot (F : ConicalLine BQ Q) :
    ¬ IsCaseIFibre F (⊥ : PointedCone ℝ (realified ↥F.space)) :=
  fun h => h.1 rfl

omit [Module.Finite ℚ V] in
/-- **Isotropic half lines are routed through Definition 6.1 (ii)**: an isotropic half line of a
fibre is not a case-(i) member, so the span formula is not its support space. -/
theorem not_isCaseIFibre_isotropicHalfLine {F : ConicalLine BQ Q}
    {σ : PointedCone ℝ (realified ↥F.space)}
    (h : IsIsotropicHalfLine (fibreForm Q F.space) σ) : ¬ IsCaseIFibre F σ :=
  fun hc => hc.2 h

omit [Module.Finite ℚ V] in
/-- **The two presentations of the point `{0}` have the same support space**: the apex and the zero
member of a fibre. At the baseline `ConicalMember.vSigma` assigned them `{0}` and `lineSpan F`
respectively, which is the defect this statement removes. -/
theorem ConicalMember.vSigma_fibre_bot_eq_zero (hBsym : BQ.IsSymm)
    (locus : ∀ F : ConicalLine BQ Q, Set (PointedCone ℝ (realified ↥F.space)))
    (F : ConicalLine BQ Q) :
    (ConicalMember.fibre F (⊥ : PointedCone ℝ (realified ↥F.space)) :
        ConicalMember BQ Q).vSigma hBsym locus =
      (ConicalMember.zero : ConicalMember BQ Q).vSigma hBsym locus := by
  rw [ConicalMember.vSigma_fibre_bot, ConicalMember.vSigma_zero]

omit [Module.Finite ℚ V] in
/-- **On a case-(i) member the member-level support space is Definition 6.1 (i)'s span formula.** -/
theorem ConicalMember.vSigma_fibre_of_isCaseI (hBsym : BQ.IsSymm)
    (locus : ∀ F : ConicalLine BQ Q, Set (PointedCone ℝ (realified ↥F.space)))
    {F : ConicalLine BQ Q} {σ : PointedCone ℝ (realified ↥F.space)} (h : IsCaseIFibre F σ) :
    (ConicalMember.fibre F σ : ConicalMember BQ Q).vSigma hBsym locus =
      LeanCategories.Lattices.Valued.vSigma F σ :=
  fibreVSigma_of_ne h.1

/-- **The span formula at an isotropic half line returns the plane**: for the class `fibreRay` of a
`ℚ`-isotropic plane `J` in the fibre of one of its lines, the case-(i) formula `lineSpan F ⊔ ⟨σ⟩` is
the whole plane `J`, and not the support space Definition 6.1 (ii) assigns to `C_{J,+}` — the
orthogonal complement of the plane (`ConicalMember.vSigma_plane_bailyBorel`). This is why the source
excludes isotropic half lines from case (i). -/
theorem vSigma_fibreRay_eq_realify_plane (hBsym : BQ.IsSymm) (F : ConicalLine BQ Q)
    (G : ConicalPlane BQ) (h : F.line ≤ G.plane) (hcoh : G.IsPositiveAt F h) :
    LeanCategories.Lattices.Valued.vSigma F
        (PointedCone.hull ℝ ({rationalPoint (fibreRay hBsym F G h)} :
          Set (realified ↥F.space)))
      = realify G.plane := by
  classical
  set c : ℚ := BQ (F.planeRay G h) F.partner with hc
  have hval : ((fibreRay hBsym F G h : ↥F.space) : V) = F.planeRay G h - c • F.gen := by
    rw [fibreRay_eq_fibreRayProj_of_isPositiveAt hBsym F G h hcoh, fibreRayProj_val, hc]
  have hpoint : rationalPoint ((fibreRay hBsym F G h : ↥F.space) : V) =
      rationalPoint (F.planeRay G h) - (c : ℝ) • rationalPoint F.gen := by
    rw [hval, map_sub, rationalPoint_rat_smul]
  have hspanσ : Submodule.span ℝ ((PointedCone.hull ℝ
      ({rationalPoint (fibreRay hBsym F G h)} : Set (realified ↥F.space))) :
        Set (realified ↥F.space))
      = Submodule.span ℝ ({rationalPoint (fibreRay hBsym F G h)} :
          Set (realified ↥F.space)) := by
    refine le_antisymm ?_ (Submodule.span_mono PointedCone.subset_hull)
    exact Submodule.span_le.2 fun x hx => PointedCone.hull_le_span ℝ _ hx
  have hmap : Submodule.map (realifyMap F.space)
      (Submodule.span ℝ ((PointedCone.hull ℝ
        ({rationalPoint (fibreRay hBsym F G h)} : Set (realified ↥F.space))) :
          Set (realified ↥F.space))) =
      Submodule.span ℝ ({rationalPoint (F.planeRay G h) - (c : ℝ) • rationalPoint F.gen} :
        Set (realified V)) := by
    rw [hspanσ, Submodule.map_span, Set.image_singleton, realifyMap_rationalPoint, hpoint]
  have hspan : realify G.plane =
      Submodule.span ℝ ({rationalPoint F.gen, rationalPoint (F.planeRay G h)} :
        Set (realified V)) := by
    rw [← span_gen_ray_eq_plane F G h]
    exact realified_span_pair
  have hgen : rationalPoint F.gen ∈
      Submodule.span ℝ ({rationalPoint F.gen, rationalPoint (F.planeRay G h)} :
        Set (realified V)) :=
    Submodule.subset_span (Set.mem_insert _ _)
  have hdiff : rationalPoint (F.planeRay G h) - (c : ℝ) • rationalPoint F.gen ∈
      Submodule.span ℝ ({rationalPoint F.gen, rationalPoint (F.planeRay G h)} :
        Set (realified V)) :=
    Submodule.sub_mem _
      (Submodule.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
      (Submodule.smul_mem _ _ hgen)
  rw [LeanCategories.Lattices.Valued.vSigma, hmap, hspan]
  refine le_antisymm (sup_le ?_ (Submodule.span_le.2 (by
    rintro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact hdiff))) ?_
  · rw [lineSpan]
    exact Submodule.span_le.2 (by
      rintro x hx
      rw [Set.mem_singleton_iff] at hx
      subst hx
      exact hgen)
  · refine Submodule.span_le.2 ?_
    rintro x (rfl | hx)
    · exact Submodule.mem_sup_left
        (by rw [lineSpan]; exact Submodule.subset_span (Set.mem_singleton _))
    · rw [Set.mem_singleton_iff] at hx
      subst hx
      have h1 : rationalPoint (F.planeRay G h) - (c : ℝ) • rationalPoint F.gen ∈
          Submodule.span ℝ ({rationalPoint (F.planeRay G h) - (c : ℝ) • rationalPoint F.gen}
            : Set (realified V)) :=
        Submodule.subset_span (Set.mem_singleton _)
      have h2 : (c : ℝ) • rationalPoint F.gen ∈ lineSpan F := by
        rw [lineSpan]
        exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton _))
      have hsum : (rationalPoint (F.planeRay G h) - (c : ℝ) • rationalPoint F.gen)
            + (c : ℝ) • rationalPoint F.gen ∈
          lineSpan F ⊔ Submodule.span ℝ
            ({rationalPoint (F.planeRay G h) - (c : ℝ) • rationalPoint F.gen}
              : Set (realified V)) :=
        Submodule.add_mem _ (Submodule.mem_sup_right h1) (Submodule.mem_sup_left h2)
      simpa [sub_add_cancel] using hsum

/-! ## The open stratum, the pointed cone and the closed members -/

/-- **The open stratum `C_I` of a conical fibre** (Looijenga, Definition 2.1, p. 10, and §1B,
p. 11): the sheet of the fibre's cone at the fibre's positive vector. It is *blunt*: it does not
contain the apex (`zero_not_mem_openStratum`), which every cone of the pointed and closed roles
does. -/
noncomputable def openStratum (F : ConicalLine BQ Q) : Set (realified ↥F.space) :=
  positiveCone.upper (fibreForm Q F.space) F.sheet

omit [Module.Finite ℚ V] in
/-- The open stratum is blunt: the apex is not on it. -/
theorem zero_not_mem_openStratum (F : ConicalLine BQ Q) :
    (0 : realified ↥F.space) ∉ openStratum F := by
  intro h
  have h0 : (fibreForm Q F.space) (0 : realified ↥F.space) = 0 := map_zero _
  have hlt : (0 : ℝ) < (fibreForm Q F.space) (0 : realified ↥F.space) := h.1
  rw [h0] at hlt
  exact lt_irrefl 0 hlt

omit [Module.Finite ℚ V] in
/-- The fibre's own positive vector lies on the open stratum, so the stratum is not empty. -/
theorem sheet_mem_openStratum (F : ConicalLine BQ Q) : F.sheet ∈ openStratum F :=
  ⟨F.sheet_pos, by rw [QuadraticMap.associated_eq_self_apply]; exact F.sheet_pos⟩

omit [Module.Finite ℚ V] in
/-- The pointed cone of a fibre is generated by its open stratum: the role Definition 2.1 carries
into `⋀²V(ℝ)` (`ConicalMember.carrier` of `fibre F F.cone`). -/
theorem cone_eq_hull_openStratum (F : ConicalLine BQ Q) :
    F.cone = PointedCone.hull ℝ (openStratum F) := rfl

omit [Module.Finite ℚ V] in
/-- The apex belongs to the pointed cone of every fibre, and not to its open stratum. -/
theorem zero_mem_cone (F : ConicalLine BQ Q) :
    (0 : realified ↥F.space) ∈ F.cone := Submodule.zero_mem _

omit [Module.Finite ℚ V] in
/-- **The apex is carried to `{0}`**: the only member of the closed conical locus whose carrier is a
single point. -/
theorem ConicalMember.carrier_zero (hBsym : BQ.IsSymm) :
    (ConicalMember.zero : ConicalMember BQ Q).carrier hBsym =
      ({0} : Set (⋀[ℝ]^2 (realified V))) := rfl

/-- **The closed members of the conical locus inside `⋀²V(ℝ)`**: the apex, the carriers of the
closed rational closures `C_{I,+}` of the `ℚ`-isotropic lines, and the half lines `C_{J,+}` of the
`ℚ`-isotropic planes. It is the counterpart of `conicalLocusSet` (Definition 2.1), which carries the
open strata `C_I`; the members of a decomposition of `C_{I,+}` are closed cones inside it, so their
carriers lie here and not necessarily in the open set. -/
noncomputable def conicalLocusClosedSet (hBsym : BQ.IsSymm) : Set (⋀[ℝ]^2 (realified V)) :=
  {x | x = 0 ∨
    (∃ (F : ConicalLine BQ Q),
      x ∈ (ConicalMember.fibre F F.closure : ConicalMember BQ Q).carrier hBsym) ∨
    (∃ (F : ConicalLine BQ Q) (G : ConicalPlane BQ) (h : F.line ≤ G.plane)
      (hcoh : G.IsPositiveAt F h),
      x ∈ (ConicalMember.plane F G h hcoh : ConicalMember BQ Q).carrier hBsym)}

omit [Module.Finite ℚ V] in
/-- The apex is a point of the closed conical locus. -/
theorem zero_mem_conicalLocusClosedSet (hBsym : BQ.IsSymm) :
    (0 : ⋀[ℝ]^2 (realified V)) ∈ conicalLocusClosedSet (Q := Q) hBsym :=
  Or.inl rfl

/-- **The members of a family of cones, as members of the conical locus**: the apex, the case-(i)
members of the fibres (`IsCaseIFibre`), and the half lines of the planes. This is the shape in which
an admissible decomposition `Σ` is used: Definition 6.1's cases are exhaustive for its members, the
zero member of a fibre being the apex and an isotropic half line being a plane member. -/
noncomputable def memberSet
    (locus : ∀ F : ConicalLine BQ Q, Set (PointedCone ℝ (realified ↥F.space))) :
    Set (ConicalMember BQ Q) :=
  {m | m = ConicalMember.zero ∨
    (∃ (F : ConicalLine BQ Q) (σ : PointedCone ℝ (realified ↥F.space)),
      σ ∈ locus F ∧ IsCaseIFibre F σ ∧ m = ConicalMember.fibre F σ) ∨
    (∃ (F : ConicalLine BQ Q) (G : ConicalPlane BQ) (h : F.line ≤ G.plane)
      (hcoh : G.IsPositiveAt F h), m = ConicalMember.plane F G h hcoh)}

omit [Module.Finite ℚ V] in
theorem mem_memberSet_iff
    {locus : ∀ F : ConicalLine BQ Q, Set (PointedCone ℝ (realified ↥F.space))}
    {m : ConicalMember BQ Q} :
    m ∈ memberSet locus ↔ m = ConicalMember.zero ∨
      (∃ (F : ConicalLine BQ Q) (σ : PointedCone ℝ (realified ↥F.space)),
        σ ∈ locus F ∧ IsCaseIFibre F σ ∧ m = ConicalMember.fibre F σ) ∨
      (∃ (F : ConicalLine BQ Q) (G : ConicalPlane BQ) (h : F.line ≤ G.plane)
        (hcoh : G.IsPositiveAt F h), m = ConicalMember.plane F G h hcoh) :=
  Iff.rfl

omit [Module.Finite ℚ V] in
/-- The apex is a member. -/
theorem zero_mem_memberSet
    (locus : ∀ F : ConicalLine BQ Q, Set (PointedCone ℝ (realified ↥F.space))) :
    (ConicalMember.zero : ConicalMember BQ Q) ∈ memberSet locus :=
  mem_memberSet_iff.2 (Or.inl rfl)

omit [Module.Finite ℚ V] in
/-- A case-(i) member of a fibre is a member. -/
theorem mem_memberSet_fibre
    {locus : ∀ F : ConicalLine BQ Q, Set (PointedCone ℝ (realified ↥F.space))}
    {F : ConicalLine BQ Q} {σ : PointedCone ℝ (realified ↥F.space)}
    (hσ : σ ∈ locus F) (hcase : IsCaseIFibre F σ) :
    (ConicalMember.fibre F σ : ConicalMember BQ Q) ∈ memberSet locus :=
  mem_memberSet_iff.2 (Or.inr (Or.inl ⟨F, σ, hσ, hcase, rfl⟩))

omit [Module.Finite ℚ V] in
/-- A plane's half line is a member. -/
theorem mem_memberSet_plane
    {locus : ∀ F : ConicalLine BQ Q, Set (PointedCone ℝ (realified ↥F.space))}
    {F : ConicalLine BQ Q} {G : ConicalPlane BQ} {h : F.line ≤ G.plane}
    {hcoh : G.IsPositiveAt F h} :
    (ConicalMember.plane F G h hcoh : ConicalMember BQ Q) ∈ memberSet locus :=
  mem_memberSet_iff.2 (Or.inr (Or.inr ⟨F, G, h, hcoh, rfl⟩))

omit [Module.Finite ℚ V] in
/-- **The carrier of a member of a decomposition of a fibre lies in the closed conical locus**: a
member of a locally rational decomposition of `C_{I,+}` is a cone inside `C_{I,+}`, and the carrier
is monotone in the member. -/
theorem ConicalMember.carrier_subset_closedSet_of_mem_locus (hBsym : BQ.IsSymm)
    {locus : ∀ F : ConicalLine BQ Q, Set (PointedCone ℝ (realified ↥F.space))}
    (hcoarse : ∀ F : ConicalLine BQ Q, IsLocallyRationalDecomposition F.closure (locus F))
    {F : ConicalLine BQ Q} {σ : PointedCone ℝ (realified ↥F.space)} (hσ : σ ∈ locus F) :
    (ConicalMember.fibre F σ : ConicalMember BQ Q).carrier hBsym ⊆
      conicalLocusClosedSet (Q := Q) hBsym := by
  intro x hx
  exact Or.inr (Or.inl ⟨F, ConicalMember.carrier_fibre_mono hBsym F
    ((hcoarse F).le hσ) hx⟩)

omit [Module.Finite ℚ V] in
/-- **The members of an admissible decomposition are carried into the closed conical locus** — the
descent of a member of `Σ` to a cone of the actual locus, in its three shapes (apex, case (i),
case (ii)). -/
theorem member_carrier_subset_closedSet (hBsym : BQ.IsSymm)
    {locus : ∀ F : ConicalLine BQ Q, Set (PointedCone ℝ (realified ↥F.space))}
    (hcoarse : ∀ F : ConicalLine BQ Q, IsLocallyRationalDecomposition F.closure (locus F))
    {m : ConicalMember BQ Q} (hm : m ∈ memberSet locus) :
    m.carrier hBsym ⊆ conicalLocusClosedSet (Q := Q) hBsym := by
  rw [mem_memberSet_iff] at hm
  rcases hm with rfl | hm | hm
  · intro x hx
    have hx0 : x = 0 := by
      have hmem : x ∈ ({0} : Set (⋀[ℝ]^2 (realified V))) := hx
      simpa using hmem
    subst hx0
    exact Or.inl rfl
  · obtain ⟨F, σ, hσ, _hcase, rfl⟩ := hm
    exact ConicalMember.carrier_subset_closedSet_of_mem_locus hBsym hcoarse hσ
  · obtain ⟨F, G, h, hcoh, rfl⟩ := hm
    intro x hx
    exact Or.inr (Or.inr ⟨F, G, h, hcoh, hx⟩)

/-! ## Presentations of one oriented cone -/

omit [Module.Finite ℚ V] in
/-- **A plane's carrier does not depend on the witnessing line** (Definition 6.1 (ii)'s
carrier-level form): both coherent presentations carry `C_{J,+}` to the closed ray of the same
positive rational generator. -/
theorem ConicalMember.carrier_plane_eq_of_witness_member (hBsym : BQ.IsSymm)
    (F F' : ConicalLine BQ Q) (G : ConicalPlane BQ)
    (h : F.line ≤ G.plane) (h' : F'.line ≤ G.plane)
    (hcoh : G.IsPositiveAt F h) (hcoh' : G.IsPositiveAt F' h') :
    (ConicalMember.plane F G h hcoh : ConicalMember BQ Q).carrier hBsym =
      (ConicalMember.plane F' G h' hcoh' : ConicalMember BQ Q).carrier hBsym :=
  ConicalMember.carrier_plane_eq_of_witness hBsym F F' G h h' hcoh hcoh'

omit [Module.Finite ℚ V] in
/-- **The fibre's line in the support space is presentation-free**: the first summand of `vSigma` is
the span of the fibre's rational generator, and two generators of one `ℚ`-isotropic line span the
same real line. This is the part of Definition 6.1 (i)'s `V_σ` that a change of generator and
partner cannot move. -/
theorem lineSpan_eq_of_gen_eq {F F' : ConicalLine BQ Q} {q : ℚ} (hq : q ≠ 0)
    (h : F'.gen = q • F.gen) : lineSpan F' = lineSpan F := by
  rw [lineSpan, lineSpan, h, rationalPoint_rat_smul]
  ext x
  rw [Submodule.mem_span_singleton, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨r, rfl⟩
    refine ⟨r * (q : ℝ), by rw [mul_smul]⟩
  · rintro ⟨r, rfl⟩
    have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq
    refine ⟨r * ((q : ℝ))⁻¹, ?_⟩
    rw [smul_smul, mul_assoc, inv_mul_cancel₀ hqR, mul_one]

omit [Module.Finite ℚ V] in
/-- **The opposite generator carries the antipodal set**: `(-e) ∧ c = -(e ∧ c)`, so the presentation
with the generator negated contributes the negation of the carrier and *not* the carrier itself. The
two are not identified here: the carrier is a cone, and the source keeps the two orientations of a
plane apart as the two components of `⋀²V(ℝ) − {0}` (Definition 2.1, p. 10, "if we replace `D` by
its complex conjugate ... the conical locus is replaced by its antipode"). -/
theorem wedgeLeft_neg (a : realified V) : wedgeLeft (-a) = -wedgeLeft a :=
  LinearMap.ext fun b => by
    change wedgeTwo (-a) b = -wedgeTwo a b
    rw [show -a = (-1 : ℝ) • a from (neg_one_smul ℝ a).symm, wedgeTwo_smul_left, neg_one_smul]

/-! ## Example 6.2, p. 29, at the member type: supports and isotropic centres -/

/-- **Example 6.2, p. 29, the plane's half line**: at the Baily–Borel decomposition the `Σ`-support
space of `C_{J,+}` is the common orthogonal of the plane, `⨅ (a : ↥G.plane), ker ⟨a, ·⟩` — the
source's "the support spaces are `{0}` and the orthogonal complements of the nontrivial
`ℚ`-isotropic subspaces". The statement names the plane, so it does not depend on the witnessing
line; Condition (ii) of Definition 6.1 for `Σ(bb)` is `Semifan.bailyBorel_condition_ii`. -/
theorem ConicalMember.vSigma_plane_bailyBorel (hBQ : ∀ u w : V,
    (associated Q) (rationalPoint u) (rationalPoint w) = (BQ u w : ℝ))
    (hBsym : BQ.IsSymm) (F : ConicalLine BQ Q) (G : ConicalPlane BQ)
    (h : F.line ≤ G.plane) (hcoh : G.IsPositiveAt F h)
    (hpos : sigPos (fibreForm Q F.space) = 1)
    (hnd : (fibreForm Q F.space).Nondegenerate) :
    (ConicalMember.plane F G h hcoh : ConicalMember BQ Q).vSigma hBsym
        (fun F => facialDecomposition F.closure) =
      ⨅ (a : ↥G.plane), LinearMap.ker (associated Q (rationalPoint (a : V))) := by
  rw [show (ConicalMember.plane F G h hcoh : ConicalMember BQ Q).vSigma hBsym
        (fun F => facialDecomposition F.closure) =
      LeanCategories.Lattices.Valued.vSigmaPlane hBsym F (facialDecomposition F.closure) G h
      from rfl,
    vSigmaPlane_eq_ker_inf_ker hBQ hBsym F G h hpos hnd]
  exact ker_inf_ker_eq F G h

/-- **Example 6.2, p. 29, the fibre's closed cone**: at the member type the support space of
`C_{I,+}` is `I^⊥`, the kernel of the fibre's generator. -/
theorem ConicalMember.vSigma_fibre_closure (hBQ : ∀ u w : V,
    (associated Q) (rationalPoint u) (rationalPoint w) = (BQ u w : ℝ))
    (hBsym : BQ.IsSymm) (F : ConicalLine BQ Q)
    (hpos : sigPos (fibreForm Q F.space) = 1)
    (locus : ∀ F : ConicalLine BQ Q, Set (PointedCone ℝ (realified ↥F.space))) :
    (ConicalMember.fibre F F.closure : ConicalMember BQ Q).vSigma hBsym locus =
      LinearMap.ker (associated Q (rationalPoint F.gen)) := by
  have hne : (F.closure : PointedCone ℝ (realified ↥F.space)) ≠ ⊥ := by
    intro hbot
    have hspan := ConicalLine.span_closure_eq_top F hpos
    have hzero : F.sheet = 0 := by
      have hmem : F.sheet ∈ Submodule.span ℝ
          ((F.closure : PointedCone ℝ (realified ↥F.space)) : Set (realified ↥F.space)) := by
        rw [hspan]
        exact Submodule.mem_top
      rw [hbot] at hmem
      simpa using hmem
    exact (ne_of_gt F.sheet_pos) (by rw [hzero]; simp)
  change fibreVSigma F F.closure = LinearMap.ker (associated Q (rationalPoint F.gen))
  rw [fibreVSigma_of_ne hne, ConicalLine.vSigma_closure_eq_ker hBQ hBsym F hpos]

omit [Module.Finite ℚ V] in
/-- **The orthogonal complement of a line is the kernel of its generator's form**: `⟨e, ·⟩` vanishes
on exactly the vectors orthogonal to `e`. -/
theorem orthogonal_lineSpan_eq_ker (F : ConicalLine BQ Q) :
    LinearMap.BilinForm.orthogonal (associated Q) (lineSpan F) =
      LinearMap.ker (associated Q (rationalPoint F.gen)) := by
  ext x
  rw [LinearMap.BilinForm.mem_orthogonal_iff, LinearMap.mem_ker, lineSpan]
  constructor
  · intro h
    exact h _ (Submodule.subset_span (Set.mem_singleton _))
  · intro h y hy
    have hle : Submodule.span ℝ ({rationalPoint F.gen} : Set (realified V)) ≤
        LinearMap.ker (associated Q x) := by
      refine Submodule.span_le.2 ?_
      rintro z hz
      rw [Set.mem_singleton_iff] at hz
      subst hz
      exact LinearMap.mem_ker.2 (by rw [associated_comm Q x (rationalPoint F.gen)]; exact h)
    have hx0 : (associated Q x) y = 0 := hle hy
    rwa [← associated_comm Q x y]

/-- **`I(C_{I,+}) = I`**: the isotropic centre of the fibre's closed cone is exactly the fibre's
line. The support space is `I^⊥` (`ConicalMember.vSigma_fibre_closure`) and the double orthogonal
complement of `I` is `I`, where nondegeneracy of the ambient form enters; no dimension count of
real isotropic subspaces is used. -/
theorem ConicalMember.isotropicCenter_fibre_closure (hBQ : ∀ u w : V,
    (associated Q) (rationalPoint u) (rationalPoint w) = (BQ u w : ℝ))
    (hBsym : BQ.IsSymm) (hnd : (associated Q).Nondegenerate) (F : ConicalLine BQ Q)
    (hpos : sigPos (fibreForm Q F.space) = 1)
    (locus : ∀ F : ConicalLine BQ Q, Set (PointedCone ℝ (realified ↥F.space))) :
    (ConicalMember.fibre F F.closure : ConicalMember BQ Q).isotropicCenter hBsym locus =
      lineSpan F := by
  have hrefl : (associated Q).IsRefl := fun x y h => by
    rw [associated_comm Q x y] at h
    exact h
  have hker := orthogonal_lineSpan_eq_ker (Q := Q) F
  rw [ConicalMember.isotropicCenter, ConicalMember.vSigma_fibre_closure hBQ hBsym F hpos locus,
    LeanCategories.Lattices.Valued.isotropicCenter, ← hker,
    LinearMap.BilinForm.orthogonal_orthogonal hnd hrefl]
  exact inf_eq_right.2 (hker ▸ lineSpan_le_ker_gen hBQ F)

omit [Module.Finite ℚ V] in
/-- **Example 6.2 at the member type, the apex**: the isotropic centre of `{0}` is `{0}`. -/
theorem ConicalMember.isotropicCenter_zero_member (hBsym : BQ.IsSymm)
    (locus : ∀ F : ConicalLine BQ Q, Set (PointedCone ℝ (realified ↥F.space))) :
    (ConicalMember.zero : ConicalMember BQ Q).isotropicCenter hBsym locus = ⊥ :=
  ConicalMember.isotropicCenter_zero hBsym locus

/-- **The Baily–Borel members are cones of the conical locus**: the descent of the first item at the
decomposition of Example 6.2. -/
theorem bailyBorel_memberSet_carrier_subset
    (hBsym : BQ.IsSymm) (hpos : ∀ F : ConicalLine BQ Q, sigPos (fibreForm Q F.space) = 1)
    (hnd : ∀ F : ConicalLine BQ Q, (fibreForm Q F.space).Nondegenerate)
    {m : ConicalMember BQ Q} (hm : m ∈ memberSet (fun F => facialDecomposition F.closure)) :
    m.carrier hBsym ⊆ conicalLocusClosedSet (Q := Q) hBsym :=
  member_carrier_subset_closedSet hBsym
    (fun F => bailyBorel_condition_i F (hpos F) (hnd F)) hm

/-! ## The isotropic centre of a plane's half line -/

omit [Module.Finite ℚ V] in
/-- **The member's own isotropic generators span the plane**: the two vectors of the plane's
positive basis are isotropic (`ConicalPlane.dir_iso`, `dirAlt_iso`) and they span `J`, so the
isotropic directions the member `C_{J,+}` is built from are a *spanning* set for `J`, not a subset.
This is what makes the centre of the member `J`: the centre is read off the member's plane, not off
its `Σ`-support space. -/
theorem ConicalPlane.realify_eq_span_isotropic (G : ConicalPlane BQ) :
    realify G.plane = Submodule.span ℝ
      ({rationalPoint G.dir, rationalPoint G.dirAlt} : Set (realified V)) := by
  rw [← ConicalPlane.span_dir_eq]
  exact realified_span_pair

/-- **The support space of a plane's half line is `J^⊥`**: the common orthogonal of the plane in the
form the facial decomposition gives it (`vSigmaPlane_eq_ker_inf_ker`), identified with the
orthogonal complement of `realify G.plane` through the plane's isotropic generators. -/
theorem orthogonal_realify_eq_ker_inf_ker (hBsym : BQ.IsSymm) (F : ConicalLine BQ Q)
    (G : ConicalPlane BQ) (h : F.line ≤ G.plane) :
    LinearMap.BilinForm.orthogonal (associated Q) (realify G.plane) =
      LinearMap.ker (associated Q (rationalPoint F.gen)) ⊓
        LinearMap.ker (associated Q (rationalPoint (F.planeRay G h))) := by
  have hspan : realify G.plane =
      Submodule.span ℝ ({rationalPoint F.gen, rationalPoint (F.planeRay G h)} :
        Set (realified V)) := by
    rw [← span_gen_ray_eq_plane F G h]
    exact realified_span_pair
  ext x
  rw [hspan, LinearMap.BilinForm.mem_orthogonal_iff, Submodule.mem_inf, LinearMap.mem_ker,
    LinearMap.mem_ker]
  constructor
  · intro hx
    exact ⟨hx _ (Submodule.subset_span (Set.mem_insert _ _)),
      hx _ (Submodule.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _)))⟩
  · rintro ⟨h1, h2⟩ y hy
    obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.1 hy
    have step : (associated Q) (a • rationalPoint F.gen + b • rationalPoint (F.planeRay G h)) x
        = a * ((associated Q) (rationalPoint F.gen)) x
          + b * ((associated Q) (rationalPoint (F.planeRay G h))) x := by
      rw [map_add, map_smul, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
        LinearMap.smul_apply, smul_eq_mul, smul_eq_mul]
    rw [step, h1, h2, mul_zero, mul_zero, add_zero]

/-- **`I(C_{J,+}) = J`**: the isotropic centre of a plane's half line is exactly the plane. The
support space is `J^⊥` (`orthogonal_realify_eq_ker_inf_ker`), and the plane is totally isotropic, so
it lies in its own orthogonal complement — this is what puts `J` inside the centre — while the
double orthogonal complement returns it, which keeps the centre from being larger. The member's
isotropic generators span `J` (`ConicalPlane.realify_eq_span_isotropic`), so the centre is the
member's own plane and not an artefact of the support formula. -/
theorem ConicalMember.isotropicCenter_plane_bailyBorel (hBQ : ∀ u w : V,
    (associated Q) (rationalPoint u) (rationalPoint w) = (BQ u w : ℝ))
    (hBsym : BQ.IsSymm) (hnd : (associated Q).Nondegenerate) (F : ConicalLine BQ Q)
    (G : ConicalPlane BQ) (h : F.line ≤ G.plane) (hcoh : G.IsPositiveAt F h)
    (hpos : sigPos (fibreForm Q F.space) = 1)
    (hndf : (fibreForm Q F.space).Nondegenerate) :
    (ConicalMember.plane F G h hcoh : ConicalMember BQ Q).isotropicCenter hBsym
        (fun F => facialDecomposition F.closure) = realify G.plane := by
  have hrefl : (associated Q).IsRefl := fun x y hxy => by
    rw [associated_comm Q x y] at hxy
    exact hxy
  -- the plane is totally isotropic, so it lies in its own orthogonal complement
  have hpair : ∀ a b : ↥G.plane,
      (associated Q) (rationalPoint (a : V)) (rationalPoint (b : V)) = 0 := by
    intro a b
    rw [hBQ, G.isotropic (a : V) a.2 (b : V) b.2]
    norm_num
  have hdd : (associated Q) (rationalPoint G.dir) (rationalPoint G.dir) = 0 :=
    hpair ⟨G.dir, G.dir_mem⟩ ⟨G.dir, G.dir_mem⟩
  have hda : (associated Q) (rationalPoint G.dir) (rationalPoint G.dirAlt) = 0 :=
    hpair ⟨G.dir, G.dir_mem⟩ ⟨G.dirAlt, G.dirAlt_mem⟩
  have had : (associated Q) (rationalPoint G.dirAlt) (rationalPoint G.dir) = 0 :=
    hpair ⟨G.dirAlt, G.dirAlt_mem⟩ ⟨G.dir, G.dir_mem⟩
  have haa : (associated Q) (rationalPoint G.dirAlt) (rationalPoint G.dirAlt) = 0 :=
    hpair ⟨G.dirAlt, G.dirAlt_mem⟩ ⟨G.dirAlt, G.dirAlt_mem⟩
  have hle : realify G.plane ≤
      LinearMap.BilinForm.orthogonal (associated Q) (realify G.plane) := by
    rw [ConicalPlane.realify_eq_span_isotropic]
    refine Submodule.span_le.2 ?_
    rintro y (rfl | hy)
    · refine LinearMap.BilinForm.mem_orthogonal_iff.2 ?_
      intro n hn
      have hker : Submodule.span ℝ
          ({rationalPoint G.dir, rationalPoint G.dirAlt} : Set (realified V)) ≤
          LinearMap.ker ((associated Q).flip (rationalPoint G.dir)) := by
        refine Submodule.span_le.2 ?_
        rintro z (rfl | hz)
        · exact LinearMap.mem_ker.2 (by rw [LinearMap.flip_apply]; exact hdd)
        · rw [Set.mem_singleton_iff] at hz
          subst hz
          exact LinearMap.mem_ker.2 (by rw [LinearMap.flip_apply]; exact had)
      exact LinearMap.mem_ker.1 (hker hn)
    · rw [Set.mem_singleton_iff] at hy
      subst hy
      refine LinearMap.BilinForm.mem_orthogonal_iff.2 ?_
      intro n hn
      have hker : Submodule.span ℝ
          ({rationalPoint G.dir, rationalPoint G.dirAlt} : Set (realified V)) ≤
          LinearMap.ker ((associated Q).flip (rationalPoint G.dirAlt)) := by
        refine Submodule.span_le.2 ?_
        rintro z (rfl | hz)
        · exact LinearMap.mem_ker.2 (by rw [LinearMap.flip_apply]; exact hda)
        · rw [Set.mem_singleton_iff] at hz
          subst hz
          exact LinearMap.mem_ker.2 (by rw [LinearMap.flip_apply]; exact haa)
      exact LinearMap.mem_ker.1 (hker hn)
  have hv : (ConicalMember.plane F G h hcoh : ConicalMember BQ Q).vSigma hBsym
      (fun F => facialDecomposition F.closure) = ⨅ (a : ↥G.plane),
        LinearMap.ker (associated Q (rationalPoint (a : V))) :=
    ConicalMember.vSigma_plane_bailyBorel hBQ hBsym F G h hcoh hpos hndf
  rw [ConicalMember.isotropicCenter, hv, ← ker_inf_ker_eq F G h,
    ← orthogonal_realify_eq_ker_inf_ker hBsym F G h,
    LeanCategories.Lattices.Valued.isotropicCenter,
    LinearMap.BilinForm.orthogonal_orthogonal hnd hrefl]
  exact inf_eq_right.2 hle

omit [Module.Finite ℚ V] in
/-- **A negated generator negates the carried set**: `wedgeLeft_neg` read on images. This is the
sign of the class, and it is what the source's two components of `⋀²V(ℝ) − {0}` distinguish:
the negated presentation is a different piece of the conical locus, not the same one. -/
theorem wedgeLeft_neg_image (a : realified V) (S : Set (realified V)) :
    wedgeLeft (-a) '' S = (fun x => -x) '' (wedgeLeft a '' S) := by
  rw [wedgeLeft_neg]
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨_, ⟨y, hy, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨y, hy, rfl⟩

/-! ## The two orientations of a plane -/

/-- **The same plane with the opposite orientation**: the positive basis in the other order, so that
the positive rational generator of Example 6.3, p. 29, is `-r_J`. It is a legitimate presentation of
the plane, and a different one: `ConicalMember.carrier_plane_flip` and
`ConicalMember.not_both_orientations_coherent` say how it differs. -/
noncomputable def ConicalPlane.flip (G : ConicalPlane BQ) : ConicalPlane BQ where
  plane := G.plane
  isotropic := G.isotropic
  two_dim := G.two_dim
  basis := G.basis.reindex (Equiv.swap (0 : Fin 2) 1)

omit [Module.Finite ℚ V] in
theorem ConicalPlane.flip_plane (G : ConicalPlane BQ) : G.flip.plane = G.plane := rfl

omit [Module.Finite ℚ V] in
theorem ConicalPlane.flip_dir (G : ConicalPlane BQ) : G.flip.dir = G.dirAlt := by
  change ((G.basis.reindex (Equiv.swap (0 : Fin 2) 1)) (0 : Fin 2) : V) = G.dirAlt
  rw [Module.Basis.reindex_apply]
  simp [ConicalPlane.dirAlt]

omit [Module.Finite ℚ V] in
theorem ConicalPlane.flip_dirAlt (G : ConicalPlane BQ) : G.flip.dirAlt = G.dir := by
  change ((G.basis.reindex (Equiv.swap (0 : Fin 2) 1)) (1 : Fin 2) : V) = G.dir
  rw [Module.Basis.reindex_apply]
  simp [ConicalPlane.dir]

omit [Module.Finite ℚ V] in
/-- **The opposite orientation generates the antipodal line**: `r_{J^op} = -r_J`. -/
theorem ConicalPlane.flip_wedge (G : ConicalPlane BQ) :
    wedgeTwo (rationalPoint G.flip.dir) (rationalPoint G.flip.dirAlt) =
      -wedgeTwo (rationalPoint G.dir) (rationalPoint G.dirAlt) := by
  rw [ConicalPlane.flip_dir, ConicalPlane.flip_dirAlt, wedgeTwo_swap]

/-- **The flip does not change the plane**, hence not the member's centre: the two orientations
present the same `J`, so `I(C_{J^op,+}) = I(C_{J,+}) = J`
(`ConicalMember.isotropicCenter_plane_bailyBorel` at `G.flip`). What the flip changes is the
*carrier*, in the next two statements. -/
theorem ConicalMember.isotropicCenter_plane_flip (hBQ : ∀ u w : V,
    (associated Q) (rationalPoint u) (rationalPoint w) = (BQ u w : ℝ))
    (hBsym : BQ.IsSymm) (hnd : (associated Q).Nondegenerate) (F : ConicalLine BQ Q)
    (G : ConicalPlane BQ) (h : F.line ≤ G.plane) (hcoh' : G.flip.IsPositiveAt F h)
    (hpos : sigPos (fibreForm Q F.space) = 1)
    (hndf : (fibreForm Q F.space).Nondegenerate) :
    (ConicalMember.plane F G.flip h hcoh' : ConicalMember BQ Q).isotropicCenter hBsym
        (fun F => facialDecomposition F.closure) = realify G.plane := by
  have h' : F.line ≤ G.flip.plane := by rw [ConicalPlane.flip_plane]; exact h
  have hcent := ConicalMember.isotropicCenter_plane_bailyBorel hBQ hBsym hnd F G.flip h' hcoh'
    hpos hndf
  rwa [ConicalPlane.flip_plane] at hcent

omit [Module.Finite ℚ V] in
/-- **The flip negates the carrier**: a plane's carrier at the opposite orientation is the antipodal
half line, `-C_{J,+}` — the other component of `⋀²V(ℝ) − {0}`, not the same subset. The two
presentations are therefore not identified anywhere below. -/
theorem ConicalMember.carrier_plane_flip (hBsym : BQ.IsSymm) (F : ConicalLine BQ Q)
    (G : ConicalPlane BQ) (h : F.line ≤ G.plane) (hcoh' : G.flip.IsPositiveAt F h) :
    (ConicalMember.plane F G.flip h hcoh' : ConicalMember BQ Q).carrier hBsym =
      {x : ⋀[ℝ]^2 (realified V) | ∃ t : ℝ, 0 ≤ t ∧
        t • (-(wedgeTwo (rationalPoint G.dir) (rationalPoint G.dirAlt))) = x} := by
  rw [ConicalMember.carrier_plane_eq_positiveRay hBsym F G.flip h hcoh', ConicalPlane.flip_wedge]

omit [Module.Finite ℚ V] in
/-- **The flipped carrier is not the half line `C_{J,+}`**: it is the antipodal ray of `r_J`, and
`r_J = dir ∧ dirAlt ≠ 0`, so the two orientations give different subsets of `⋀²V(ℝ)` and are not
identified. -/
theorem ConicalMember.carrier_plane_flip_ne_posRay (hBsym : BQ.IsSymm) (F : ConicalLine BQ Q)
    (G : ConicalPlane BQ) (h : F.line ≤ G.plane) (hcoh' : G.flip.IsPositiveAt F h) :
    (ConicalMember.plane F G.flip h hcoh' : ConicalMember BQ Q).carrier hBsym ≠
      {x : ⋀[ℝ]^2 (realified V) | ∃ t : ℝ, 0 ≤ t ∧
        t • wedgeTwo (rationalPoint G.dir) (rationalPoint G.dirAlt) = x} := by
  intro heq
  have hmem : wedgeTwo (rationalPoint G.dir) (rationalPoint G.dirAlt) ∈
      (ConicalMember.plane F G.flip h hcoh' : ConicalMember BQ Q).carrier hBsym := by
    rw [heq]
    exact ⟨(1 : ℝ), zero_le_one, one_smul ℝ _⟩
  rw [ConicalMember.carrier_plane_flip hBsym F G h hcoh'] at hmem
  obtain ⟨t, ht, hteq⟩ := hmem
  have htr : t • wedgeTwo (rationalPoint G.dir) (rationalPoint G.dirAlt) =
      -wedgeTwo (rationalPoint G.dir) (rationalPoint G.dirAlt) := by
    have h2 : -(t • wedgeTwo (rationalPoint G.dir) (rationalPoint G.dirAlt)) =
        wedgeTwo (rationalPoint G.dir) (rationalPoint G.dirAlt) := by
      rwa [smul_neg] at hteq
    simpa using congrArg Neg.neg h2
  have h1 : (1 + t) • wedgeTwo (rationalPoint G.dir) (rationalPoint G.dirAlt) = 0 := by
    rw [add_smul, one_smul, htr, add_neg_cancel]
  exact wedgeTwo_dir_ne_zero G ((smul_eq_zero.1 h1).resolve_left (by linarith [ht]))

omit [Module.Finite ℚ V] in
/-- **The wedge with a generator kills the line**: two vectors that differ by an element of
`span{a}` are carried to the same element of `⋀²V(ℝ)` by `c ↦ a ∧ c`. This is why a member's carrier
depends on its class in `I^⊥/I` and not on the representative a chosen complement gives it. -/
theorem wedgeLeft_eq_of_sub_mem_span {a c c' : realified V}
    (h : c' - c ∈ Submodule.span ℝ ({a} : Set (realified V))) :
    wedgeLeft a c' = wedgeLeft a c := by
  obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.1 h
  have hc' : c' = c + t • a := by
    rw [add_comm]
    exact sub_eq_iff_eq_add.1 ht.symm
  rw [hc', map_add, wedgeLeft_apply, wedgeLeft_apply]
  have hzero : wedgeTwo a (t • a) = 0 := by
    rw [wedgeTwo_smul_right]
    exact smul_eq_zero.2 (Or.inr (wedgeTwo_self a))
  rw [hzero, add_zero]

omit [Module.Finite ℚ V] in
omit [Module.Finite ℚ V] in
/-- **A change of partner does not change the carrier**: if two presentations `F`, `F'` of one
`ℚ`-isotropic line have the same generator, and the two cones are carried to images whose elements
differ by elements of the line — which is what it means for them to present the same cone of classes
in `I^⊥/I` — then the carriers in `⋀²V(ℝ)` are equal. This is the carrier-level form of a partner
change: the complement `I^⊥/I ≅ ⟨gen, partner⟩^⊥` moves, but `gen ∧ ·` kills the difference. -/
theorem ConicalMember.carrier_fibre_eq_of_class_eq (hBsym : BQ.IsSymm) {F F' : ConicalLine BQ Q}
    (hgen : F'.gen = F.gen)
    {σ : PointedCone ℝ (realified ↥F.space)} {σ' : PointedCone ℝ (realified ↥F'.space)}
    (h1 : ∀ x ∈ (fun c : realified ↥F.space => realifyMap F.space c) ''
        (σ : Set (realified ↥F.space)),
      ∃ x' ∈ (fun c : realified ↥F'.space => realifyMap F'.space c) ''
        (σ' : Set (realified ↥F'.space)), x' - x ∈ lineSpan F)
    (h2 : ∀ x' ∈ (fun c : realified ↥F'.space => realifyMap F'.space c) ''
        (σ' : Set (realified ↥F'.space)),
      ∃ x ∈ (fun c : realified ↥F.space => realifyMap F.space c) ''
        (σ : Set (realified ↥F.space)), x' - x ∈ lineSpan F) :
    (ConicalMember.fibre F σ : ConicalMember BQ Q).carrier hBsym =
      (ConicalMember.fibre F' σ' : ConicalMember BQ Q).carrier hBsym := by
  have hgenR : rationalPoint F'.gen = rationalPoint F.gen := by rw [hgen]
  rw [ConicalMember.carrier, ConicalMember.carrier, hgenR]
  ext x
  constructor
  · rintro ⟨c, hc, rfl⟩
    obtain ⟨c', hc', hdiff⟩ := h1 c hc
    exact ⟨c', hc', wedgeLeft_eq_of_sub_mem_span hdiff⟩
  · rintro ⟨c', hc', rfl⟩
    obtain ⟨c, hc, hdiff⟩ := h2 c' hc'
    exact ⟨c, hc, (wedgeLeft_eq_of_sub_mem_span hdiff).symm⟩

end LeanCategories.Lattices.Valued
