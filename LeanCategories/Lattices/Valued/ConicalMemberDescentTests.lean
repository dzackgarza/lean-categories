/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Lattices.Valued.ConicalMemberDescent

/-!
# Controls for the descent of admissible members to the conical locus (#166)

The members of an admissible decomposition of the conical locus are cones of the actual locus
(Looijenga, Definition 2.1, p. 10, and Definition 6.1, p. 28), with a support space and an isotropic
centre that do not depend on the presentation. These are the compile-level controls of
`ConicalMemberDescent.lean`: each declaration here consumes the new API, and the first one records
the identity that *fails* at the baseline.

* **The baseline defect (item 2)**: at the span formula the zero member of a fibre has support space
  `lineSpan F`, while the apex has `{0}` — the same carrier `{0}` with two support spaces. The first
  example below records the fact that made it a defect (`lineSpan F ≠ ⊥`, so the two values really
  differ), and the second that the two presentations now agree.
* **The two degenerate shapes of Definition 6.1 (i) are excluded** (item 2): the zero member is the
  apex, and an isotropic half line is a plane member; the span formula at a half line returns the
  *plane* (`vSigma_fibreRay_eq_realify_plane`), which is why the source routes half lines through
  case (ii) instead.
* **One carrier, one role** (item 1): the open stratum is blunt (no apex), the pointed cone is its
  cone hull, and the members of a decomposition are carried into the closed conical locus.
* **Presentations** (item 3): a positive rescaling of a generator does not change the carrier, a
  change of witnessing line does not change a plane's carrier or support, and the opposite
  orientation of a plane is the *antipodal* half line — a different subset of `⋀²V(ℝ)`, not
  identified with `C_{J,+}`.
* **The Baily–Borel supports and centres (item 4)**: `{0}`, `I^⊥`, `J^⊥` for the supports and
  `{0}`, `I`, `J` for the isotropic centres.
-/

@[expose] public section

open PointedCone QuadraticMap

open scoped TensorProduct

namespace LeanCategories.Lattices.Valued.ConicalMemberDescentTests

variable {V : Type} [AddCommGroup V] [Module ℚ V] [Module.Finite ℚ V]
variable {BQ : LinearMap.BilinForm ℚ V} {Q : QuadraticForm ℝ (realified V)}

/-! ## Item 2: zero and fibre bottom reconciled -/

/-- **The defect the repair removes**: the case-(i) span formula at the zero member of a fibre is
`lineSpan F`, not `{0}`, so at the baseline the carrier `{0}` of the apex and of the fibre's zero
member carried two different support spaces. -/
example (F : ConicalLine BQ Q) : lineSpan F ≠ ⊥ := by
  intro h
  have hmem : rationalPoint F.gen ∈ (⊥ : Submodule ℝ (realified V)) := by
    rw [← h]
    exact Submodule.subset_span (Set.mem_singleton _)
  rw [Submodule.mem_bot] at hmem
  exact (rationalPoint_ne_zero F.gen_ne) hmem

/-- **Item 2, reconciled**: the apex and the zero member of a fibre have the same carrier and the
same support space. -/
example (hBsym : BQ.IsSymm)
    (locus : ∀ F : ConicalLine BQ Q, Set (PointedCone ℝ (realified ↥F.space)))
    (F : ConicalLine BQ Q) :
    (ConicalMember.fibre F (⊥ : PointedCone ℝ (realified ↥F.space)) :
        ConicalMember BQ Q).vSigma hBsym locus =
      (ConicalMember.zero : ConicalMember BQ Q).vSigma hBsym locus ∧
    (ConicalMember.fibre F (⊥ : PointedCone ℝ (realified ↥F.space)) :
        ConicalMember BQ Q).carrier hBsym =
      (ConicalMember.zero : ConicalMember BQ Q).carrier hBsym :=
  ⟨ConicalMember.vSigma_fibre_bot_eq_zero hBsym locus F,
    ConicalMember.carrier_fibre_bot hBsym F⟩

/-- **Item 2, the zero member is not a case-(i) member**: it is the apex. -/
example (F : ConicalLine BQ Q) :
    ¬ IsCaseIFibre F (⊥ : PointedCone ℝ (realified ↥F.space)) :=
  not_isCaseIFibre_bot F

/-- **Item 2, isotropic half lines are routed through Definition 6.1 (ii)**: the half line of a
plane in a fibre is not a case-(i) member. -/
example (hBQ : ∀ u w : V, (associated Q) (rationalPoint u) (rationalPoint w) = (BQ u w : ℝ))
    (hBsym : BQ.IsSymm) (F : ConicalLine BQ Q) (G : ConicalPlane BQ)
    (h : F.line ≤ G.plane) (hne : rationalPoint (fibreRay hBsym F G h) ≠ 0) :
    ¬ IsCaseIFibre F (PointedCone.hull ℝ
      ({rationalPoint (fibreRay hBsym F G h)} : Set (realified ↥F.space))) :=
  not_isCaseIFibre_isotropicHalfLine
    ⟨_, hne, fibreRay_isotropic hBQ hBsym F G h, rfl⟩

/-- **Item 2, the span formula at a half line returns the plane**, not the case-(ii) support
space. -/
example (hBsym : BQ.IsSymm) (F : ConicalLine BQ Q) (G : ConicalPlane BQ)
    (h : F.line ≤ G.plane) (hcoh : G.IsPositiveAt F h) :
    LeanCategories.Lattices.Valued.vSigma F (PointedCone.hull ℝ
        ({rationalPoint (fibreRay hBsym F G h)} : Set (realified ↥F.space))) =
      realify G.plane :=
  vSigma_fibreRay_eq_realify_plane hBsym F G h hcoh

/-! ## Item 1: the open stratum, the pointed cone and the closed members -/

/-- The open stratum is blunt. -/
example (F : ConicalLine BQ Q) : (0 : realified ↥F.space) ∉ openStratum F :=
  zero_not_mem_openStratum F

/-- The open stratum is not empty: the fibre's sheet lies on it. -/
example (F : ConicalLine BQ Q) : F.sheet ∈ openStratum F := sheet_mem_openStratum F

/-- The pointed cone of a fibre is generated by its open stratum. -/
example (F : ConicalLine BQ Q) :
    F.cone = PointedCone.hull ℝ (openStratum F) := cone_eq_hull_openStratum F

/-- **Item 1, descent of the members**: every member of a locally rational decomposition of the
fibres is carried into the closed conical locus. -/
example (hBsym : BQ.IsSymm)
    {locus : ∀ F : ConicalLine BQ Q, Set (PointedCone ℝ (realified ↥F.space))}
    (hcoarse : ∀ F : ConicalLine BQ Q, IsLocallyRationalDecomposition F.closure (locus F))
    {m : ConicalMember BQ Q} (hm : m ∈ memberSet locus) :
    m.carrier hBsym ⊆ conicalLocusClosedSet (Q := Q) hBsym :=
  member_carrier_subset_closedSet hBsym hcoarse hm

/-! ## Item 3: presentations -/

/-- **A change of witnessing line does not change a plane's carrier.** -/
example (hBsym : BQ.IsSymm) (F F' : ConicalLine BQ Q) (G : ConicalPlane BQ)
    (h : F.line ≤ G.plane) (h' : F'.line ≤ G.plane)
    (hcoh : G.IsPositiveAt F h) (hcoh' : G.IsPositiveAt F' h') :
    (ConicalMember.plane F G h hcoh : ConicalMember BQ Q).carrier hBsym =
      (ConicalMember.plane F' G h' hcoh' : ConicalMember BQ Q).carrier hBsym :=
  ConicalMember.carrier_plane_eq_of_witness_member hBsym F F' G h h' hcoh hcoh'

/-- **A change of generator and partner does not move the fibre's line in the support space.** -/
example {F F' : ConicalLine BQ Q} {q : ℚ} (hq : q ≠ 0) (h : F'.gen = q • F.gen) :
    lineSpan F' = lineSpan F :=
  lineSpan_eq_of_gen_eq hq h

/-- **The opposite generator carries the antipodal set**, and it is not identified with the carrier
of the opposite orientation. -/
example (a : realified V) : wedgeLeft (-a) = -wedgeLeft a := wedgeLeft_neg a

/-! ## Item 4: the Baily–Borel supports and isotropic centres -/

/-- **Item 4, the plane support is the common orthogonal of `J`.** -/
example (hBQ : ∀ u w : V, (associated Q) (rationalPoint u) (rationalPoint w) = (BQ u w : ℝ))
    (hBsym : BQ.IsSymm) (F : ConicalLine BQ Q) (G : ConicalPlane BQ)
    (h : F.line ≤ G.plane) (hcoh : G.IsPositiveAt F h)
    (hpos : sigPos (fibreForm Q F.space) = 1)
    (hnd : (fibreForm Q F.space).Nondegenerate) :
    (ConicalMember.plane F G h hcoh : ConicalMember BQ Q).vSigma hBsym
        (fun F => facialDecomposition F.closure) =
      ⨅ (a : ↥G.plane), LinearMap.ker (associated Q (rationalPoint (a : V))) :=
  ConicalMember.vSigma_plane_bailyBorel hBQ hBsym F G h hcoh hpos hnd

/-- **Item 4, the fibre support is `I^⊥`.** -/
example (hBQ : ∀ u w : V, (associated Q) (rationalPoint u) (rationalPoint w) = (BQ u w : ℝ))
    (hBsym : BQ.IsSymm) (F : ConicalLine BQ Q)
    (hpos : sigPos (fibreForm Q F.space) = 1)
    (locus : ∀ F : ConicalLine BQ Q, Set (PointedCone ℝ (realified ↥F.space))) :
    (ConicalMember.fibre F F.closure : ConicalMember BQ Q).vSigma hBsym locus =
      LinearMap.ker (associated Q (rationalPoint F.gen)) :=
  ConicalMember.vSigma_fibre_closure hBQ hBsym F hpos locus

/-- **Item 4, the exact isotropic centre of the fibre's closed cone is `I`.** -/
example (hBQ : ∀ u w : V, (associated Q) (rationalPoint u) (rationalPoint w) = (BQ u w : ℝ))
    (hBsym : BQ.IsSymm) (hnd : (associated Q).Nondegenerate) (F : ConicalLine BQ Q)
    (hpos : sigPos (fibreForm Q F.space) = 1)
    (locus : ∀ F : ConicalLine BQ Q, Set (PointedCone ℝ (realified ↥F.space))) :
    (ConicalMember.fibre F F.closure : ConicalMember BQ Q).isotropicCenter hBsym locus =
      lineSpan F :=
  ConicalMember.isotropicCenter_fibre_closure hBQ hBsym hnd F hpos locus

/-- **Item 4, the apex's isotropic centre is `{0}`.** -/
example (hBsym : BQ.IsSymm)
    (locus : ∀ F : ConicalLine BQ Q, Set (PointedCone ℝ (realified ↥F.space))) :
    (ConicalMember.zero : ConicalMember BQ Q).isotropicCenter hBsym locus = ⊥ :=
  ConicalMember.isotropicCenter_zero_member hBsym locus

/-- **Item 4, the Baily–Borel members descend to cones of the conical locus.** -/
example (hBsym : BQ.IsSymm) (hpos : ∀ F : ConicalLine BQ Q, sigPos (fibreForm Q F.space) = 1)
    (hnd : ∀ F : ConicalLine BQ Q, (fibreForm Q F.space).Nondegenerate)
    {m : ConicalMember BQ Q} (hm : m ∈ memberSet (fun F => facialDecomposition F.closure)) :
    m.carrier hBsym ⊆ conicalLocusClosedSet (Q := Q) hBsym :=
  bailyBorel_memberSet_carrier_subset hBsym hpos hnd hm

end LeanCategories.Lattices.Valued.ConicalMemberDescentTests
