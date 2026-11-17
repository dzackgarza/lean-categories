/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Lattices.Valued.Semifan
public import Mathlib.LinearAlgebra.ExteriorPower.Basic
public import Mathlib.LinearAlgebra.ExteriorPower.Basis

/-!
# Members of the conical locus, their support spaces and their isotropic centres

E. Looijenga, *Compactifications defined by arrangements II: locally symmetric varieties of
  type IV*, arXiv math/0201218v2 (2002), text version `.tmp-sources/looijenga-math0201218v2.md`:

* **Definition 2.1, p. 10** (text line 279): the conical locus as the union of the cones `C_I` over
  the `ℚ`-isotropic subspaces `I` of `V`, a disjoint union inside `so(φ)(R) ≅ ⋀²V(R)`.
* **Definition 6.1, p. 28** (text line 769): the Σ-support space `V_σ` of a member `σ` of an
  admissible decomposition, in its two cases — case (i) a member of the fibre of a `ℚ`-isotropic
  line, which is not an isotropic half line, where `V_σ` is the subspace of `I^⊥` containing `I`
  corresponding to the span of `σ`; case (ii) the half line `C_{J,+}` of a `ℚ`-isotropic plane,
  where `V_σ` is the support space that condition (ii) makes independent of the line `I ⊆ J` —
  and the isotropic centre `I(σ) = V_σ ∩ V_σ^⊥`.
* **Example 6.2, p. 29** (text line 783): the support spaces of the Baily–Borel (facial)
  decomposition are `{0}` and the orthogonal complements of the nontrivial `ℚ`-isotropic
  subspaces.
* **Lemma 6.6, p. 30** (text line 821): for a refinement, `V_σ ⊆ V_{σ'}`.

## What this file adds

`ConicalLocus.ConicalLine` carries the fibre of one `ℚ`-isotropic line and
`ConicalLocus.vSigma`/`vSigmaPlane` the two cases of Definition 6.1 separately. A member of the
conical locus, however, is one object of the union of Definition 2.1, and both Definition 6.1's
`V_σ`/`I(σ)` and Lemma 6.6's inclusion are statements about that object across fibres. This file
supplies

* `ConicalMember`: **the common member type** — the apex `{0}` (the member `C_{{0}}` of Definition
  2.1), a cone in the fibre of a `ℚ`-isotropic line (Definition 6.1 case (i)), and the half line
  `C_{J,+}` of a `ℚ`-isotropic plane (case (ii)), the latter with the witnessing line `I ⊆ J` that
  the source's condition (ii) makes immaterial, *together with the coherence of the fibre's sheet
  with the plane's orientation* (`ConicalPlane.IsPositiveAt`): the two are independent data, and
  without the coherence the same oriented plane presents, in the fibre with the opposite sheet, as
  the antipodal half line — `tests/regression/ConicalPlaneSplit22.lean` computes both carriers of
  the two sheets of one fibre;
* `ConicalMember.vSigma` and `ConicalMember.isotropicCenter`: `V_σ` and `I(σ)` **for every member**,
  in all three cases, the plane case taken relative to the decomposition as the source says
  ("this space not only depends on σ, but also on Σ");
* `ConicalMember.vSigma_plane_witness`: condition (ii) of Definition 6.1 as the statement that the
  plane member's support space does not depend on the witnessing line, so that `V_σ` is a function
  of the plane;
* `ConicalMember.vSigma_mono_member`: **Lemma 6.6** for the member-level containments — the apex
  below everything, and the fibre and plane cases of the refinement;
* **the conical locus inside `⋀²V(ℝ)`** (Definition 2.1, p. 10): `wedgeTwo`/`wedgeLeft` are the
  inclusion `e ⊗ c ↦ e ∧ c` of a fibre `I^⊥/I` into `⋀²V(ℝ)`, `ConicalMember.carrier` is the image
  of every member there, `conicalLocusSet` is the source's union, and
  `ConicalMember.carrier_plane_eq_fibre` / `carrier_plane_le_fibre_closure` are §1B's identification
  of the two presentations of a half line and the sentence "`C_J` is contained in the boundary of
  `C_I`", and `carrier_plane_eq_positiveRay` is the carrier itself: at a coherent presentation the
  plane member is carried to the closed ray `{t • r_J | 0 ≤ t}` of the positive generator of
  Example 6.3, p. 29 (with `wedgeTwo_dir_ne_zero`: that generator is not zero), so two witnessing
  lines of one plane give the same carrier (`ConicalMember.carrier_plane_eq_of_witness`);
* **Example 6.2 in all three cases**: `vSigma` of the fibre's closed cone and of its open cone is
  `I^⊥` (`ConicalLine.vSigma_closure_eq_ker`, `ConicalLine.vSigma_cone_eq_ker`), of a plane's half
  line is `J^⊥` (`ConicalLine.vSigmaPlane_eq_ker_inf_ker`, in `Semifan`), and of the apex is `{0}`;
  with the isotropic centres `I(σ) = I` for the fibre's own cone, `J` for the plane's half line and
  `{0}` for the apex, the `dim I(σ) = 1` (torus) and `dim I(σ) = 2` (abelian varieties) cases of the
  source's `X(σ)`.

## Why the support space of `C_I` needs a proof

Definition 6.1 case (i) takes the *span* of the member inside the fibre, so `V_{C_I} = I^⊥` is the
statement that the closed sheet of a form of signature `(1, n-1)` spans its space.
`span_upper_eq_top` proves it without any signature hypothesis: for any `t` with `Q t > 0` and any
`x`, the vector
`x + t` is scaled onto the open sheet by a small positive multiple (`lam • x + t` with
`lam` bounded by `Q t / (2 * M)`, `M = |Q x| + 2 |x · t| + 1`), so `x` is a difference of two
points of the sheet. `ConicalLine.span_closure_eq_top` then transfers it to `C_{I,+}`, which
contains the open sheet of the fibre (`upper_subset_rationalClosure_closedSheet`).

## LC-09 search record (2026-11-20)

Formalization-corpus queries: `content:conical member` (5 files, Mathlib's import list only),
`content:semifan` (no file), `content:admissible decomposition conical locus` (one file, the
import list), `content:isotropic center` (Clifford-algebra centres, unrelated). Nothing to import:
neither Looijenga's conical locus, its members, nor a semifan is formalized in the corpus. The
sub-lemmas were searched in Mathlib on disk as well: `span` of an open sheet of a quadratic cone
(`positiveCone`, `closedSheet`: no span statement, hence `span_upper_eq_top`), and the orthogonal
complement of an isotropic line as the span of the line and the reduced fibre
(`LinearMap.BilinForm.orthogonal` has `mem_orthogonal_iff` but no such decomposition, hence
`lineSpan_sup_realify_eq_ker`).

## References

* E. Looijenga, *Compactifications defined by arrangements II*, arXiv math/0201218v2 (2002), §1B
  (p. 11), §2 (Definition 2.1, p. 10), §4 (Lemma-Definition 4.5), §6 (Definition 6.1, p. 28,
  Example 6.2, p. 29, Lemma 6.6, p. 30).
* V. Alexeev, P. Engel, *Compact moduli of K3 surfaces*, arXiv 2101.12186v2 (2021), Definition 7.14,
  p. 46: the same object as a semifan.
-/

@[expose] public section

open PointedCone QuadraticMap

open scoped TensorProduct

namespace LeanCategories.Lattices.Valued

variable {V : Type} [AddCommGroup V] [Module ℚ V] [Module.Finite ℚ V]

/-! ## The open sheet of a quadratic cone spans -/

omit [Module.Finite ℚ V] in
/-- **A vector scaled towards a positive vector lies on the open sheet.** For `t` with `Q t > 0`
and any `x` there is a nonzero `lam` with `lam • x + t` on the open upper sheet of `Q` at `t`. The
bound is explicit: `lam = min (1/2) (Q t / (2 M))` with `M = |Q x| + 2 |x · t| + 1`, so that
`lam ^ 2 * Q x + 2 * lam * (x · t) + Q t >= Q t / 2`. -/
theorem exists_smul_add_mem_upper {Q : QuadraticForm ℝ (realified V)} {t : realified V}
    (ht : 0 < Q t) (x : realified V) :
    ∃ lam : ℝ, lam ≠ 0 ∧ lam • x + t ∈ positiveCone.upper Q t := by
  classical
  set B : ℝ := (associated Q) x t with hBdef
  set M : ℝ := |Q x| + 2 * |B| + 1 with hMdef
  have hMpos : 0 < M := by
    have h1 := abs_nonneg (Q x); have h2 := abs_nonneg B; linarith
  set lam : ℝ := min (1 / 2) (Q t / (2 * M)) with hlamdef
  have hlam_pos : 0 < lam := lt_min (by norm_num) (by positivity)
  have hlam_le : lam ≤ 1 / 2 := min_le_left _ _
  have hlam_small : lam * M ≤ Q t / 2 := by
    have h2 : lam ≤ Q t / (2 * M) := min_le_right _ _
    have h3 := mul_le_mul_of_nonneg_right h2 hMpos.le
    rw [div_mul_eq_mul_div] at h3
    have h4 : Q t * M / (2 * M) = Q t / 2 := by field_simp
    rwa [h4] at h3
  have hlam_nonneg : 0 ≤ lam := hlam_pos.le
  have hlam_sq : lam * lam ≤ lam := by nlinarith
  have habsQ : 0 ≤ |Q x| := abs_nonneg _
  have habsB : 0 ≤ |B| := abs_nonneg _
  have hlow : -(lam * M) ≤ lam * lam * Q x + 2 * lam * B := by
    have ha : -(lam * |Q x|) ≤ lam * lam * Q x := by
      have h5 : lam * lam * (-|Q x|) ≤ lam * lam * Q x := by
        have := neg_abs_le (Q x)
        nlinarith [mul_nonneg (mul_nonneg hlam_nonneg hlam_nonneg) (abs_nonneg (Q x))]
      nlinarith [hlam_sq, habsQ, mul_nonneg hlam_nonneg habsQ]
    have hb : -(2 * (lam * |B|)) ≤ 2 * lam * B := by
      have := neg_abs_le B
      nlinarith [mul_nonneg hlam_nonneg habsB]
    have h2 : lam * |Q x| + 2 * (lam * |B|) ≤ lam * M := by
      have h6 : lam * M = lam * |Q x| + lam * (2 * |B|) + lam * 1 := by
        rw [hMdef]; ring
      rw [h6]
      linarith [habsB, habsQ, hlam_nonneg]
    linarith
  have hQy : 0 < Q (lam • x + t) := by
    have hexp := quadratic_expand Q lam 1 x t
    simp only [one_smul, one_pow, one_mul] at hexp
    rw [hexp]
    nlinarith [hlow, hlam_small]
  have hBy : 0 < (associated Q) (lam • x + t) t := by
    have hsplit : (associated Q) (lam • x + t) t = lam * B + Q t := by
      rw [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply, smul_eq_mul,
        QuadraticMap.associated_eq_self_apply]
    rw [hsplit]
    have h8 : -(lam * |B|) ≤ lam * B := by
      have := neg_abs_le B
      nlinarith [hlam_nonneg]
    have h9 : lam * |B| ≤ lam * M := by
      rw [hMdef]; nlinarith [habsQ, hlam_nonneg]
    nlinarith [h9, h8, hlam_small, hlam_nonneg]
  exact ⟨lam, hlam_pos.ne', hQy, hBy⟩

omit [Module.Finite ℚ V] in
/-- **The open upper sheet of a quadratic cone spans the whole space.** Every `x` is a difference of
two points of the sheet: `lam • x + t` lies on it for the `lam` of `exists_smul_add_mem_upper`, and
so does `t`. No signature or nondegeneracy hypothesis is used. -/
theorem span_upper_eq_top {Q : QuadraticForm ℝ (realified V)} {t : realified V}
    (ht : 0 < Q t) : Submodule.span ℝ (positiveCone.upper Q t : Set (realified V)) = ⊤ := by
  classical
  refine Submodule.eq_top_iff'.2 (fun x => ?_)
  obtain ⟨lam, hne, hy⟩ := exists_smul_add_mem_upper ht x
  have htmem : t ∈ positiveCone.upper Q t := by
    refine ⟨ht, ?_⟩
    have h2 : (associated Q) t t = Q t := by rw [QuadraticMap.associated_eq_self_apply]
    rw [h2]; exact ht
  have hsub : lam • x + t - t ∈
      Submodule.span ℝ (positiveCone.upper Q t : Set (realified V)) :=
    Submodule.sub_mem _ (Submodule.subset_span hy) (Submodule.subset_span htmem)
  have hx : x = lam⁻¹ • (lam • x + t - t) := by
    rw [add_sub_cancel_right, smul_smul, inv_mul_cancel₀ hne, one_smul]
  rw [hx]
  exact Submodule.smul_mem _ _ hsub

section FibreSpan

variable {BQ : LinearMap.BilinForm ℚ V} {Q : QuadraticForm ℝ (realified V)}

/-- **The fibre's closed rational closure spans the fibre** (Looijenga §1B, p. 11: `C_{I,+}` is the
closed sheet). It contains the open sheet, whose span is everything. -/
theorem ConicalLine.span_closure_eq_top (F : ConicalLine BQ Q)
    (hpos : sigPos (fibreForm Q F.space) = 1) :
    Submodule.span ℝ (F.closure : Set (realified ↥F.space)) = ⊤ := by
  refine le_antisymm le_top ?_
  rw [ConicalLine.closure_eq_closedSheet F hpos]
  rw [← span_upper_eq_top (Q := fibreForm Q F.space) F.sheet_pos]
  exact Submodule.span_mono (R := ℝ)
    (upper_subset_rationalClosure_closedSheet hpos F.sheet_pos)

omit [Module.Finite ℚ V] in
/-- The fibre's open cone spans the fibre as well. -/
theorem ConicalLine.span_cone_eq_top (F : ConicalLine BQ Q) :
    Submodule.span ℝ (F.cone : Set (realified ↥F.space)) = ⊤ := by
  have hle : (positiveCone.upper (fibreForm Q F.space) F.sheet : Set (realified ↥F.space)) ⊆
      (F.cone : Set (realified ↥F.space)) := by
    intro x hx
    exact PointedCone.subset_hull hx
  refine le_antisymm le_top ?_
  rw [← span_upper_eq_top (Q := fibreForm Q F.space) F.sheet_pos]
  exact Submodule.span_mono (R := ℝ) hle

end FibreSpan

/-! ## `I^⊥` as the span of the line and the fibre -/

section GenSpan

variable {BQ : LinearMap.BilinForm ℚ V} {Q : QuadraticForm ℝ (realified V)}

omit [Module.Finite ℚ V] in
/-- The generator of a fibre's line is isotropic, so the line lies in the kernel of its metric
dual. -/
theorem lineSpan_le_ker_gen (hBQ : ∀ u w : V,
    (associated Q) (rationalPoint u) (rationalPoint w) = (BQ u w : ℝ))
    (F : ConicalLine BQ Q) :
    lineSpan F ≤ LinearMap.ker ((associated Q) (rationalPoint F.gen)) := by
  rw [lineSpan, Submodule.span_le]
  intro x hx
  rw [Set.mem_singleton_iff] at hx
  subst hx
  change ((associated Q) (rationalPoint F.gen)) (rationalPoint F.gen) = 0
  rw [hBQ, F.gen_iso]
  norm_num

omit [Module.Finite ℚ V] in
/-- The fibre's carrier lies in the kernel of the metric dual of the fibre's generator: it is
orthogonal to the line. -/
theorem realify_le_ker_gen (hBQ : ∀ u w : V,
    (associated Q) (rationalPoint u) (rationalPoint w) = (BQ u w : ℝ))
    (F : ConicalLine BQ Q) :
    realify F.space ≤ LinearMap.ker ((associated Q) (rationalPoint F.gen)) := by
  intro x hx
  rw [mem_realify_iff] at hx
  have hsub : Submodule.span ℝ (rationalPoint '' (F.space : Set V)) ≤
      LinearMap.ker ((associated Q) (rationalPoint F.gen)) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨v, hv, rfl⟩
    change ((associated Q) (rationalPoint F.gen)) (rationalPoint v) = 0
    rw [hBQ, ((mem_planeComplement_iff BQ).1 hv).1]
    norm_num
  exact hsub hx

omit [Module.Finite ℚ V] in
/-- **`I^⊥ = I ⊔ I^⊥/I`**: the hyperplane orthogonal to a `ℚ`-isotropic line is spanned by the line
and the fibre's carrier. Both are inside the hyperplane (`lineSpan_le_ker_gen`,
`realify_le_ker_gen`); conversely a vector of the hyperplane, written along the decomposition
`V = (⟨e, f⟩^⊥) ⊔ ⟨e, f⟩`, has no component along the partner `f`. -/
theorem lineSpan_sup_realify_eq_ker (hBQ : ∀ u w : V,
    (associated Q) (rationalPoint u) (rationalPoint w) = (BQ u w : ℝ))
    (hBsym : BQ.IsSymm) (F : ConicalLine BQ Q) :
    lineSpan F ⊔ realify F.space = LinearMap.ker ((associated Q) (rationalPoint F.gen)) := by
  refine le_antisymm (sup_le (lineSpan_le_ker_gen hBQ F) (realify_le_ker_gen hBQ F)) ?_
  intro x hx
  have hx0 : ((associated Q) (rationalPoint F.gen)) x = 0 := hx
  have htop := realify_planeComplement_sup hBsym F.gen_iso F.partner_iso F.pairing
  have hx' : x ∈ realify F.space ⊔
      Submodule.span ℝ ({rationalPoint F.gen, rationalPoint F.partner} : Set (realified V)) := by
    rw [htop]; exact Submodule.mem_top
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hx'
  obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.1 hz
  have hy0 : ((associated Q) (rationalPoint F.gen)) y = 0 := realify_le_ker_gen hBQ F hy
  have hgen0 : (associated Q) (rationalPoint F.gen) (rationalPoint F.gen) = 0 := by
    rw [hBQ, F.gen_iso]; norm_num
  have hpair1 : (associated Q) (rationalPoint F.gen) (rationalPoint F.partner) = 1 := by
    rw [hBQ, F.pairing]; norm_num
  have hz0 : (associated Q) (rationalPoint F.gen) z = b := by
    rw [← hab]
    simp only [map_add, map_smul, smul_eq_mul, hgen0, hpair1]
    ring
  have hb : b = 0 := by
    have h5 : ((associated Q) (rationalPoint F.gen)) (y + z) = 0 := hx0
    rw [map_add] at h5
    rw [← hz0]
    linarith [hy0, h5]
  have hz' : z = a • rationalPoint F.gen := by
    rw [← hab, hb, zero_smul, add_zero]
  rw [hz']
  refine Submodule.add_mem _ (Submodule.mem_sup_right hy) ?_
  exact Submodule.mem_sup_left (Submodule.smul_mem _ _
    (Submodule.subset_span (Set.mem_singleton _)))

end GenSpan

/-! ## Example 6.2: the support space of a fibre's cone is `I^⊥` -/

section FibreVs

variable {BQ : LinearMap.BilinForm ℚ V} {Q : QuadraticForm ℝ (realified V)}

/-- **Example 6.2, p. 29, the fibre's closed cone**: the Σ-support space of `C_{I,+}` is `I^⊥`.
Definition 6.1 case (i) takes the span of the member inside the fibre, and `C_{I,+}` spans the fibre
(`ConicalLine.span_closure_eq_top`), so the subspace of `I^⊥` containing `I` is `I^⊥` itself. -/
theorem ConicalLine.vSigma_closure_eq_ker (hBQ : ∀ u w : V,
    (associated Q) (rationalPoint u) (rationalPoint w) = (BQ u w : ℝ))
    (hBsym : BQ.IsSymm) (F : ConicalLine BQ Q)
    (hpos : sigPos (fibreForm Q F.space) = 1) :
    vSigma F F.closure = LinearMap.ker ((associated Q) (rationalPoint F.gen)) := by
  have hmap : Submodule.map (realifyMap F.space)
      (Submodule.span ℝ (F.closure : Set (realified ↥F.space))) = realify F.space := by
    rw [ConicalLine.span_closure_eq_top F hpos, Submodule.map_top]
    rfl
  rw [vSigma, hmap]
  exact lineSpan_sup_realify_eq_ker hBQ hBsym F

omit [Module.Finite ℚ V] in
/-- **Example 6.2, p. 29, the fibre's open cone**: the support space of `C_I` is `I^⊥` as well. -/
theorem ConicalLine.vSigma_cone_eq_ker (hBQ : ∀ u w : V,
    (associated Q) (rationalPoint u) (rationalPoint w) = (BQ u w : ℝ))
    (hBsym : BQ.IsSymm) (F : ConicalLine BQ Q) :
    vSigma F F.cone = LinearMap.ker ((associated Q) (rationalPoint F.gen)) := by
  have hmap : Submodule.map (realifyMap F.space)
      (Submodule.span ℝ (F.cone : Set (realified ↥F.space))) = realify F.space := by
    rw [ConicalLine.span_cone_eq_top F, Submodule.map_top]
    rfl
  rw [vSigma, hmap]
  exact lineSpan_sup_realify_eq_ker hBQ hBsym F

end FibreVs

/-! ## The common member type of the conical locus

Definition 2.1 (p. 10) writes the conical locus as the union of the cones `C_I` over the
`ℚ`-isotropic subspaces `I` of `V`, with `I = {0}`, a line, or a plane. `ConicalMember` is that
union as a type: the apex `{0}` (the cone at `I = {0}`), a cone in the fibre of a `ℚ`-isotropic line
(Definition 6.1 case (i)), and the half line `C_{J,+}` of a `ℚ`-isotropic plane (case (ii)). The
plane member carries the witnessing line `I ⊆ J` because the source's condition (ii) is exactly the
statement that `V_σ` does not depend on it (`ConicalMember.vSigma_plane_witness`). -/

section Member

variable {BQ : LinearMap.BilinForm ℚ V} {Q : QuadraticForm ℝ (realified V)}

/-- **The members of the conical locus**, Looijenga Definition 2.1 (p. 10) and Definition 6.1
(p. 28): the apex, a member of the fibre of a `ℚ`-isotropic line, and the half line of a
`ℚ`-isotropic plane at a witnessing line of it.

The plane case carries the *coherence* of the two pieces of presentation data, not just their
incidence: the plane's orientation and the fibre's sheet are independent (`ConicalLine.sheet` and
its negative are different `ConicalLine`s both containing the plane's lines), and the source's
`C_J ⊂ ∂C_I` (§1B, p. 11) is the statement that the class of `r_J` pairs positively with the sheet
(`ConicalPlane.IsPositiveAt`). Without it the same oriented plane would present, through a fibre
with the opposite sheet, as the *antipodal* half line in `⋀²V(ℝ)` — which is not `C_J` —
`tests/regression/ConicalPlaneSplit22.lean` computes both carriers and shows they differ. A plane
member is therefore always a source-valid incidence presentation, and its carrier is the closed ray
of the positive generator (`ConicalMember.carrier_plane_eq_positiveRay`). -/
inductive ConicalMember (BQ : LinearMap.BilinForm ℚ V)
    (Q : QuadraticForm ℝ (realified V)) : Type
  /-- the apex `{0}`: the cone `C_{{0}}` at the zero isotropic subspace -/
  | zero : ConicalMember BQ Q
  /-- a cone in the fibre of a `ℚ`-isotropic line: Definition 6.1 case (i) -/
  | fibre (F : ConicalLine BQ Q) (σ : PointedCone ℝ (realified ↥F.space)) :
      ConicalMember BQ Q
  /-- the half line `C_{J,+}` of a `ℚ`-isotropic plane, at a witnessing `ℚ`-isotropic line
  `I ≤ J` whose sheet is coherent with the plane's orientation: Definition 6.1 case (ii) -/
  | plane (F : ConicalLine BQ Q) (G : ConicalPlane BQ) (h : F.line ≤ G.plane)
      (hcoh : G.IsPositiveAt F h) : ConicalMember BQ Q

namespace ConicalMember

/-- **The support space of a fibre member at the member type**: Definition 6.1 (i)'s span formula,
with the two degenerate shapes of the case reconciled. A member of a fibre that is the *zero* cone
is the apex `C_{{0}}` of Definition 2.1 — `ConicalMember.carrier` carries it to the same point
`{0}` of `⋀²V(ℝ)` as `ConicalMember.zero` (`ConicalMember.carrier_fibre_bot`) — so its support is
`{0}`, not the `lineSpan F` that the span formula returns at `σ = ⊥`: the formula is the source's
`V_σ` only for a nonzero member of the fibre that is not an isotropic half line (Definition 6.1,
p. 28, case (i)), and both degenerate shapes are excluded from that case (Looijenga routes the
half lines through case (ii)). -/
noncomputable def fibreVSigma (F : ConicalLine BQ Q)
    (σ : PointedCone ℝ (realified ↥F.space)) : Submodule ℝ (realified V) := by
  classical
  exact if σ = ⊥ then ⊥ else LeanCategories.Lattices.Valued.vSigma F σ

omit [Module.Finite ℚ V] in
/-- **The zero member of a fibre has the apex's support space**, removing the baseline defect that
assigned one and the same carrier `{0}` the two supports `{0}` and `lineSpan F`. -/
@[simp] theorem fibreVSigma_bot (F : ConicalLine BQ Q) :
    fibreVSigma F (⊥ : PointedCone ℝ (realified ↥F.space)) = ⊥ := by
  classical
  simp [fibreVSigma]

omit [Module.Finite ℚ V] in
/-- On a nonzero member of a fibre the member-level support space *is* Definition 6.1 (i)'s span
formula. -/
theorem fibreVSigma_of_ne {F : ConicalLine BQ Q}
    {σ : PointedCone ℝ (realified ↥F.space)} (h : σ ≠ ⊥) :
    fibreVSigma F σ = LeanCategories.Lattices.Valued.vSigma F σ := by
  classical
  simp [fibreVSigma, h]

/-- **the support space `V_σ` of every member of the conical locus**, Definition 6.1, p. 28. Case
(i) is `ConicalLocus.vSigma` of the fibre, taken at `fibreVSigma` so that the fibre's zero member
gets the apex's support; case (ii) is `ConicalLocus.vSigmaPlane`, which the source computes relative
to the decomposition (hence the argument `locus`); the apex is `{0}`, Definition 2.1's convention
`V_{{0}} = {0}`. -/
noncomputable def vSigma (hBsym : BQ.IsSymm)
    (locus : ∀ F : ConicalLine BQ Q, Set (PointedCone ℝ (realified ↥F.space))) :
    ConicalMember BQ Q → Submodule ℝ (realified V)
  | zero => ⊥
  | fibre F σ => fibreVSigma F σ
  | plane F G h _ => LeanCategories.Lattices.Valued.vSigmaPlane hBsym F (locus F) G h

/-- **the isotropic centre `I(σ) = V_σ ∩ V_σ^⊥`** of any member (Definition 6.1, p. 28). -/
noncomputable def isotropicCenter (hBsym : BQ.IsSymm)
    (locus : ∀ F : ConicalLine BQ Q, Set (PointedCone ℝ (realified ↥F.space)))
    (m : ConicalMember BQ Q) : Submodule ℝ (realified V) :=
  LeanCategories.Lattices.Valued.isotropicCenter Q (vSigma hBsym locus m)

omit [Module.Finite ℚ V] in
@[simp] theorem vSigma_zero (hBsym : BQ.IsSymm)
    (locus : ∀ F : ConicalLine BQ Q, Set (PointedCone ℝ (realified ↥F.space))) :
    vSigma hBsym locus zero = ⊥ := rfl

omit [Module.Finite ℚ V] in
/-- **Example 6.2, p. 29, the apex**: the isotropic centre of `{0}` is `{0}`. -/
theorem isotropicCenter_zero (hBsym : BQ.IsSymm)
    (locus : ∀ F : ConicalLine BQ Q, Set (PointedCone ℝ (realified ↥F.space))) :
    isotropicCenter hBsym locus zero = ⊥ := by
  rw [isotropicCenter, vSigma_zero]
  simp [LeanCategories.Lattices.Valued.isotropicCenter]

omit [Module.Finite ℚ V] in
/-- **Condition (ii) of Definition 6.1 as the well-definedness of `V_σ` for a plane member**: for an
admissible decomposition the support space of the half line `C_{J,+}` does not depend on the
witnessing `ℚ`-isotropic line `I ⊆ J`. The source calls this space `J_Σ` for that reason. -/
theorem vSigma_plane_witness {Γ : Set (V ≃ₗ[ℚ] V)}
    {locus : ∀ F : ConicalLine BQ Q, Set (PointedCone ℝ (realified ↥F.space))}
    (D : IsAdmissibleDecomposition BQ Q Γ locus) (hBsym : BQ.IsSymm)
    (F F' : ConicalLine BQ Q) (G : ConicalPlane BQ)
    (h : F.line ≤ G.plane) (h' : F'.line ≤ G.plane)
    (hcoh : G.IsPositiveAt F h) (hcoh' : G.IsPositiveAt F' h') :
    (plane F G h hcoh : ConicalMember BQ Q).vSigma hBsym locus =
      (plane F' G h' hcoh' : ConicalMember BQ Q).vSigma hBsym locus :=
  D.condition_ii hBsym F F' G h h'

omit [Module.Finite ℚ V] in
/-- **Lemma 6.6, p. 30, the apex case**: `V_σ ⊆ V_{σ'}` when `σ` is the apex. -/
theorem vSigma_zero_le (hBsym : BQ.IsSymm)
    (locus : ∀ F : ConicalLine BQ Q, Set (PointedCone ℝ (realified ↥F.space)))
    (m : ConicalMember BQ Q) :
    (zero : ConicalMember BQ Q).vSigma hBsym locus ≤ m.vSigma hBsym locus := by
  rw [vSigma_zero]
  exact bot_le

omit [Module.Finite ℚ V] in
/-- **The zero member of a fibre and the apex have the same support space**: the reconciliation of
the two presentations of the point `{0}` of the conical locus, and the statement that one carrier no
longer carries two support spaces. -/
@[simp] theorem vSigma_fibre_bot (hBsym : BQ.IsSymm)
    (locus : ∀ F : ConicalLine BQ Q, Set (PointedCone ℝ (realified ↥F.space)))
    (F : ConicalLine BQ Q) :
    (fibre F ⊥ : ConicalMember BQ Q).vSigma hBsym locus = ⊥ :=
  fibreVSigma_bot F

omit [Module.Finite ℚ V] in
/-- **Lemma 6.6, p. 30, the fibre case**: for two members of the fibre of one `ℚ`-isotropic line
with `σ ⊆ σ'`, the support spaces are nested — the containment of the members gives the containment
of their spans. The zero member is the apex on both sides, so it is handled separately
(`vSigma_fibre_bot`). -/
theorem vSigma_fibre_mono (hBsym : BQ.IsSymm)
    (locus : ∀ F : ConicalLine BQ Q, Set (PointedCone ℝ (realified ↥F.space)))
    (F : ConicalLine BQ Q) {σ σ' : PointedCone ℝ (realified ↥F.space)} (h : σ ≤ σ') :
    (fibre F σ : ConicalMember BQ Q).vSigma hBsym locus ≤
      (fibre F σ' : ConicalMember BQ Q).vSigma hBsym locus := by
  by_cases hσ : σ = ⊥
  · subst hσ
    rw [vSigma_fibre_bot]
    exact bot_le
  · have hσ' : σ' ≠ ⊥ := fun h' => hσ (le_bot_iff.1 (h' ▸ h))
    rw [show (fibre F σ : ConicalMember BQ Q).vSigma hBsym locus
        = LeanCategories.Lattices.Valued.vSigma F σ from fibreVSigma_of_ne hσ,
      show (fibre F σ' : ConicalMember BQ Q).vSigma hBsym locus
        = LeanCategories.Lattices.Valued.vSigma F σ' from fibreVSigma_of_ne hσ']
    exact vSigma_mono h

omit [Module.Finite ℚ V] in
/-- **Lemma 6.6, p. 30, the plane case**: for two decompositions of the fibre of `I`, the second
refining the first above the half line `C_{J,+}`, the support space of the plane member grows. This
is `Semifan.vSigmaPlane_le_of_refines` read at the member type: the plane member's `V_σ` is the
source's `J_Σ`, and it is monotone in `Σ`. -/
theorem vSigma_plane_mono_of_refines (hBsym : BQ.IsSymm) (F : ConicalLine BQ Q)
    (G : ConicalPlane BQ) (h : F.line ≤ G.plane) (hcoh : G.IsPositiveAt F h)
    {locus locus' : ∀ F : ConicalLine BQ Q, Set (PointedCone ℝ (realified ↥F.space))}
    (hidx : supportIndex (positiveCone.upper (fibreForm Q F.space) F.sheet) (locus F)
      (PointedCone.hull ℝ ({rationalPoint (fibreRay hBsym F G h)} :
        Set (realified ↥F.space))))
    (hrefines : ∀ τ' : supportIndex (positiveCone.upper (fibreForm Q F.space) F.sheet)
      (locus' F) (PointedCone.hull ℝ ({rationalPoint (fibreRay hBsym F G h)} :
        Set (realified ↥F.space))),
      ∃ τ ∈ locus F, PointedCone.hull ℝ ({rationalPoint (fibreRay hBsym F G h)} :
        Set (realified ↥F.space)) ≤ τ ∧ τ ≤ τ'.1 ∧
        ((τ : Set (realified ↥F.space)) ∩
          (positiveCone.upper (fibreForm Q F.space) F.sheet : Set (realified ↥F.space))).Nonempty) :
    (plane F G h hcoh : ConicalMember BQ Q).vSigma hBsym locus ≤
      (plane F G h hcoh : ConicalMember BQ Q).vSigma hBsym locus' :=
  vSigmaPlane_le_of_refines hBsym F G h hidx hrefines

end ConicalMember

end Member

/-! ## Example 6.2 at the member level, and the isotropic centres -/

section Example62Member

variable {BQ : LinearMap.BilinForm ℚ V} {Q : QuadraticForm ℝ (realified V)}

/-- **Example 6.2, p. 29, the plane member**: for the facial (Baily–Borel) decomposition the
support space of the half line `C_{J,+}` of a `ℚ`-isotropic plane is `J^⊥`, written as the common
kernel of the two forms of a spanning pair of `J` (`Semifan.vSigmaPlane_eq_ker_inf_ker`). The
source's "the support spaces are `{0}` and the orthogonal complements of the nontrivial
`ℚ`-isotropic subspaces". -/
theorem ConicalMember.vSigma_plane_facial (hBQ : ∀ u w : V,
    (associated Q) (rationalPoint u) (rationalPoint w) = (BQ u w : ℝ))
    (hBsym : BQ.IsSymm) (F : ConicalLine BQ Q) (G : ConicalPlane BQ)
    (h : F.line ≤ G.plane) (hcoh : G.IsPositiveAt F h)
    (hpos : ∀ F : ConicalLine BQ Q, sigPos (fibreForm Q F.space) = 1)
    (hnd : ∀ F : ConicalLine BQ Q, (fibreForm Q F.space).Nondegenerate) :
    (ConicalMember.plane F G h hcoh).vSigma hBsym (fun F => facialDecomposition F.closure) =
      LinearMap.ker ((associated Q) (rationalPoint F.gen)) ⊓
        LinearMap.ker ((associated Q) (rationalPoint (F.planeRay G h))) :=
  vSigmaPlane_eq_ker_inf_ker hBQ hBsym F G h (hpos F) (hnd F)

omit [Module.Finite ℚ V] in
/-- **Example 6.2, p. 29, the isotropic centre of a fibre's own cone**: `I(C_I) = I`. The support
space is `I^⊥` (`ConicalLine.vSigma_cone_eq_ker`), and the line of the fibre lies in it and in its
orthogonal complement because its generator is isotropic. This is the `dim I(σ) = 1` case of the
source, where `X(σ)` is an algebraic torus; the inclusion is stated, the dimension count `dim = 1`
is the source's and is not needed for it. -/
theorem ConicalMember.lineSpan_le_isotropicCenter_cone (hBQ : ∀ u w : V,
    (associated Q) (rationalPoint u) (rationalPoint w) = (BQ u w : ℝ))
    (hBsym : BQ.IsSymm) (F : ConicalLine BQ Q)
    (locus : ∀ F : ConicalLine BQ Q, Set (PointedCone ℝ (realified ↥F.space))) :
    lineSpan F ≤ (ConicalMember.fibre F F.cone).isotropicCenter hBsym locus := by
  have hne : (F.cone : PointedCone ℝ (realified ↥F.space)) ≠ ⊥ := by
    intro hbot
    have hmem : F.sheet ∈ (F.cone : PointedCone ℝ (realified ↥F.space)) :=
      PointedCone.subset_hull ⟨F.sheet_pos, by
        rw [QuadraticMap.associated_eq_self_apply]; exact F.sheet_pos⟩
    rw [hbot] at hmem
    have hzero : F.sheet = 0 := by simpa using hmem
    exact (ne_of_gt F.sheet_pos) (by rw [hzero]; simp)
  have hv : (ConicalMember.fibre F F.cone).vSigma hBsym locus
      = LeanCategories.Lattices.Valued.vSigma F F.cone := fibreVSigma_of_ne hne
  rw [ConicalMember.isotropicCenter, hv, ConicalLine.vSigma_cone_eq_ker hBQ hBsym F,
    LeanCategories.Lattices.Valued.isotropicCenter]
  refine le_inf (lineSpan_le_ker_gen hBQ F) ?_
  refine Submodule.span_le.2 ?_
  intro x hx
  rw [Set.mem_singleton_iff] at hx
  subst hx
  refine LinearMap.BilinForm.mem_orthogonal_iff.2 ?_
  intro y hy
  rw [associated_comm Q y (rationalPoint F.gen)]
  exact hy

/-- **Example 6.2, p. 29, the isotropic centre of a plane's half line**: `J ⊆ I(C_{J,+})`. The
support space is `J^⊥`, and the plane is totally isotropic, so it lies in `J^⊥` and pairs to zero
with everything in it. This is the `dim I(σ) = 2` case of the source, where `X(σ)` is a bundle of
abelian varieties over a modular curve; the reverse inclusion would need the bound `dim ≤ 2` on
real isotropic subspaces (Looijenga §1, p. 11) and the description of `V_σ` for an arbitrary
admissible `Σ`, neither of which is used here. -/
theorem ConicalMember.realify_plane_le_isotropicCenter_facial (hBQ : ∀ u w : V,
    (associated Q) (rationalPoint u) (rationalPoint w) = (BQ u w : ℝ))
    (hBsym : BQ.IsSymm) (F : ConicalLine BQ Q) (G : ConicalPlane BQ)
    (h : F.line ≤ G.plane) (hcoh : G.IsPositiveAt F h)
    (hpos : ∀ F : ConicalLine BQ Q, sigPos (fibreForm Q F.space) = 1)
    (hnd : ∀ F : ConicalLine BQ Q, (fibreForm Q F.space).Nondegenerate) :
    realify G.plane ≤
      (ConicalMember.plane F G h hcoh).isotropicCenter hBsym
        (fun F => facialDecomposition F.closure) := by
  have hv := ConicalMember.vSigma_plane_facial hBQ hBsym F G h hcoh hpos hnd
  rw [ConicalMember.isotropicCenter, hv, LeanCategories.Lattices.Valued.isotropicCenter]
  set Kg := LinearMap.ker ((associated Q) (rationalPoint F.gen)) with hKg
  set Kr := LinearMap.ker ((associated Q) (rationalPoint (F.planeRay G h))) with hKr
  have hiso : BQ (F.planeRay G h) F.gen = 0 :=
    G.isotropic (F.planeRay G h) (F.planeRay_mem G h) F.gen (F.gen_mem_plane G h)
  have hgen : ((associated Q) (rationalPoint F.gen)) (rationalPoint (F.planeRay G h)) = 0 := by
    rw [hBQ, hBsym.eq, hiso]; norm_num
  have hraygen : ((associated Q) (rationalPoint (F.planeRay G h))) (rationalPoint F.gen) = 0 := by
    rw [hBQ, hiso]; norm_num
  have hgengen : ((associated Q) (rationalPoint F.gen)) (rationalPoint F.gen) = 0 := by
    rw [hBQ, F.gen_iso]; norm_num
  have hrayray : ((associated Q) (rationalPoint (F.planeRay G h)))
      (rationalPoint (F.planeRay G h)) = 0 := by
    rw [hBQ, F.planeRay_self G h]; norm_num
  have hspan : realify G.plane =
      Submodule.span ℝ ({rationalPoint F.gen, rationalPoint (F.planeRay G h)} :
        Set (realified V)) := by
    rw [← span_gen_ray_eq_plane F G h]
    exact realified_span_pair
  have h1 : realify G.plane ≤ Kg := by
    rw [hKg, hspan]
    refine (Submodule.span_le.2 ?_)
    rintro x (rfl | hx)
    · exact hgengen
    · rw [Set.mem_singleton_iff] at hx
      subst hx
      exact hgen
  have h2 : realify G.plane ≤ Kr := by
    rw [hKr, hspan]
    refine (Submodule.span_le.2 ?_)
    rintro x (rfl | hx)
    · exact hraygen
    · rw [Set.mem_singleton_iff] at hx
      subst hx
      exact hrayray
  have h3 : realify G.plane ≤ LinearMap.BilinForm.orthogonal (associated Q) (Kg ⊓ Kr) := by
    rw [hspan]
    refine Submodule.span_le.2 ?_
    rintro x (rfl | hx)
    · refine LinearMap.BilinForm.mem_orthogonal_iff.2 ?_
      intro y hy
      rw [associated_comm Q y (rationalPoint F.gen)]
      exact hy.1
    · rw [Set.mem_singleton_iff] at hx
      subst hx
      refine LinearMap.BilinForm.mem_orthogonal_iff.2 ?_
      intro y hy
      rw [associated_comm Q y (rationalPoint (F.planeRay G h))]
      exact hy.2
  exact le_inf (le_inf h1 h2) h3

end Example62Member

/-! ## Definition 2.1: the conical locus inside `⋀²V(ℝ)`

The conical locus is a subset of `so(φ)(ℝ) ≅ ⋀²V(ℝ)` (Definition 2.1, p. 10): the cone `C_I` of a
`ℚ`-isotropic line sits in `(I ⊗ I^⊥/I)(ℝ) ⊂ ⋀²V(ℝ)` through `e ⊗ c ↦ e ∧ c`, and the half line
`C_{J,+}` of a `ℚ`-isotropic plane sits in `⋀²J(ℝ) ⊂ ⋀²V(ℝ)` (§1B, p. 11, text line 267: "`Λ²J` can
be regarded as a line in `I ⊗ I^⊥/I`, and via this inclusion, `C_J` is contained in the boundary of
`C_I`"). `ConicalMember.carrier` is the image of each member there, and
`ConicalMember.carrier_plane_le_fibre_closure` is that sentence. -/

section Wedge

/-- The exterior product `a ∧ b` in `⋀²` of the real form of `V`. -/
noncomputable def wedgeTwo (a b : realified V) : ⋀[ℝ]^2 (realified V) :=
  exteriorPower.ιMulti ℝ 2 ![a, b]

/-- **`a ∧ ·` as a linear map** `⋀²V(ℝ)`: the map through which the fibre `I^⊥/I` of a
`ℚ`-isotropic line `I = ℚ a` sits in `⋀²V(ℝ)` (Looijenga §1B, p. 11). -/
noncomputable def wedgeLeft (a : realified V) : realified V →ₗ[ℝ] ⋀[ℝ]^2 (realified V) where
  toFun b := wedgeTwo a b
  map_add' b b' := by
    have h1 : (![a, b + b'] : Fin 2 → realified V) =
        Function.update ![a, b] 1 (b + b') := by
      funext i; fin_cases i <;> simp
    have h2 : Function.update (![a, b] : Fin 2 → realified V) 1 b = ![a, b] := by
      funext i; fin_cases i <;> simp
    have h3 : Function.update (![a, b] : Fin 2 → realified V) 1 b' = ![a, b'] := by
      funext i; fin_cases i <;> simp
    rw [wedgeTwo, h1, AlternatingMap.map_update_add, h2, h3]
    rfl
  map_smul' c b := by
    have h1 : (![a, c • b] : Fin 2 → realified V) = Function.update ![a, b] 1 (c • b) := by
      funext i; fin_cases i <;> simp
    have h2 : Function.update (![a, b] : Fin 2 → realified V) 1 b = ![a, b] := by
      funext i; fin_cases i <;> simp
    rw [wedgeTwo, h1, AlternatingMap.map_update_smul, h2]
    rfl

omit [Module.Finite ℚ V] in
@[simp] theorem wedgeLeft_apply (a b : realified V) : wedgeLeft a b = wedgeTwo a b := rfl

omit [Module.Finite ℚ V] in
omit [Module.Finite ℚ V] in
theorem wedgeTwo_self (a : realified V) : wedgeTwo a a = 0 := by
  rw [wedgeTwo]
  exact AlternatingMap.map_eq_zero_of_eq (f := exteriorPower.ιMulti ℝ 2) (v := ![a, a])
    (i := (0 : Fin 2)) (j := 1) (by rfl) (by decide)

omit [Module.Finite ℚ V] in
theorem wedgeTwo_add_left (x y b : realified V) :
    wedgeTwo (x + y) b = wedgeTwo x b + wedgeTwo y b := by
  have h1 : (![x + y, b] : Fin 2 → realified V) = Function.update ![x, b] 0 (x + y) := by
    funext i; fin_cases i <;> simp
  have h2 : Function.update (![x, b] : Fin 2 → realified V) 0 x = ![x, b] := by
    funext i; fin_cases i <;> simp
  have h3 : Function.update (![x, b] : Fin 2 → realified V) 0 y = ![y, b] := by
    funext i; fin_cases i <;> simp
  rw [wedgeTwo, h1, AlternatingMap.map_update_add, h2, h3]
  rfl

omit [Module.Finite ℚ V] in
theorem wedgeTwo_smul_left (c : ℝ) (x b : realified V) :
    wedgeTwo (c • x) b = c • wedgeTwo x b := by
  have h1 : (![c • x, b] : Fin 2 → realified V) = Function.update ![x, b] 0 (c • x) := by
    funext i; fin_cases i <;> simp
  have h2 : Function.update (![x, b] : Fin 2 → realified V) 0 x = ![x, b] := by
    funext i; fin_cases i <;> simp
  rw [wedgeTwo, h1, AlternatingMap.map_update_smul, h2]
  rfl

omit [Module.Finite ℚ V] in
theorem wedgeTwo_swap (x y : realified V) : wedgeTwo y x = -wedgeTwo x y := by
  have h := AlternatingMap.map_swap_add (f := exteriorPower.ιMulti ℝ 2)
    (v := ![x, y]) (i := (0 : Fin 2)) (j := 1) (by decide)
  have h2 : (![x, y] : Fin 2 → realified V) ∘ Equiv.swap (0 : Fin 2) 1 = ![y, x] := by
    funext i; fin_cases i <;> rfl
  rw [h2] at h
  exact eq_neg_of_add_eq_zero_left (by simpa [wedgeTwo] using h)

omit [Module.Finite ℚ V] in
theorem wedgeTwo_linear_comb (a b c d : ℝ) (x y : realified V) :
    wedgeTwo (a • x + b • y) (c • x + d • y) = (a * d - b * c) • wedgeTwo x y := by
  have h1 : wedgeTwo (a • x + b • y) x = -(b • wedgeTwo x y) := by
    rw [wedgeTwo_add_left, wedgeTwo_smul_left, wedgeTwo_smul_left, wedgeTwo_self, wedgeTwo_swap]
    module
  have h2 : wedgeTwo (a • x + b • y) y = a • wedgeTwo x y := by
    rw [wedgeTwo_add_left, wedgeTwo_smul_left, wedgeTwo_smul_left, wedgeTwo_self, wedgeTwo_swap]
    module
  have hlin : wedgeTwo (a • x + b • y) (c • x + d • y)
      = wedgeLeft (a • x + b • y) (c • x + d • y) := rfl
  rw [hlin, map_add, map_smul, map_smul, wedgeLeft_apply, wedgeLeft_apply, h1, h2]
  module

omit [Module.Finite ℚ V] in
theorem wedgeTwo_add_right (a b c : realified V) :
    wedgeTwo a (b + c) = wedgeTwo a b + wedgeTwo a c := by
  rw [wedgeTwo_swap, wedgeTwo_add_left, wedgeTwo_swap a b, wedgeTwo_swap a c]
  abel

omit [Module.Finite ℚ V] in
theorem wedgeTwo_smul_right (c : ℝ) (a b : realified V) :
    wedgeTwo a (c • b) = c • wedgeTwo a b := by
  rw [wedgeTwo_swap, wedgeTwo_smul_left, wedgeTwo_swap a b, smul_neg, neg_neg]

section RayOf

variable {BQ : LinearMap.BilinForm ℚ V}

omit [Module.Finite ℚ V] in
/-- **`g ∧ ρ = r_J`**: the ray of the oriented plane in the fibre of a witnessing line `I = ℚ g` is
the vector whose exterior product with `g` is the positive generator `r_J = dir ∧ dirAlt` of
`⋀²J(ℚ)` — §1B, p. 11, "`Λ²J` can be regarded as a line in `I ⊗ I^⊥/I`". So the class of the ray
in `I^⊥/I` is the image of `r_J` and not of `-r_J`. -/
theorem wedgeTwo_rayOf (G : ConicalPlane BQ) {g : V} (hg : g ∈ G.plane) (hg0 : g ≠ 0) :
    wedgeTwo (rationalPoint g) (rationalPoint (G.rayOf g hg hg0)) =
      wedgeTwo (rationalPoint G.dir) (rationalPoint G.dirAlt) := by
  set a : ℚ := G.basis.repr ⟨g, hg⟩ 0 with ha
  set b : ℚ := G.basis.repr ⟨g, hg⟩ 1 with hb
  have hrp : rationalPoint g =
      (a : ℝ) • rationalPoint G.dir + (b : ℝ) • rationalPoint G.dirAlt := by
    rw [show g = a • G.dir + b • G.dirAlt from G.repr_eq ⟨g, hg⟩, map_add,
      rationalPoint_rat_smul, rationalPoint_rat_smul]
  by_cases h : a = 0
  · have hb0 : b ≠ 0 := G.repr_one_ne_zero_of_repr_zero_eq_zero hg hg0 h
    have hρ : rationalPoint (G.rayOf g hg hg0) = (-(b : ℝ)⁻¹) • rationalPoint G.dir := by
      rw [G.rayOf_eq_smul_dir hg hg0 h, rationalPoint_rat_smul]
      norm_cast
    have hpad : (-(b : ℝ)⁻¹) • rationalPoint G.dir
        = (-(b : ℝ)⁻¹) • rationalPoint G.dir + (0 : ℝ) • rationalPoint G.dirAlt := by
      rw [zero_smul, add_zero]
    rw [hrp, hρ, hpad, wedgeTwo_linear_comb]
    have hcoef : ((a : ℚ) : ℝ) * 0 - (b : ℝ) * (-(b : ℝ)⁻¹) = 1 := by
      rw [show ((a : ℚ) : ℝ) = 0 by rw [h]; norm_num]
      have hbR : (b : ℝ) ≠ 0 := by exact_mod_cast hb0
      field_simp
      norm_num
    rw [hcoef, one_smul]
  · have hρ : rationalPoint (G.rayOf g hg hg0) = ((a : ℚ) : ℝ)⁻¹ • rationalPoint G.dirAlt := by
      rw [G.rayOf_eq_smul_dirAlt hg hg0 h, rationalPoint_rat_smul]
      norm_cast
    have hpad : ((a : ℚ) : ℝ)⁻¹ • rationalPoint G.dirAlt
        = (0 : ℝ) • rationalPoint G.dir + ((a : ℚ) : ℝ)⁻¹ • rationalPoint G.dirAlt := by
      rw [zero_smul, zero_add]
    rw [hrp, hρ, hpad, wedgeTwo_linear_comb]
    have hcoef : ((a : ℚ) : ℝ) * ((a : ℚ) : ℝ)⁻¹ - (b : ℝ) * 0 = 1 := by
      have haR : ((a : ℚ) : ℝ) ≠ 0 := by exact_mod_cast h
      field_simp
      norm_num
    rw [hcoef, one_smul]

omit [Module.Finite ℚ V] in
/-- In `⋀²` of the real form of a plane, the wedge of the two vectors of the positive basis is the
basis vector at the full set of the two indices of the basis of the plane, hence not zero. -/
theorem wedgeTwo_planeBasis_ne_zero (G : ConicalPlane BQ) :
    wedgeTwo (rationalPoint (G.basis 0)) (rationalPoint (G.basis 1)) ≠ 0 := by
  classical
  have hcard : (Finset.univ : Finset (Fin 2)).card = 2 := by simp
  set s : Set.powersetCard (Fin 2) 2 := ⟨(Finset.univ : Finset (Fin 2)), hcard⟩ with hs
  have hne : ((G.basis.baseChange ℝ).exteriorPower 2) s ≠ 0 := Module.Basis.ne_zero _ s
  rw [exteriorPower.basis_apply ℝ 2 (G.basis.baseChange ℝ) s] at hne
  have hidx' : (id : Fin 2 → Fin 2) =
      Finset.orderEmbOfFin (Finset.univ : Finset (Fin 2)) hcard :=
    Finset.orderEmbOfFin_unique hcard (fun x => Finset.mem_univ x) strictMono_id
  have hidx : ∀ i, Set.powersetCard.ofFinEmbEquiv.symm s i = i := by
    intro i
    rw [Set.powersetCard.ofFinEmbEquiv_symm_apply, ← hidx']
    rfl
  have hfun : (⇑(G.basis.baseChange ℝ) ∘ Set.powersetCard.ofFinEmbEquiv.symm s) =
      ![rationalPoint (G.basis 0), rationalPoint (G.basis 1)] := by
    funext i
    rw [Function.comp_apply, hidx i]
    fin_cases i <;> simp [Module.Basis.baseChange_apply, rationalPoint_apply]
  rw [exteriorPower.ιMulti_family, hfun] at hne
  exact hne

omit [Module.Finite ℚ V] in
/-- **The positive rational generator `r_J = dir ∧ dirAlt` of an oriented plane is not zero**: by
Example 6.3, p. 29, it generates the line `⋀²J(ℚ)`, so the two half lines of `⋀²J(ℝ) − {0}` are its
positive and negative multiples, and `{t • r_J | 0 ≤ t}` is one of them. -/
theorem wedgeTwo_dir_ne_zero (G : ConicalPlane BQ) :
    wedgeTwo (rationalPoint G.dir) (rationalPoint G.dirAlt) ≠ 0 := by
  classical
  have hne := wedgeTwo_planeBasis_ne_zero G
  have hinj : Function.Injective ⇑(exteriorPower.map 2 (realifyMap G.plane)) :=
    exteriorPower.map_injective_field (realifyMap_injective G.plane)
  have hmap : exteriorPower.map 2 (realifyMap G.plane)
      (wedgeTwo (rationalPoint (G.basis 0)) (rationalPoint (G.basis 1))) =
      wedgeTwo (rationalPoint G.dir) (rationalPoint G.dirAlt) := by
    rw [wedgeTwo, wedgeTwo, exteriorPower.map_apply_ιMulti]
    congr 1
    funext i
    fin_cases i <;>
      simp [ConicalPlane.dir, ConicalPlane.dirAlt, realifyMap_rationalPoint]
  intro h
  exact hne (hinj (by rw [hmap, map_zero]; exact h))

end RayOf


section Carrier

variable {BQ : LinearMap.BilinForm ℚ V} {Q : QuadraticForm ℝ (realified V)}

/-- **The image of a member in `⋀²V(ℝ)`**, Definition 2.1, p. 10. The apex is `{0}`; a cone in the
fibre of a `ℚ`-isotropic line `ℚ e` is carried by `c ↦ e ∧ c` (the inclusion
`(I ⊗ I^⊥/I)(ℝ) ⊂ ⋀²V(ℝ)` of §1B); the half line `C_{J,+}` of a plane at a witnessing line `I` is
carried the same way, through the class of `J` in the fibre of `I` (`Λ²J ⊂ I ⊗ I^⊥/I`), so that the
two presentations of the same half line give the same subset of `⋀²V(ℝ)`
(`ConicalMember.carrier_plane_eq_fibre`). -/
noncomputable def ConicalMember.carrier (hBsym : BQ.IsSymm) :
    ConicalMember BQ Q → Set (⋀[ℝ]^2 (realified V))
  | zero => {0}
  | fibre F σ => wedgeLeft (rationalPoint F.gen) ''
      ((fun c : realified ↥F.space => realifyMap F.space c) '' (σ : Set (realified ↥F.space)))
  | plane F G hw _ => wedgeLeft (rationalPoint F.gen) ''
      ((fun c : realified ↥F.space => realifyMap F.space c) ''
        (PointedCone.hull ℝ ({rationalPoint (fibreRay hBsym F G hw)} :
          Set (realified ↥F.space)) : Set (realified ↥F.space)))

omit [Module.Finite ℚ V] in
/-- The pointed hull of a singleton is the closed ray generated by the vector. -/
theorem mem_hull_singleton {M : Type*} [AddCommGroup M] [Module ℝ M] {x y : M} :
    y ∈ (PointedCone.hull ℝ ({x} : Set M) : Set M) ↔ ∃ t : ℝ, 0 ≤ t ∧ t • x = y := by
  rw [PointedCone.hull, SetLike.mem_coe, Submodule.mem_span_singleton]
  exact ⟨fun ⟨a, ha⟩ => ⟨(a : ℝ), a.2, ha⟩, fun ⟨t, ht, h⟩ => ⟨⟨t, ht⟩, h⟩⟩

omit [Module.Finite ℚ V] in
/-- The wedge with a zero right factor vanishes. -/
theorem wedgeTwo_zero_right (a : realified V) : wedgeTwo a 0 = 0 := by
  have h : wedgeTwo a (0 : realified V) = wedgeTwo a ((0 : ℝ) • (0 : realified V)) := by
    rw [zero_smul]
  rw [h, wedgeTwo_smul_right, zero_smul]

omit [Module.Finite ℚ V] in
/-- **The zero member of a fibre is carried to the apex**: both are the single point `{0}` of
`⋀²V(ℝ)`. With `ConicalMember.vSigma_fibre_bot` this is the pair of facts that reconciles the two
presentations of that point: one carrier, one support space. It is also why the apex is the *only*
member of an admissible decomposition carried to `{0}`: the fibre's zero member is the apex, and it
is not a case-(i) member (`not_isCaseIFibre_bot`). -/
@[simp] theorem ConicalMember.carrier_fibre_bot (hBsym : BQ.IsSymm) (F : ConicalLine BQ Q) :
    (ConicalMember.fibre F (⊥ : PointedCone ℝ (realified ↥F.space)) :
        ConicalMember BQ Q).carrier hBsym =
      (ConicalMember.zero : ConicalMember BQ Q).carrier hBsym := by
  ext x
  constructor
  · intro hx
    obtain ⟨y, hy, rfl⟩ := hx
    obtain ⟨c, hc, rfl⟩ := hy
    have hc0 : c = 0 := by simpa using hc
    subst hc0
    change wedgeTwo (rationalPoint F.gen) (realifyMap F.space 0) = 0
    rw [map_zero, wedgeTwo_zero_right]
  · intro hx
    have hx0 : x = 0 := by
      have hmem : x ∈ ({0} : Set (⋀[ℝ]^2 (realified V))) := hx
      simpa using hmem
    subst hx0
    refine ⟨realifyMap F.space 0, ⟨0, by simp, rfl⟩, ?_⟩
    rw [map_zero, wedgeLeft_apply, wedgeTwo_zero_right]
omit [Module.Finite ℚ V] in
/-- **The class of the plane's ray in the fibre, carried to `⋀²V(ℝ)` by `e ⊗ c ↦ e ∧ c`, is the
wedge `e ∧ ρ`** of the line's generator with the ray: the projection `fibreProj` moves the ray by a
multiple of `e`, which the wedge kills. -/
theorem wedgeLeft_fibreRayProj (hBsym : BQ.IsSymm) (F : ConicalLine BQ Q) (G : ConicalPlane BQ)
    (h : F.line ≤ G.plane) :
    wedgeLeft (rationalPoint F.gen)
        (realifyMap F.space (rationalPoint (fibreRayProj hBsym F G h))) =
      wedgeTwo (rationalPoint F.gen) (rationalPoint (F.planeRay G h)) := by
  rw [realifyMap_rationalPoint, fibreRayProj_val, map_sub, rationalPoint_rat_smul, map_sub,
    wedgeLeft_apply, wedgeLeft_apply, wedgeTwo_smul_right, wedgeTwo_self, smul_zero, sub_zero]

omit [Module.Finite ℚ V] in
/-- The same vector, written with the positive generator of the plane: `g ∧ ρ = r_J`
(`wedgeTwo_rayOf`). -/
theorem wedgeLeft_gen_fibreRayProj (hBsym : BQ.IsSymm) (F : ConicalLine BQ Q)
    (G : ConicalPlane BQ) (h : F.line ≤ G.plane) :
    wedgeLeft (rationalPoint F.gen)
        (realifyMap F.space (rationalPoint (fibreRayProj hBsym F G h))) =
      wedgeTwo (rationalPoint G.dir) (rationalPoint G.dirAlt) := by
  rw [wedgeLeft_fibreRayProj]
  exact wedgeTwo_rayOf G (F.gen_mem_of_le G h) F.gen_ne

omit [Module.Finite ℚ V] in
/-- **The carrier of a plane member at a witnessing line is the closed ray over the wedge of its
fibre half line with the line's generator**: `ConicalMember.carrier` carries the cone
`PointedCone.hull {fibreRay}` to `⋀²V(ℝ)` by the linear map `e ∧ ·`, and a linear image of the cone
hull of one vector is the cone hull of its image. -/
theorem ConicalMember.mem_carrier_plane_iff (hBsym : BQ.IsSymm) (F : ConicalLine BQ Q)
    (G : ConicalPlane BQ) (h : F.line ≤ G.plane) (hcoh : G.IsPositiveAt F h)
    (x : ⋀[ℝ]^2 (realified V)) :
    x ∈ (ConicalMember.plane F G h hcoh : ConicalMember BQ Q).carrier hBsym ↔
      ∃ t : ℝ, 0 ≤ t ∧ t • (wedgeLeft (rationalPoint F.gen)
        (realifyMap F.space (rationalPoint (fibreRay hBsym F G h)))) = x := by
  simp only [ConicalMember.carrier, Set.mem_image]
  constructor
  · rintro ⟨y, ⟨c, hc, rfl⟩, rfl⟩
    rw [mem_hull_singleton] at hc
    obtain ⟨t, ht, rfl⟩ := hc
    exact ⟨t, ht, by rw [map_smul, map_smul]⟩
  · rintro ⟨t, ht, rfl⟩
    refine ⟨realifyMap F.space (t • rationalPoint (fibreRay hBsym F G h)), ?_, ?_⟩
    · exact ⟨t • rationalPoint (fibreRay hBsym F G h),
        mem_hull_singleton.2 ⟨t, ht, rfl⟩, rfl⟩
    · rw [map_smul, map_smul]

omit [Module.Finite ℚ V] in
/-- **The carrier of a plane member at a coherent presentation is the closed ray of the positive
rational generator**: Example 6.3, p. 29, `r_J ∈ ⋀²J(ℚ)` generates `C_J`, and §1B, p. 11, embeds
`⋀²J` in the fibre of every line of `J`; with the sheet coherent with the orientation, the `C_J`
that arrives is the positive one. -/
theorem ConicalMember.carrier_plane_eq_positiveRay (hBsym : BQ.IsSymm) (F : ConicalLine BQ Q)
    (G : ConicalPlane BQ) (h : F.line ≤ G.plane) (hcoh : G.IsPositiveAt F h) :
    (ConicalMember.plane F G h hcoh : ConicalMember BQ Q).carrier hBsym =
      {x : ⋀[ℝ]^2 (realified V) |
        ∃ t : ℝ, 0 ≤ t ∧ t • wedgeTwo (rationalPoint G.dir) (rationalPoint G.dirAlt) = x} := by
  refine Set.ext fun x => ?_
  rw [ConicalMember.mem_carrier_plane_iff, Set.mem_ofPred]
  refine exists_congr fun t => ?_
  rw [fibreRay_eq_fibreRayProj_of_isPositiveAt hBsym F G h hcoh,
    wedgeLeft_gen_fibreRayProj hBsym F G h]

omit [Module.Finite ℚ V] in
/-- **The two source-valid presentations of a plane give the same carrier**: condition (ii) of
Definition 6.1 asks for independence of the line `I ⊆ J`, and at the level of the carrier in
`⋀²V(ℝ)` that is now a theorem — both coherent presentations carry `C_{J,+}` to the closed ray of
the same positive generator. -/
theorem ConicalMember.carrier_plane_eq_of_witness (hBsym : BQ.IsSymm) (F F' : ConicalLine BQ Q)
    (G : ConicalPlane BQ) (h : F.line ≤ G.plane) (h' : F'.line ≤ G.plane)
    (hcoh : G.IsPositiveAt F h) (hcoh' : G.IsPositiveAt F' h') :
    (ConicalMember.plane F G h hcoh : ConicalMember BQ Q).carrier hBsym =
      (ConicalMember.plane F' G h' hcoh' : ConicalMember BQ Q).carrier hBsym := by
  rw [ConicalMember.carrier_plane_eq_positiveRay hBsym F G h hcoh,
    ConicalMember.carrier_plane_eq_positiveRay hBsym F' G h' hcoh']

omit [Module.Finite ℚ V] in
/-- **The two presentations of a plane's half line give the same subset of `⋀²V(ℝ)`**: the plane
member and the fibre member whose cone is the class of the plane's ray are carried to the same
set — §1B, p. 11, "`Λ²J` can be regarded as a line in `I ⊗ I^⊥/I`". -/
theorem ConicalMember.carrier_plane_eq_fibre (hBsym : BQ.IsSymm)
    (F : ConicalLine BQ Q) (G : ConicalPlane BQ) (h : F.line ≤ G.plane)
    (hcoh : G.IsPositiveAt F h) :
    (ConicalMember.plane F G h hcoh : ConicalMember BQ Q).carrier hBsym =
      (ConicalMember.fibre F (PointedCone.hull ℝ
        ({rationalPoint (fibreRay hBsym F G h)} : Set (realified ↥F.space))) :
        ConicalMember BQ Q).carrier hBsym := rfl

omit [Module.Finite ℚ V] in
/-- A member of a fibre is carried into the carrier of a larger member of the same fibre. -/
theorem ConicalMember.carrier_fibre_mono (hBsym : BQ.IsSymm) (F : ConicalLine BQ Q)
    {σ σ' : PointedCone ℝ (realified ↥F.space)} (h : σ ≤ σ') :
    (ConicalMember.fibre F σ : ConicalMember BQ Q).carrier hBsym ⊆
      (ConicalMember.fibre F σ' : ConicalMember BQ Q).carrier hBsym := by
  rintro y ⟨z, hz, rfl⟩
  obtain ⟨c, hc, rfl⟩ := hz
  exact ⟨_, ⟨c, h hc, rfl⟩, rfl⟩

/-- **`C_J` lies in the boundary of `C_I`** (Looijenga §1B, p. 11, text line 267), in `⋀²V(ℝ)`:
the half line of a `ℚ`-isotropic plane is inside the carrier of the closure `C_{I,+}` of the fibre
of any of its lines. The class of the plane's ray is a point of `C_{I,+}`
(`fibreRay_mem_closure`), so the cone it generates is a subcone of the closure. -/
theorem ConicalMember.carrier_plane_le_fibre_closure (hBQ : ∀ u w : V,
    (associated Q) (rationalPoint u) (rationalPoint w) = (BQ u w : ℝ))
    (hBsym : BQ.IsSymm) (F : ConicalLine BQ Q) (G : ConicalPlane BQ) (h : F.line ≤ G.plane)
    (hcoh : G.IsPositiveAt F h) (hpos : sigPos (fibreForm Q F.space) = 1) :
    (ConicalMember.plane F G h hcoh : ConicalMember BQ Q).carrier hBsym ⊆
      (ConicalMember.fibre F F.closure : ConicalMember BQ Q).carrier hBsym := by
  rw [ConicalMember.carrier_plane_eq_fibre hBsym F G h hcoh]
  refine ConicalMember.carrier_fibre_mono hBsym F ?_
  rw [PointedCone.hull]
  refine Submodule.span_le.2 ?_
  intro x hx
  rw [Set.mem_singleton_iff] at hx
  subst hx
  exact fibreRay_mem_closure hBQ hBsym F G h hpos

/-- **The conical locus of Definition 2.1, p. 10, inside `⋀²V(ℝ)`**: the union of the apex, the open
cones `C_I` of the `ℚ`-isotropic lines and the half lines `C_{J,+}` of the `ℚ`-isotropic planes, the
latter at the presentations coherent with their orientation (`ConicalPlane.IsPositiveAt`). The
incoherent presentations would contribute the antipode of `C_J`, which is the conical locus of the
other component of `D` ("If we replace `D` by its complex conjugate (the other component), then the
conical locus is replaced by its antipode", Definition 2.1, p. 10). -/
noncomputable def conicalLocusSet (hBsym : BQ.IsSymm) : Set (⋀[ℝ]^2 (realified V)) :=
  ({0} : Set (⋀[ℝ]^2 (realified V))) ∪
    (⋃ (F : ConicalLine BQ Q),
      (ConicalMember.fibre F F.cone : ConicalMember BQ Q).carrier hBsym) ∪
    (⋃ (F : ConicalLine BQ Q) (G : ConicalPlane BQ) (h : F.line ≤ G.plane)
        (hcoh : G.IsPositiveAt F h),
      (ConicalMember.plane F G h hcoh : ConicalMember BQ Q).carrier hBsym)

omit [Module.Finite ℚ V] in
/-- The apex is a point of the conical locus. -/
theorem zero_mem_conicalLocusSet (hBsym : BQ.IsSymm) :
    (0 : ⋀[ℝ]^2 (realified V)) ∈ conicalLocusSet (Q := Q) hBsym := by
  simp [conicalLocusSet]

omit [Module.Finite ℚ V] in
/-- The open cone of every `ℚ`-isotropic line is part of the conical locus. -/
theorem carrier_cone_subset_conicalLocusSet (hBsym : BQ.IsSymm) (F : ConicalLine BQ Q) :
    (ConicalMember.fibre F F.cone : ConicalMember BQ Q).carrier hBsym ⊆
      conicalLocusSet (Q := Q) hBsym := by
  intro x hx
  exact Or.inl (Or.inr (Set.mem_iUnion.2 ⟨F, hx⟩))

omit [Module.Finite ℚ V] in
/-- The half line of every `ℚ`-isotropic plane is part of the conical locus. -/
theorem carrier_plane_subset_conicalLocusSet (hBsym : BQ.IsSymm)
    (F : ConicalLine BQ Q) (G : ConicalPlane BQ) (h : F.line ≤ G.plane)
    (hcoh : G.IsPositiveAt F h) :
    (ConicalMember.plane F G h hcoh : ConicalMember BQ Q).carrier hBsym ⊆
      conicalLocusSet (Q := Q) hBsym := by
  intro x hx
  exact Or.inr (Set.mem_iUnion.2 ⟨F, Set.mem_iUnion.2 ⟨G, Set.mem_iUnion.2
    ⟨h, Set.mem_iUnion.2 ⟨hcoh, hx⟩⟩⟩⟩)

end Carrier

end Wedge

end LeanCategories.Lattices.Valued
