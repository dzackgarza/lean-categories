/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Lattices.Valued.Semifan
public import Mathlib.LinearAlgebra.ExteriorPower.Basic

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
  the source's condition (ii) makes immaterial;
* `ConicalMember.vSigma` and `ConicalMember.isotropicCenter`: `V_σ` and `I(σ)` **for every member**,
  in all three cases, the plane case taken relative to the decomposition as the source says
  ("this space not only depends on σ, but also on Σ");
* `ConicalMember.vSigma_plane_witness`: condition (ii) of Definition 6.1 as the statement that the
  plane member's support space does not depend on the witnessing line, so that `V_σ` is a function
  of the plane;
* `ConicalMember.vSigma_mono_member`: **Lemma 6.6** for the member-level containments — the apex
  below everything, and the fibre and plane cases of the refinement;
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
`ℚ`-isotropic plane at a witnessing line of it. -/
inductive ConicalMember (BQ : LinearMap.BilinForm ℚ V)
    (Q : QuadraticForm ℝ (realified V)) : Type
  /-- the apex `{0}`: the cone `C_{{0}}` at the zero isotropic subspace -/
  | zero : ConicalMember BQ Q
  /-- a cone in the fibre of a `ℚ`-isotropic line: Definition 6.1 case (i) -/
  | fibre (F : ConicalLine BQ Q) (σ : PointedCone ℝ (realified ↥F.space)) :
      ConicalMember BQ Q
  /-- the half line `C_{J,+}` of a `ℚ`-isotropic plane, at a witnessing `ℚ`-isotropic line
  `I ≤ J`: Definition 6.1 case (ii) -/
  | plane (F : ConicalLine BQ Q) (G : ConicalPlane BQ) (h : F.line ≤ G.plane) :
      ConicalMember BQ Q

namespace ConicalMember

/-- **the support space `V_σ` of every member of the conical locus**, Definition 6.1, p. 28. Case
(i) is `ConicalLocus.vSigma` of the fibre; case (ii) is `ConicalLocus.vSigmaPlane`, which the
source computes relative to the decomposition (hence the argument `locus`); the apex is `{0}`,
Definition 2.1's convention `V_{{0}} = {0}`. -/
noncomputable def vSigma (hBsym : BQ.IsSymm)
    (locus : ∀ F : ConicalLine BQ Q, Set (PointedCone ℝ (realified ↥F.space))) :
    ConicalMember BQ Q → Submodule ℝ (realified V)
  | zero => ⊥
  | fibre F σ => LeanCategories.Lattices.Valued.vSigma F σ
  | plane F G h => LeanCategories.Lattices.Valued.vSigmaPlane hBsym F (locus F) G h

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
    (h : F.line ≤ G.plane) (h' : F'.line ≤ G.plane) :
    (plane F G h : ConicalMember BQ Q).vSigma hBsym locus =
      (plane F' G h' : ConicalMember BQ Q).vSigma hBsym locus :=
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
/-- **Lemma 6.6, p. 30, the fibre case**: for two members of the fibre of one `ℚ`-isotropic line
with `σ ⊆ σ'`, the support spaces are nested — the containment of the members gives the containment
of their spans. -/
theorem vSigma_fibre_mono (hBsym : BQ.IsSymm)
    (locus : ∀ F : ConicalLine BQ Q, Set (PointedCone ℝ (realified ↥F.space)))
    (F : ConicalLine BQ Q) {σ σ' : PointedCone ℝ (realified ↥F.space)} (h : σ ≤ σ') :
    (fibre F σ : ConicalMember BQ Q).vSigma hBsym locus ≤
      (fibre F σ' : ConicalMember BQ Q).vSigma hBsym locus :=
  vSigma_mono h

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
    (h : F.line ≤ G.plane)
    (hpos : ∀ F : ConicalLine BQ Q, sigPos (fibreForm Q F.space) = 1)
    (hnd : ∀ F : ConicalLine BQ Q, (fibreForm Q F.space).Nondegenerate) :
    (ConicalMember.plane F G h).vSigma hBsym (fun F => facialDecomposition F.closure) =
      LinearMap.ker ((associated Q) (rationalPoint F.gen)) ⊓
        LinearMap.ker ((associated Q) (rationalPoint G.ray)) :=
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
  have hv : (ConicalMember.fibre F F.cone).vSigma hBsym locus
      = LeanCategories.Lattices.Valued.vSigma F F.cone := rfl
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
    (h : F.line ≤ G.plane)
    (hpos : ∀ F : ConicalLine BQ Q, sigPos (fibreForm Q F.space) = 1)
    (hnd : ∀ F : ConicalLine BQ Q, (fibreForm Q F.space).Nondegenerate) :
    realify G.plane ≤
      (ConicalMember.plane F G h).isotropicCenter hBsym
        (fun F => facialDecomposition F.closure) := by
  have hv := ConicalMember.vSigma_plane_facial hBQ hBsym F G h hpos hnd
  rw [ConicalMember.isotropicCenter, hv, LeanCategories.Lattices.Valued.isotropicCenter]
  set Kg := LinearMap.ker ((associated Q) (rationalPoint F.gen)) with hKg
  set Kr := LinearMap.ker ((associated Q) (rationalPoint G.ray)) with hKr
  have hiso : BQ G.ray F.gen = 0 :=
    G.isotropic G.ray G.ray_mem F.gen (F.gen_mem_plane G h)
  have hgen : ((associated Q) (rationalPoint F.gen)) (rationalPoint G.ray) = 0 := by
    rw [hBQ, hBsym.eq, hiso]; norm_num
  have hraygen : ((associated Q) (rationalPoint G.ray)) (rationalPoint F.gen) = 0 := by
    rw [hBQ, hiso]; norm_num
  have hgengen : ((associated Q) (rationalPoint F.gen)) (rationalPoint F.gen) = 0 := by
    rw [hBQ, F.gen_iso]; norm_num
  have hrayray : ((associated Q) (rationalPoint G.ray)) (rationalPoint G.ray) = 0 := by
    rw [hBQ, ConicalPlane.ray_iso G]; norm_num
  have hspan : realify G.plane =
      Submodule.span ℝ ({rationalPoint F.gen, rationalPoint G.ray} : Set (realified V)) := by
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
      rw [associated_comm Q y (rationalPoint G.ray)]
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
  | plane F G _ => wedgeLeft (rationalPoint F.gen) ''
      ((fun c : realified ↥F.space => realifyMap F.space c) ''
        (PointedCone.hull ℝ ({rationalPoint (fibreRay hBsym F G)} :
          Set (realified ↥F.space)) : Set (realified ↥F.space)))

omit [Module.Finite ℚ V] in
/-- **The two presentations of a plane's half line give the same subset of `⋀²V(ℝ)`**: the plane
member and the fibre member whose cone is the class of the plane's ray are carried to the same
set — §1B, p. 11, "`Λ²J` can be regarded as a line in `I ⊗ I^⊥/I`". -/
theorem ConicalMember.carrier_plane_eq_fibre (hBsym : BQ.IsSymm)
    (F : ConicalLine BQ Q) (G : ConicalPlane BQ) (_h : F.line ≤ G.plane) :
    (ConicalMember.plane F G _h : ConicalMember BQ Q).carrier hBsym =
      (ConicalMember.fibre F (PointedCone.hull ℝ
        ({rationalPoint (fibreRay hBsym F G)} : Set (realified ↥F.space))) :
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
    (hpos : sigPos (fibreForm Q F.space) = 1) :
    (ConicalMember.plane F G h : ConicalMember BQ Q).carrier hBsym ⊆
      (ConicalMember.fibre F F.closure : ConicalMember BQ Q).carrier hBsym := by
  rw [ConicalMember.carrier_plane_eq_fibre]
  refine ConicalMember.carrier_fibre_mono hBsym F ?_
  rw [PointedCone.hull]
  refine Submodule.span_le.2 ?_
  intro x hx
  rw [Set.mem_singleton_iff] at hx
  subst hx
  exact fibreRay_mem_closure hBQ hBsym F G h hpos

/-- **The conical locus of Definition 2.1, p. 10, inside `⋀²V(ℝ)`**: the union of the apex, the open
cones `C_I` of the `ℚ`-isotropic lines and the half lines `C_{J,+}` of the `ℚ`-isotropic planes. -/
noncomputable def conicalLocusSet (hBsym : BQ.IsSymm) : Set (⋀[ℝ]^2 (realified V)) :=
  ({0} : Set (⋀[ℝ]^2 (realified V))) ∪
    (⋃ (F : ConicalLine BQ Q),
      (ConicalMember.fibre F F.cone : ConicalMember BQ Q).carrier hBsym) ∪
    (⋃ (F : ConicalLine BQ Q) (G : ConicalPlane BQ) (h : F.line ≤ G.plane),
      (ConicalMember.plane F G h : ConicalMember BQ Q).carrier hBsym)

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
    (F : ConicalLine BQ Q) (G : ConicalPlane BQ) (h : F.line ≤ G.plane) :
    (ConicalMember.plane F G h : ConicalMember BQ Q).carrier hBsym ⊆
      conicalLocusSet (Q := Q) hBsym := by
  intro x hx
  exact Or.inr (Set.mem_iUnion.2 ⟨F, Set.mem_iUnion.2 ⟨G, Set.mem_iUnion.2 ⟨h, hx⟩⟩⟩)

end Carrier

end Wedge

end LeanCategories.Lattices.Valued
