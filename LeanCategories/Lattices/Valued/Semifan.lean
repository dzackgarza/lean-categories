/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Lattices.Valued.ConicalLocus

/-!
# The semifan of a type IV domain

E. Looijenga, *Compactifications defined by arrangements II: locally symmetric varieties of
  type IV*, arXiv math/0201218v2 (2002), §6, text version
  `.tmp-sources/looijenga-math0201218v2.md`:

* **Definition 6.1, p. 28** (text line 769): an admissible decomposition of the conical locus, the
  `Σ`-support space `V_σ` of a member and its isotropic centre `I(σ) = V_σ ∩ V_σ^⊥`. The
  decomposition, the spaces `V_σ` and `I(σ)` are
  `ConicalLocus.IsAdmissibleDecomposition`, `ConicalLocus.vSigma`, `ConicalLocus.vSigmaPlane` and
  `ConicalLocus.isotropicCenter`.
* **Example 6.2, p. 29** (text line 783): the decomposition of the conical locus into its
  faces — the Baily–Borel decomposition — is admissible, "the support spaces are `{0}` and the
  orthogonal complements of the nontrivial `ℚ`-isotropic subspaces".
* **Lemma 6.6, p. 30** (text line 821): a refinement `Σ` of `Σ'` gives `V_σ ⊆ V_{σ'}` for the
  smallest member `σ'` of `Σ'` containing `σ`.

## The fibre form, and why it is the source's

A member of the conical locus is a cone in the fibre `I^⊥/I ⊗ I` of a `ℚ`-isotropic line `I`
(Definition 2.1, p. 10; `ConicalLocus.ConicalLine`), so every support space of §6 is computed with
the form on that fibre, not with the ambient form. Looijenga, §1B, p. 11 (text line 247): "Suppose
that `I` is a real isotropic line in `V`. Then the form on `I^⊥/I` induced by `φ` has signature
`(1, n-1)` ... As this signature remains `(1, n-1)`, the set of positive vectors is the union of a
cone and its antipode." That is the hypothesis under which §4 — Definitions 4.1 and 4.2 and
Lemma-Definition 4.5 — applies inside a fibre, and it is proved here rather than assumed:

* `realify_planeComplement_eq_planePerp`: the real form of the carrier `I^⊥/I` is *exactly* the
  orthogonal complement `IsotropicQuotientSignature.planePerp` of the hyperbolic plane `⟨e, f⟩`
  (`ConicalLocus.realify_planeComplement_le_planePerp` gives one inclusion; the other is the
  disjointness of `planeComplement` and the plane, `planeComplement_inf_span_pair`);
* `fibreFormIsometry`: the fibre form is the restriction of the ambient form to that real form, so
  `sigPos_fibreForm` is `IsotropicQuotientSignature.sigPos_restrict_planePerp`: a form of signature
  `(2, n)` has fibres of signature `(1, n-1)`;
* `fibreForm_nondegenerate`: the fibre form of a nondegenerate ambient form is nondegenerate.

With them, `sigmaSupportSpace_facialDecomposition_hull_eq_ker`
(`LocallyRationalDecomposition`, #159) applies in a fibre, and Example 6.2's support space of a
plane member — the value `V_σ` of case (ii) of Definition 6.1 — is `vSigmaPlane_eq_ker_inf_ker`:
the orthogonal complement `J^⊥` of the `ℚ`-isotropic plane `J`, written as the common kernel of the
two forms of a spanning pair. That is the "hyperplane orthogonal to a `ℚ`-isotropic line" of the
sentence after Lemma-Definition 4.5 (p. 19, text line 523), in the fibre `I^⊥/I` of a line of `J`.

## What is assumed, and where the source supplies it

* `IsGammaInvariantLocus` is a field of `IsAdmissibleDecomposition` and is *not* discharged here for
  the facial decomposition: transporting a fibre along an isometry of `V` is not constructed.
  The two conditions (i) and (ii) of Definition 6.1 and the support spaces are, and are the
  content of Example 6.2 below.
* `hray` in the theorems of §5: the half line `C_{J,+}` of a `ℚ`-isotropic plane `J` lies on the
  closed sheet of the fibre of a line `I ≤ J`. The source has this as part of its construction: "A
  real isotropic plane `J` in `V` containing `I` corresponds to a real isotropic line `J̄` in
  `I^⊥/I` and vice versa. In that case, `Λ²J` can be regarded as a line in `I ⊗ I^⊥/I` and via this
  inclusion, `C_J` is contained in the boundary of `C_I`" (§1B, p. 11, text line 267). The carrier
  `ConicalLines` and `ConicalPlane` of `ConicalLocus` record the two cones but not which half of the
  boundary of the other they occupy, so the half line's orientation is a named hypothesis.

## What is not here

* **The `Γ`-invariance of the facial decomposition** (`IsGammaInvariantLocus`), and with it
  Example 6.2 as a whole: transporting a conical fibre along an isometry of `V` — the choice of the
  transported sheet among the two components of the fibre's cone — is not constructed, so
  `IsAdmissibleDecomposition` keeps `gammaInvariant` as a hypothesis. The conditions (i) and (ii)
  of Definition 6.1 are proved (`bailyBorel_condition_i`,
  `bailyBorel_condition_ii`), as are the support spaces the example names.
* **Example 6.4, the admissible decomposition `Σ(H)` of an arithmetic arrangement** (p. 29, text
  line 791), and with it the identification `J_{Σ(H)} = J_H = J^⊥ ∩ ⋂_{H ∋ J} H`. Both are
  statements about the cells of the arrangement in a fibre, and the missing step is the one the
  source reads off the decomposition: the support space of the half line `C_{J,+}` relative to
  `Σ(H)` is the intersection of the hyperplanes containing it. In the facial decomposition that is
  `vSigmaPlane_eq_ker_inf_ker` — `I(σ) = V_σ ∩ V_σ^⊥` is then `J` — but for `Σ(H)` the forms
  cutting the walls out of the round cone are needed, and they are not constructed here.
* **Theorem 6.7** (`X^Σ` is a normal analytic space) is a later unit of the pipeline.

## References

* E. Looijenga, *Compactifications defined by arrangements II*, arXiv math/0201218v2 (2002), §1B
  (p. 11), §4 (Definitions 4.1 and 4.2, Lemma-Definition 4.5), §6 (Definition 6.1, p. 28; Examples
  6.2 and 6.4, p. 29; Lemma 6.6, p. 30).
* V. Alexeev, P. Engel, *Compact moduli of K3 surfaces*, arXiv 2101.12186v2 (2021), Definition 7.14,
  p. 46: the same object under the name semifan.

## LC-09 search record (2026-11-19)

Formalization-corpus queries, with the hits. `content:semifan`: no file — Looijenga's semifans are
not formalized in the corpus. `content:admissible decomposition conical locus`: one file,
Mathlib's `Mathlib.lean` (the import list; no match). `content:locally rational decomposition`:
TauCeti `Analysis/Convex/Polyhedron/Rational/Stratification/{Basic,Refinement}.lean`, already ported
as `LeanCategories/Analysis/Convex/SignCell.lean` and used by `LocallyRationalDecomposition`; the
finite-intersection and common-refinement statements ported there are what §7 below uses.
`content:supportSpace sigmaSupportSpace`: no file. `content:Nondegenerate restrict orthogonal
complement quadratic`: TauCeti `RepresentationTheory/Quiver/PathAlgebra/Quadratic/Orthogonal.lean`
on double orthogonals of path relations, nothing on a signature drop.
`content:sigPos orthogonal complement restriction quadratic form`: TauCeti
`LinearAlgebra/QuadraticForm/Signature.lean` with `LinearAlgebra/QuadraticForm/PosDef.lean`; no
statement that a restriction to an orthogonal complement drops the positive index by one, which is
this repository's `IsotropicQuotientSignature.sigPos_restrict_planePerp` and is what
`sigPos_fibreForm` uses. `content:signature add orthogonal decomposition quadratic`: only the
`TauCetiRoadmap` target files, no proof. `content:faces of a closed convex cone extreme ray`: no
match for the isotropic case. Nothing to import for the statements below.
-/

@[expose] public section

open PointedCone QuadraticMap

open scoped TensorProduct

namespace LeanCategories.Lattices.Valued

variable {V : Type} [AddCommGroup V] [Module ℚ V] [Module.Finite ℚ V]

/-! ## The carrier of a conical fibre is the orthogonal complement of its plane -/

section PlaneCarrier

variable {BQ : LinearMap.BilinForm ℚ V} {e f : V}

omit [Module.Finite ℚ V] in
/-- The carrier `I^⊥/I` of a conical fibre is disjoint from the hyperbolic plane `⟨e, f⟩` that
splits it off: a vector of the plane orthogonal to both `e` and `f` is zero, since `e · f = 1`. -/
theorem planeComplement_inf_span_pair (hBsym : BQ.IsSymm) (he : BQ e e = 0)
    (hf : BQ f f = 0) (hef : BQ e f = 1) :
    planeComplement BQ e f ⊓ Submodule.span ℚ ({e, f} : Set V) = ⊥ := by
  refine (Submodule.eq_bot_iff _).2 ?_
  rintro x hx
  obtain ⟨hxe, hxf⟩ := (mem_planeComplement_iff BQ).1 hx.1
  obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.1 hx.2
  have hfe : BQ f e = 1 := by rw [hBsym.eq]; exact hef
  have hb : b = 0 := by
    have h := hxe
    simp only [map_add, map_smul, smul_eq_mul, he, hef, mul_one, mul_zero, zero_add] at h
    exact h
  have ha : a = 0 := by
    have h := hxf
    simp only [map_add, map_smul, smul_eq_mul, hfe, hf, mul_one, mul_zero, add_zero] at h
    exact h
  rw [ha, hb, zero_smul, zero_smul, add_zero]

/-- **The real form of a conical fibre is the orthogonal complement of its hyperbolic plane.** For
`I = ℚ e` and a hyperbolic partner `f`, the reduction `I^⊥/I` of Looijenga §1B, p. 11, carried by
`ConicalLocus.planeComplement`, has real form exactly `planePerp Q e f`. -/
theorem realify_planeComplement_eq_planePerp {Q : QuadraticForm ℝ (realified V)}
    (hBQ : ∀ u w : V, (associated Q) (rationalPoint u) (rationalPoint w) = (BQ u w : ℝ))
    (hBsym : BQ.IsSymm) (he : BQ e e = 0) (hf : BQ f f = 0) (hef : BQ e f = 1) :
    realify (planeComplement BQ e f) = planePerp Q (rationalPoint e) (rationalPoint f) := by
  refine le_antisymm (realify_planeComplement_le_planePerp hBQ) ?_
  intro x hx
  have hsup := realify_planeComplement_sup hBsym he hf hef
  have hx' : x ∈ realify (planeComplement BQ e f) ⊔
      Submodule.span ℝ ({rationalPoint e, rationalPoint f} : Set (realified V)) := by
    rw [hsup]
    exact Submodule.mem_top
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hx'
  have hzp : z ∈ planePerp Q (rationalPoint e) (rationalPoint f) := by
    simpa using Submodule.sub_mem _ hx (realify_planeComplement_le_planePerp hBQ hy)
  obtain ⟨hze, hzf⟩ := mem_planePerp_iff.1 hzp
  obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.1 hz
  have hre : (associated Q) (rationalPoint e) (rationalPoint e) = 0 := by
    rw [hBQ e e, he]
    norm_num
  have hrf : (associated Q) (rationalPoint f) (rationalPoint f) = 0 := by
    rw [hBQ f f, hf]
    norm_num
  have href : (associated Q) (rationalPoint e) (rationalPoint f) = 1 := by
    rw [hBQ e f, hef]
    norm_num
  have hfe : (associated Q) (rationalPoint f) (rationalPoint e) = 1 := by
    rw [associated_comm, href]
  have hb : b = 0 := by
    have h := hze
    simp only [map_add, map_smul, smul_eq_mul, hre, href, mul_one, mul_zero, zero_add] at h
    exact h
  have ha : a = 0 := by
    have h := hzf
    simp only [map_add, map_smul, smul_eq_mul, hfe, hrf, mul_one, mul_zero, add_zero] at h
    exact h
  simpa [ha, hb] using hy

end PlaneCarrier

/-! ## The form of a conical fibre -/

section FibreForm

variable {Q : QuadraticForm ℝ (realified V)} {BQ : LinearMap.BilinForm ℚ V} {e f : V}

omit [Module.Finite ℚ V] in
/-- The pairing of the fibre form at rational points of the fibre is the ambient pairing. -/
theorem associated_fibreForm_rationalPoint
    (hBQ : ∀ u w : V, (associated Q) (rationalPoint u) (rationalPoint w) = (BQ u w : ℝ))
    (W : Submodule ℚ V) (u v : ↥W) :
    (associated (fibreForm Q W)) (rationalPoint u) (rationalPoint v)
      = (BQ (u : V) (v : V) : ℝ) := by
  rw [associated_fibreForm, realifyMap_rationalPoint, realifyMap_rationalPoint, hBQ]

/-- **The fibre form is the restriction of the ambient form to the real form of the fibre.** -/
noncomputable def fibreFormIsometry (W : Submodule ℚ V) :
    QuadraticMap.IsometryEquiv (fibreForm Q W) (QuadraticMap.restrict Q (realify W)) where
  toLinearEquiv := LinearEquiv.ofInjective (realifyMap W) (realifyMap_injective W)
  map_app' := by
    intro x
    rw [QuadraticMap.restrict_apply, fibreForm]
    rfl

/-- **The fibre form of a form of signature `(2, n)` has positive index one**: Looijenga §1B,
p. 11 (text line 247), "as this signature remains `(1, n-1)`"; the ambient positive index is
`2` here. -/
theorem sigPos_fibreForm (hBQ : ∀ u w : V,
    (associated Q) (rationalPoint u) (rationalPoint w) = (BQ u w : ℝ))
    (hBsym : BQ.IsSymm) (he : BQ e e = 0) (hf : BQ f f = 0) (hef : BQ e f = 1) :
    sigPos (fibreForm Q (planeComplement BQ e f)) + 1 = sigPos Q := by
  have hre : Q (rationalPoint e) = 0 := by
    rw [← associated_self_apply, hBQ e e, he]
    norm_num
  have hrf : Q (rationalPoint f) = 0 := by
    rw [← associated_self_apply, hBQ f f, hf]
    norm_num
  have href : (associated Q) (rationalPoint e) (rationalPoint f) = 1 := by
    rw [hBQ, hef]
    norm_num
  have h := sigPos_restrict_planePerp Q hre hrf href
  rw [← realify_planeComplement_eq_planePerp hBQ hBsym he hf hef] at h
  rw [(QuadraticMap.Equivalent.sigPos_eq
    ⟨fibreFormIsometry (Q := Q) (planeComplement BQ e f)⟩).symm] at h
  exact h

/-- **The fibre form of a nondegenerate form is nondegenerate.** -/
theorem fibreForm_nondegenerate (hBQ : ∀ u w : V,
    (associated Q) (rationalPoint u) (rationalPoint w) = (BQ u w : ℝ))
    (hBsym : BQ.IsSymm) (he : BQ e e = 0) (hf : BQ f f = 0) (hef : BQ e f = 1)
    (hnd : Q.Nondegenerate) : (fibreForm Q (planeComplement BQ e f)).Nondegenerate := by
  rw [QuadraticMap.nondegenerate_iff_radical_eq_bot, QuadraticMap.radical_eq_ker_associated,
    Submodule.eq_bot_iff]
  intro x hx
  rw [LinearMap.mem_ker] at hx
  have hBnd : (associated Q).Nondegenerate :=
    QuadraticMap.nondegenerate_associated_iff.2 hnd
  have hsep : (associated Q).SeparatingLeft := hBnd.1
  have hzero : realifyMap (planeComplement BQ e f) x = 0 := by
    refine hsep _ fun z => ?_
    have hsup := realify_planeComplement_sup hBsym he hf hef
    have hz : z ∈ realify (planeComplement BQ e f) ⊔
        Submodule.span ℝ ({rationalPoint e, rationalPoint f} : Set (realified V)) := by
      rw [hsup]
      exact Submodule.mem_top
    obtain ⟨w, hw, u, hu, rfl⟩ := Submodule.mem_sup.1 hz
    obtain ⟨w₀, rfl⟩ := hw
    obtain ⟨c, d, rfl⟩ := Submodule.mem_span_pair.1 hu
    have hww : (associated Q) (realifyMap (planeComplement BQ e f) x)
        (realifyMap (planeComplement BQ e f) w₀) = 0 := by
      rw [← associated_fibreForm]
      exact congrArg (fun g => g w₀) hx
    have hwe : (associated Q) (realifyMap (planeComplement BQ e f) x)
        (rationalPoint e) = 0 := by
      have hmem : realifyMap (planeComplement BQ e f) x ∈ realify (planeComplement BQ e f) :=
        ⟨x, rfl⟩
      have := (mem_planePerp_iff.1 (realify_planeComplement_le_planePerp hBQ hmem)).1
      rw [associated_comm, this]
    have hwf : (associated Q) (realifyMap (planeComplement BQ e f) x)
        (rationalPoint f) = 0 := by
      have hmem : realifyMap (planeComplement BQ e f) x ∈ realify (planeComplement BQ e f) :=
        ⟨x, rfl⟩
      have := (mem_planePerp_iff.1 (realify_planeComplement_le_planePerp hBQ hmem)).2
      rw [associated_comm, this]
    have hsplit : (associated Q) (realifyMap (planeComplement BQ e f) x)
        (realifyMap (planeComplement BQ e f) w₀ +
          (c • rationalPoint e + d • rationalPoint f))
        = (associated Q) (realifyMap (planeComplement BQ e f) x)
            (realifyMap (planeComplement BQ e f) w₀)
          + c * ((associated Q) (realifyMap (planeComplement BQ e f) x) (rationalPoint e))
          + d * ((associated Q) (realifyMap (planeComplement BQ e f) x) (rationalPoint f)) := by
      rw [map_add, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
      ring
    rw [hsplit, hww, hwe, hwf]
    ring
  have hinj := realifyMap_injective (planeComplement BQ e f)
  exact hinj (by rw [hzero, map_zero])

end FibreForm

omit [Module.Finite ℚ V] in
/-- The rational points of `V` do not collapse: `v ↦ 1 ⊗ v` is injective, `ℝ` being flat
over `ℚ`. -/
theorem rationalPoint_ne_zero {v : V} (hv : v ≠ 0) : rationalPoint v ≠ 0 := by
  intro h0
  have _ : Module.Flat ℚ ℝ := inferInstance
  have hf : Function.Injective ⇑(LinearMap.toSpanSingleton ℚ V v) := by
    rw [injective_iff_map_eq_zero]
    intro c hc
    have hcv : c • v = 0 := hc
    rcases smul_eq_zero.1 hcv with h | h
    · exact h
    · exact absurd h hv
  have hone : (LinearMap.toSpanSingleton ℚ V v) 1 = v := LinearMap.toSpanSingleton_apply_one ..
  have hε : LinearMap.lTensor ℝ (LinearMap.toSpanSingleton ℚ V v)
      ((1 : ℝ) ⊗ₜ[ℚ] (1 : ℚ)) = 0 := by
    rw [LinearMap.lTensor_tmul, hone]
    exact h0
  have hzero : ((1 : ℝ) ⊗ₜ[ℚ] (1 : ℚ)) = 0 :=
    (Module.Flat.lTensor_preserves_injective_linearMap (M := ℝ) _ hf) (by rw [hε, map_zero])
  have hcontra := congrArg (TensorProduct.rid ℚ ℝ) hzero
  simp only [TensorProduct.rid_tmul, map_zero, one_smul] at hcontra
  exact one_ne_zero hcontra

/-! ## The ray of a plane inside the fibre of one of its lines -/

section FibreRay

variable {Q : QuadraticForm ℝ (realified V)} {BQ : LinearMap.BilinForm ℚ V}

omit [Module.Finite ℚ V] in
/-- The generator of a line inside an isotropic plane lies in the plane. -/
theorem ConicalLine.gen_mem_plane (F : ConicalLine BQ Q) (G : ConicalPlane BQ)
    (h : F.line ≤ G.plane) : F.gen ∈ G.plane := by
  refine h ?_
  rw [F.line_eq]
  exact Submodule.subset_span (Set.mem_singleton F.gen)

omit [Module.Finite ℚ V] in
/-- **The class of a plane's ray in the fibre of one of its lines**: Looijenga §1B, p. 11 (text
line 265), "`Λ²J` can be regarded as a line in `I ⊗ I^⊥/I`". The representative in the carrier
`planeComplement` of the fibre is `ray - (ray · f) e`: the adjustment is along the hyperbolic
partner `f` only, because `ray · e = 0` (both lie in the totally isotropic plane). -/
theorem fibreRay_val (hBsym : BQ.IsSymm) (F : ConicalLine BQ Q) (G : ConicalPlane BQ)
    (h : F.line ≤ G.plane) :
    ((fibreRay hBsym F G : ↥F.space) : V) = G.ray - BQ G.ray F.partner • F.gen := by
  have hge : BQ G.ray F.gen = 0 := G.isotropic G.ray G.ray_mem F.gen (F.gen_mem_plane G h)
  simp [fibreRay, fibreProj, hge]

omit [Module.Finite ℚ V] in
/-- **The ray of a plane is isotropic in the fibre**: `J/I` is totally isotropic in `I^⊥/I`, so the
half line `C_{J,+}` is an isotropic half line of the fibre's cone — the case of Lemma-Definition
4.5, p. 19, that the source distinguishes. -/
theorem fibreRay_isotropic (hBQ : ∀ u w : V,
    (associated Q) (rationalPoint u) (rationalPoint w) = (BQ u w : ℝ))
    (hBsym : BQ.IsSymm) (F : ConicalLine BQ Q) (G : ConicalPlane BQ) (h : F.line ≤ G.plane) :
    (fibreForm Q F.space) (rationalPoint (fibreRay hBsym F G)) = 0 := by
  rw [fibreForm_rationalPoint hBQ]
  have hge : BQ G.ray F.gen = 0 := G.isotropic G.ray G.ray_mem F.gen (F.gen_mem_plane G h)
  have hsym : BQ F.gen G.ray = 0 := by rw [hBsym.eq]; exact hge
  have hb : BQ ((fibreRay hBsym F G : ↥F.space) : V) ((fibreRay hBsym F G : ↥F.space) : V)
      = 0 := by
    rw [fibreRay_val hBsym F G h]
    set a : ℚ := BQ G.ray F.partner with ha
    have step1 : BQ (G.ray - a • F.gen) (G.ray - a • F.gen)
        = BQ G.ray (G.ray - a • F.gen) - a * BQ F.gen (G.ray - a • F.gen) := by
      rw [LinearMap.BilinForm.sub_left, LinearMap.BilinForm.smul_left]
    have step2 : BQ G.ray (G.ray - a • F.gen) = BQ G.ray G.ray - a * BQ G.ray F.gen := by
      rw [map_sub, map_smul, smul_eq_mul]
    have step3 : BQ F.gen (G.ray - a • F.gen) = BQ F.gen G.ray - a * BQ F.gen F.gen := by
      rw [map_sub, map_smul, smul_eq_mul]
    rw [step1, step2, step3, G.ray_iso, hge, hsym, F.gen_iso]
    ring
  rw [hb]
  norm_num

omit [Module.Finite ℚ V] in
/-- The ray of a plane is not zero in the fibre: `ray ∉ I` (the plane's ray is not a multiple of the
line's generator, `ConicalPlane.ray_not_mem_of_line`), and the representative differs from `ray`
by a multiple of `e`. -/
theorem fibreRay_ne_zero (hBsym : BQ.IsSymm) (F : ConicalLine BQ Q) (G : ConicalPlane BQ)
    (h : F.line ≤ G.plane) : fibreRay hBsym F G ≠ 0 := by
  intro h0
  have hval := fibreRay_val hBsym F G h
  rw [h0] at hval
  simp only [ZeroMemClass.coe_zero] at hval
  have hray : G.ray = BQ G.ray F.partner • F.gen := sub_eq_zero.1 hval.symm
  have hmem : G.ray ∈ F.line := by
    rw [F.line_eq, hray]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton F.gen))
  exact G.ray_not_mem_of_line F.line h F.one_dim hmem

end FibreRay

/-! ## The cone of a fibre, and its closed sheet -/

section FibreCone

variable {Q : QuadraticForm ℝ (realified V)} {BQ : LinearMap.BilinForm ℚ V}

omit [Module.Finite ℚ V] in
/-- The rational closure of a cone depends only on its closure (Definition 4.2, p. 17: `C₊` is the
convex hull of the rational points of the closure of `C`). -/
theorem rationalClosure_congr {C D : PointedCone ℝ (realified V)}
    (h : (C.closure : Set (realified V)) = (D.closure : Set (realified V))) :
    rationalClosure C = rationalClosure D := by
  have hb : rationalBoundary C = rationalBoundary D := by
    simp only [rationalBoundary, h]
  rw [rationalClosure_eq_hull, rationalClosure_eq_hull, hb]

/-- **The rational closure `C_{I,+}` of a fibre cone is the rational closure of the closed sheet.**
The cone `C_I` of a conical fibre is a component of the positive cone of the fibre form (§1B,
p. 11), so the closure of `C_{I,+} = rationalClosure C_I` is the closed sheet, and
`rationalClosure` depends on the cone only through its closure (`rationalClosure_congr`). -/
theorem ConicalLine.closure_eq_closedSheet (F : ConicalLine BQ Q)
    (hpos : sigPos (fibreForm Q F.space) = 1) :
    F.closure = rationalClosure (closedSheet (fibreForm Q F.space) hpos F.sheet_pos) := by
  refine rationalClosure_congr ?_
  rw [show (closedSheet (fibreForm Q F.space) hpos F.sheet_pos).closure
      = closedSheet (fibreForm Q F.space) hpos F.sheet_pos from
    (isClosed_closedSheet_of_moduleTopology _ hpos F.sheet_pos).submodule_topologicalClosure_eq]
  have hle : F.cone ≤ closedSheet (fibreForm Q F.space) hpos F.sheet_pos := by
    refine Submodule.span_le.2 ?_
    intro x hx
    exact subset_closedSheet hpos F.sheet_pos hx
  refine Set.Subset.antisymm ?_ ?_
  · intro x hx
    exact closure_minimal hle (isClosed_closedSheet_of_moduleTopology _ hpos F.sheet_pos) hx
  · intro x hx
    rw [closedSheet_eq_closure_upper (Q := fibreForm Q F.space) hpos F.sheet_pos] at hx
    exact closure_mono (fun y hy => subset_hull hy) hx

end FibreCone

/-! ## Definition 6.1, case (ii): the support space of a plane's half line -/

section SupportSpace

variable {Q : QuadraticForm ℝ (realified V)} {BQ : LinearMap.BilinForm ℚ V}

omit [Module.Finite ℚ V] in
/-- **A form of the ambient space vanishes on the whole fibre when it vanishes on the rational
points of the fibre.** The fibre's rational points span it over `ℝ`. -/
theorem associated_rationalPoint_eq_zero_of_forall {W : Submodule ℚ V} {w : V}
    (hBQ : ∀ u v : V, (associated Q) (rationalPoint u) (rationalPoint v) = (BQ u v : ℝ))
    (h : ∀ y : ↥W, BQ w (y : V) = 0) (x : realified ↥W) :
    (associated Q) (rationalPoint w) (realifyMap W x) = 0 := by
  have hspan := span_range_rationalPoint (V := ↥W)
  have hmem : x ∈ Submodule.span ℝ (Set.range (rationalPoint (V := ↥W))) := by
    rw [hspan]
    trivial
  have hker : Submodule.span ℝ (Set.range (rationalPoint (V := ↥W))) ≤
      LinearMap.ker (((associated Q) (rationalPoint w)).comp (realifyMap W)) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨y, rfl⟩
    simp only [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.comp_apply,
      realifyMap_rationalPoint, hBQ]
    rw [h y]
    norm_num
  exact hker hmem

/-- **Looijenga, Definition 6.1, p. 28, case (ii), for the Baily–Borel decomposition**: the
`Σ`-support space of the half line `C_{J,+}` in the fibre of a `ℚ`-isotropic line `I ≤ J`,
relative to the facial decomposition `Σ(bb) = facialDecomposition F.closure`, is `J^⊥` — the
orthogonal
complement of the `ℚ`-isotropic plane `J`, written as the common zero set of the two forms of a
spanning pair `e`, `ray` of `J`.

The computation is in three parts. The fibre's `Σ`-support space of the ray is `(J/I)^⊥ ⊂ I^⊥/I`
(`sigmaSupportSpace_facialDecomposition_hull_eq_ker` at the fibre form, §1B's signature `(1, n-1)`).
The image of `(J/I)^⊥` in `V`, together with the line `I`, is `J^⊥`: every vector of it pairs to
zero with `e` and with `ray`, and conversely a vector of `J^⊥` differs from a vector of `(J/I)^⊥`
only by a multiple of `e`, which lies in `J`. -/
theorem vSigmaPlane_eq_ker_inf_ker (hBQ : ∀ u w : V,
    (associated Q) (rationalPoint u) (rationalPoint w) = (BQ u w : ℝ))
    (hBsym : BQ.IsSymm) (F : ConicalLine BQ Q) (G : ConicalPlane BQ) (h : F.line ≤ G.plane)
    (hpos : sigPos (fibreForm Q F.space) = 1)
    (hnd : (fibreForm Q F.space).Nondegenerate)
    (hsheet : 0 ≤ (associated (fibreForm Q F.space)) (rationalPoint (fibreRay hBsym F G)) F.sheet) :
    vSigmaPlane hBsym F (facialDecomposition F.closure) G h =
      LinearMap.ker (associated Q (rationalPoint F.gen)) ⊓
        LinearMap.ker (associated Q (rationalPoint G.ray)) := by
  have hQr : (fibreForm Q F.space) (rationalPoint (fibreRay hBsym F G)) = 0 :=
    fibreRay_isotropic hBQ hBsym F G h
  have hrne : rationalPoint (fibreRay hBsym F G) ≠ 0 :=
    rationalPoint_ne_zero (fibreRay_ne_zero hBsym F G h)
  have hsheetC : rationalPoint (fibreRay hBsym F G) ∈
      rationalClosure (closedSheet (fibreForm Q F.space) hpos F.sheet_pos) :=
    mem_rationalClosure.2 (subset_convexHull ℝ _ ⟨⟨_, Set.mem_univ _, rfl⟩,
      subset_closure ((mem_closedSheet hpos F.sheet_pos).2
        ⟨le_of_eq hQr.symm, hsheet⟩)⟩)
  have hsig : sigmaSupportSpace (positiveCone.upper (fibreForm Q F.space) F.sheet)
      (facialDecomposition F.closure) (PointedCone.hull ℝ {rationalPoint (fibreRay hBsym F G)})
      = LinearMap.ker (associated (fibreForm Q F.space) (rationalPoint (fibreRay hBsym F G))) := by
    rw [ConicalLine.closure_eq_closedSheet F hpos]
    exact sigmaSupportSpace_facialDecomposition_hull_eq_ker (t := F.sheet) hpos hnd hQr hrne
      hsheetC hsheet
  rw [vSigmaPlane, hsig]
  have hge : BQ G.ray F.gen = 0 := G.isotropic G.ray G.ray_mem F.gen (F.gen_mem_plane G h)
  have hgene : (associated Q) (rationalPoint G.ray) (rationalPoint F.gen) = 0 := by
    rw [hBQ, hge]
    norm_num
  have hgen : (associated Q) (rationalPoint F.gen) (rationalPoint F.gen) = 0 := by
    rw [hBQ, F.gen_iso]
    norm_num
  have hfgen : (associated Q) (rationalPoint F.gen) (rationalPoint F.partner) = 1 := by
    rw [hBQ, F.pairing]
    norm_num
  have hfgen' : (associated Q) (rationalPoint F.partner) (rationalPoint F.gen) = 1 := by
    rw [associated_comm, hfgen]
  refine le_antisymm ?_ ?_
  · refine sup_le ?_ ?_
    · rw [lineSpan, Submodule.span_le]
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      subst hx
      exact Submodule.mem_inf.2 ⟨by rw [LinearMap.mem_ker]; exact hgen,
        by rw [LinearMap.mem_ker]; exact hgene⟩
    · intro x hx
      obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.1 hx
      rw [LinearMap.mem_ker] at hy
      have hAM : (associated Q) (rationalPoint F.gen) (realifyMap F.space y) = 0 :=
        (mem_planePerp_iff.1 (realify_planeComplement_le_planePerp hBQ ⟨y, rfl⟩)).1
      have h1 : (associated Q) (rationalPoint ((fibreRay hBsym F G : ↥F.space) : V))
          (realifyMap F.space y) = 0 := by
        rw [← realifyMap_rationalPoint, ← associated_fibreForm]
        exact hy
      have hsplit : (associated Q) (rationalPoint ((fibreRay hBsym F G : ↥F.space) : V))
          (realifyMap F.space y)
          = (associated Q) (rationalPoint G.ray) (realifyMap F.space y)
            - (BQ G.ray F.partner : ℝ) *
              ((associated Q) (rationalPoint F.gen) (realifyMap F.space y)) := by
        have hrat : rationalPoint ((fibreRay hBsym F G : ↥F.space) : V)
            = rationalPoint G.ray - (BQ G.ray F.partner : ℝ) • rationalPoint F.gen := by
          rw [fibreRay_val hBsym F G h, map_sub]
          congr 1
          exact rationalPoint_rat_smul (BQ G.ray F.partner) F.gen
        rw [hrat, LinearMap.BilinForm.sub_left, LinearMap.BilinForm.smul_left]
      rw [hsplit, hAM, mul_zero, sub_zero] at h1
      exact Submodule.mem_inf.2 ⟨by rw [LinearMap.mem_ker]; exact hAM,
        by rw [LinearMap.mem_ker]; exact h1⟩
  · intro z hz
    obtain ⟨hz1, hz2⟩ := Submodule.mem_inf.1 hz
    rw [LinearMap.mem_ker] at hz1 hz2
    set lam : ℝ := (associated Q) (rationalPoint F.partner) z with hlam
    have hyW : z - lam • rationalPoint F.gen ∈ planePerp Q (rationalPoint F.gen)
        (rationalPoint F.partner) := by
      rw [mem_planePerp_iff]
      refine ⟨?_, ?_⟩
      · have hexp : (associated Q) (rationalPoint F.gen) (z - lam • rationalPoint F.gen)
            = (associated Q) (rationalPoint F.gen) z
              - lam * ((associated Q) (rationalPoint F.gen) (rationalPoint F.gen)) := by
          rw [map_sub, map_smul, smul_eq_mul]
        rw [hexp, hz1, hgen, mul_zero, sub_zero]
      · have hexp : (associated Q) (rationalPoint F.partner) (z - lam • rationalPoint F.gen)
            = (associated Q) (rationalPoint F.partner) z
              - lam * ((associated Q) (rationalPoint F.partner) (rationalPoint F.gen)) := by
          rw [map_sub, map_smul, smul_eq_mul]
        rw [hexp, hlam, hfgen']
        ring
    have hyMem : z - lam • rationalPoint F.gen ∈ realify F.space := by
      change z - lam • rationalPoint F.gen ∈ realify (planeComplement BQ F.gen F.partner)
      rw [realify_planeComplement_eq_planePerp hBQ hBsym F.gen_iso F.partner_iso F.pairing]
      exact hyW
    obtain ⟨y, hy⟩ := hyMem
    have hyker : (associated (fibreForm Q F.space)) (rationalPoint (fibreRay hBsym F G)) y = 0 := by
      have hrat : rationalPoint ((fibreRay hBsym F G : ↥F.space) : V)
          = rationalPoint G.ray - (BQ G.ray F.partner : ℝ) • rationalPoint F.gen := by
        rw [fibreRay_val hBsym F G h, map_sub]
        congr 1
        exact rationalPoint_rat_smul (BQ G.ray F.partner) F.gen
      have hconf : realifyMap F.space y = z - lam • rationalPoint F.gen := hy
      rw [associated_fibreForm, realifyMap_rationalPoint, hrat, hconf]
      have hexp : (associated Q)
          (rationalPoint G.ray - (BQ G.ray F.partner : ℝ) • rationalPoint F.gen)
          (z - lam • rationalPoint F.gen)
          = ((associated Q) (rationalPoint G.ray) z
              - lam * ((associated Q) (rationalPoint G.ray) (rationalPoint F.gen)))
            - (BQ G.ray F.partner : ℝ) * ((associated Q) (rationalPoint F.gen) z
              - lam * ((associated Q) (rationalPoint F.gen) (rationalPoint F.gen))) := by
        rw [LinearMap.BilinForm.sub_left, LinearMap.BilinForm.smul_left, map_sub, map_sub,
          map_smul, map_smul, smul_eq_mul, smul_eq_mul]
      rw [hexp, hz1, hz2, hgene, hgen]
      ring
    have hz_eq : z = realifyMap F.space y + lam • rationalPoint F.gen := by
      rw [hy]
      abel
    rw [hz_eq]
    refine Submodule.add_mem _ ?_ ?_
    · refine Submodule.mem_sup_right ?_
      exact Submodule.mem_map.2 ⟨y, by rw [LinearMap.mem_ker]; exact hyker, rfl⟩
    · refine Submodule.mem_sup_left ?_
      exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton _))

end SupportSpace

/-! ## The two isotropic lines of a plane span it -/

section PlaneSpan

variable {Q : QuadraticForm ℝ (realified V)} {BQ : LinearMap.BilinForm ℚ V}

/-- **A `ℚ`-isotropic plane is spanned by one of its isotropic lines and its ray.** Both lie in the
two-dimensional plane, and the ray is not on any isotropic line of the plane
(`ConicalPlane.ray_not_mem_of_line`), so they are independent. -/
theorem span_gen_ray_eq_plane (F : ConicalLine BQ Q) (G : ConicalPlane BQ)
    (h : F.line ≤ G.plane) :
    Submodule.span ℚ ({F.gen, G.ray} : Set V) = G.plane := by
  have hle : Submodule.span ℚ ({F.gen, G.ray} : Set V) ≤ G.plane := by
    refine Submodule.span_le.2 ?_
    intro x hx
    rcases Set.mem_insert_iff.1 hx with rfl | hx
    · exact F.gen_mem_plane G h
    · rw [Set.mem_singleton_iff] at hx
      subst hx
      exact G.ray_mem
  have hray : G.ray ∉ Submodule.span ℚ ({F.gen} : Set V) := by
    rw [show Submodule.span ℚ ({F.gen} : Set V) = F.line from F.line_eq.symm]
    exact G.ray_not_mem_of_line F.line h F.one_dim
  have hunion : Submodule.span ℚ ({F.gen, G.ray} : Set V)
      = Submodule.span ℚ ({F.gen} : Set V) ⊔ Submodule.span ℚ ({G.ray} : Set V) := by
    rw [← Submodule.span_union]
    rfl
  have hfin : Module.finrank ℚ ↥(Submodule.span ℚ ({F.gen, G.ray} : Set V)) = 2 := by
    have hgen1 : Module.finrank ℚ ↥(Submodule.span ℚ ({F.gen} : Set V)) = 1 :=
      finrank_span_singleton F.gen_ne
    have hray1 : Module.finrank ℚ ↥(Submodule.span ℚ ({G.ray} : Set V)) = 1 :=
      finrank_span_singleton G.ray_ne
    have hinf : Module.finrank ℚ ↥(Submodule.span ℚ ({F.gen} : Set V) ⊓
        Submodule.span ℚ ({G.ray} : Set V)) = 0 := by
      have hbot : Submodule.span ℚ ({F.gen} : Set V) ⊓ Submodule.span ℚ ({G.ray} : Set V)
          = ⊥ := by
        refine (Submodule.eq_bot_iff _).2 ?_
        rintro x hx
        obtain ⟨hx1, hx2⟩ := Submodule.mem_inf.1 hx
        obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 hx1
        obtain ⟨d, hd⟩ := Submodule.mem_span_singleton.1 hx2
        by_contra hx0
        have hc0 : c ≠ 0 := by
          intro h0
          apply hx0
          calc x = c • F.gen := hc.symm
            _ = (0 : ℚ) • F.gen := by rw [h0]
            _ = 0 := zero_smul ℚ F.gen
        have hd0 : d ≠ 0 := by
          intro h0
          apply hc0
          have hzero : c • F.gen = 0 := by
            calc c • F.gen = x := hc
              _ = d • G.ray := hd.symm
              _ = (0 : ℚ) • G.ray := by rw [h0]
              _ = 0 := zero_smul ℚ G.ray
          rcases smul_eq_zero.1 hzero with h' | h'
          · exact h'
          · exact absurd h' F.gen_ne
        refine hray ?_
        rw [Submodule.mem_span_singleton]
        refine ⟨d⁻¹ * c, ?_⟩
        have hkey : c • F.gen = d • G.ray := hc.trans hd.symm
        calc (d⁻¹ * c) • F.gen = d⁻¹ • (c • F.gen) := mul_smul d⁻¹ c F.gen
          _ = d⁻¹ • (d • G.ray) := congrArg (fun t => d⁻¹ • t) hkey
          _ = G.ray := inv_smul_smul₀ hd0 G.ray
      rw [hbot]
      simp
    have hsup := Submodule.finrank_sup_add_finrank_inf_eq
      (Submodule.span ℚ ({F.gen} : Set V)) (Submodule.span ℚ ({G.ray} : Set V))
    rw [hgen1, hray1, hinf] at hsup
    rw [hunion]
    omega
  exact Submodule.eq_of_le_of_finrank_eq hle (by rw [hfin, G.two_dim])

/-- **The orthogonal complement of a plane is the common kernel of the forms of a spanning pair**:
with `span_gen_ray_eq_plane`, the intersection of the two kernels is the intersection over the whole
plane, so it does not depend on which isotropic line of the plane it is computed from. -/
theorem ker_inf_ker_eq (F : ConicalLine BQ Q) (G : ConicalPlane BQ) (h : F.line ≤ G.plane) :
    LinearMap.ker (associated Q (rationalPoint F.gen)) ⊓
        LinearMap.ker (associated Q (rationalPoint G.ray))
      = ⨅ (a : ↥G.plane), LinearMap.ker (associated Q (rationalPoint (a : V))) := by
  refine le_antisymm ?_ ?_
  · intro z hz
    obtain ⟨hz1, hz2⟩ := Submodule.mem_inf.1 hz
    rw [LinearMap.mem_ker] at hz1 hz2
    rw [Submodule.mem_iInf]
    intro a
    rw [LinearMap.mem_ker]
    have ha : (a : V) ∈ Submodule.span ℚ ({F.gen, G.ray} : Set V) := by
      rw [span_gen_ray_eq_plane F G h]
      exact a.2
    obtain ⟨c, d, hcd⟩ := Submodule.mem_span_pair.1 ha
    rw [← hcd, map_add, rationalPoint_rat_smul, rationalPoint_rat_smul,
      LinearMap.BilinForm.add_left, LinearMap.BilinForm.smul_left,
      LinearMap.BilinForm.smul_left, hz1, hz2]
    ring
  · intro z hz
    rw [Submodule.mem_iInf] at hz
    exact Submodule.mem_inf.2
      ⟨by rw [LinearMap.mem_ker]; exact hz ⟨F.gen, F.gen_mem_plane G h⟩,
       by rw [LinearMap.mem_ker]; exact hz ⟨G.ray, G.ray_mem⟩⟩

end PlaneSpan

/-! ## Example 6.2: the Baily–Borel decomposition -/

section BailyBorel

variable {Q : QuadraticForm ℝ (realified V)} {BQ : LinearMap.BilinForm ℚ V}

/-- **Looijenga, Example 6.2, p. 29 (text line 783), condition (i) of Definition 6.1**: for every
`ℚ`-isotropic line, the faces of the cone `C_{I,+}` of its fibre define a locally rational
decomposition of `C_{I,+}` (Definition 4.2, p. 17) — in fact the coarsest one, which is what the
source calls the Baily–Borel decomposition. -/
theorem bailyBorel_condition_i (F : ConicalLine BQ Q)
    (hpos : sigPos (fibreForm Q F.space) = 1)
    (hnd : (fibreForm Q F.space).Nondegenerate) :
    IsLocallyRationalDecomposition F.closure (facialDecomposition F.closure) := by
  refine facialDecomposition_isLocallyRational F.closure ?_
  refine (closedSheet_salient hpos hnd F.sheet_pos).anti ?_
  rw [ConicalLine.closure_eq_closedSheet F hpos]
  exact rationalClosure_le_closedSheet hpos

/-- **Looijenga, Example 6.2, p. 29, condition (ii) of Definition 6.1**: the `Σ`-support space of
the half line `C_{J,+}` of a `ℚ`-isotropic plane `J` in the fibre of any of its `ℚ`-isotropic lines
is `J^⊥` (`vSigmaPlane_eq_ker_inf_ker`), so it is independent of the line. -/
theorem bailyBorel_condition_ii (hBQ : ∀ u w : V,
    (associated Q) (rationalPoint u) (rationalPoint w) = (BQ u w : ℝ))
    (hpos : ∀ F : ConicalLine BQ Q, sigPos (fibreForm Q F.space) = 1)
    (hnd : ∀ F : ConicalLine BQ Q, (fibreForm Q F.space).Nondegenerate)
    (hsheet : ∀ (hBsym : BQ.IsSymm) (F : ConicalLine BQ Q) (G : ConicalPlane BQ)
      (_h : F.line ≤ G.plane),
      0 ≤ (associated (fibreForm Q F.space)) (rationalPoint (fibreRay hBsym F G)) F.sheet)
    (hBsym : BQ.IsSymm) (F F' : ConicalLine BQ Q) (G : ConicalPlane BQ)
    (h : F.line ≤ G.plane) (h' : F'.line ≤ G.plane) :
    vSigmaPlane hBsym F (facialDecomposition F.closure) G h =
      vSigmaPlane hBsym F' (facialDecomposition F'.closure) G h' := by
  rw [vSigmaPlane_eq_ker_inf_ker hBQ hBsym F G h (hpos F) (hnd F) (hsheet hBsym F G h),
    vSigmaPlane_eq_ker_inf_ker hBQ hBsym F' G h' (hpos F') (hnd F') (hsheet hBsym F' G h'),
    ker_inf_ker_eq F G h, ker_inf_ker_eq F' G h']

end BailyBorel

/-! ## Lemma 6.6: a refinement does not grow the support spaces -/

section Lemma66

variable {Q : QuadraticForm ℝ (realified V)} {BQ : LinearMap.BilinForm ℚ V}

omit [Module.Finite ℚ V] in
/-- **Looijenga, Lemma 6.6, p. 30 (text line 821)**, for the support spaces of one fibre: if `S`
refines `S'` — every member of `S'` above `σ` that meets the open cone dominates a member of `S`
above `σ` that meets it — then the `Σ`-support space of `σ` does not grow: `L_σ^S ⊆ L_σ^{S'}`. -/
theorem sigmaSupportSpace_le_of_refines {C : Set (realified V)}
    {S S' : Set (PointedCone ℝ (realified V))} {σ : PointedCone ℝ (realified V)}
    (_hidx : supportIndex C S σ)
    (h : ∀ τ' : supportIndex C S' σ, ∃ τ ∈ S, σ ≤ τ ∧ τ ≤ τ'.1 ∧
      ((τ : Set (realified V)) ∩ C).Nonempty) :
    sigmaSupportSpace C S σ ≤ sigmaSupportSpace C S' σ := by
  refine le_iInf fun τ' => ?_
  obtain ⟨τ, hτ, hστ, hττ', hτC⟩ := h τ'
  exact (iInf_le (fun τ : supportIndex C S σ => supportSpace τ.1 σ) ⟨τ, hτ, hστ, hτC⟩).trans
    (supportSpace_mono hττ')

omit [Module.Finite ℚ V] in
/-- **Looijenga, Lemma 6.6, p. 30: the inclusion `V_σ ⊆ V_{σ'}`** of the `Σ`-support spaces of
Definition 6.1, for the members of two decompositions of the fibre of a line `I`, the second
refining the first, and the half line `C_{J,+}` of a `ℚ`-isotropic plane `J ⊇ I` as the member
`σ`. -/
theorem vSigmaPlane_le_of_refines (hBsym : BQ.IsSymm) (F : ConicalLine BQ Q)
    (G : ConicalPlane BQ) (hFG : F.line ≤ G.plane)
    {S S' : Set (PointedCone ℝ (realified ↥F.space))}
    (hidx : supportIndex (positiveCone.upper (fibreForm Q F.space) F.sheet) S
      (PointedCone.hull ℝ {rationalPoint (fibreRay hBsym F G)}))
    (h : ∀ τ' : supportIndex (positiveCone.upper (fibreForm Q F.space) F.sheet) S'
      (PointedCone.hull ℝ {rationalPoint (fibreRay hBsym F G)}),
      ∃ τ ∈ S, PointedCone.hull ℝ {rationalPoint (fibreRay hBsym F G)} ≤ τ ∧ τ ≤ τ'.1 ∧
        ((τ : Set (realified ↥F.space)) ∩
          (positiveCone.upper (fibreForm Q F.space) F.sheet : Set (realified ↥F.space))).Nonempty) :
    vSigmaPlane hBsym F S G hFG ≤ vSigmaPlane hBsym F S' G hFG := by
  refine sup_le_sup_left ?_ _
  exact Submodule.map_mono (sigmaSupportSpace_le_of_refines hidx h)

end Lemma66

end LeanCategories.Lattices.Valued
