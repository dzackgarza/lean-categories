/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Lattices.Valued.LocallyRationalDecomposition
public import LeanCategories.Lattices.Valued.IsotropicQuotientSignature
public import LeanCategories.Lattices.Valued.PositiveCone
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.Flat.Basic

/-!
# The conical locus of a type IV domain

The conical locus of a type IV domain (E. Looijenga, *Compactifications defined by arrangements
II: locally symmetric varieties of type IV*, arXiv math/0201218v2 (2002),
`looijenga-math0201218v2.md`):
its fibres at the `ℚ`-isotropic lines, and the reduction data `I^⊥/I` that the admissible
decompositions of §6 live on.

## What is stated

* Definition 2.1, p. 10 (text line 279): the conical locus, as the union of the cones `C_I` over the
  `ℚ`-isotropic subspaces `I` of `V`, with `I` a line or a plane. A cone is carried by the fibre
  `ConicalLine`: the reduction `I^⊥/I` of §1B, p. 11 (text line 251), realised as the orthogonal
  complement `planeComplement` of the hyperbolic plane `⟨e, f⟩` inside `V` (so that every fibre is a
  `ℚ`-subspace of `V`, and the support spaces of §6 — subspaces of `V` — are subspaces of one
  ambient space); its open cone `C_I` is `ConicalLine.cone`, and its rational closure `C_{I,+}`
  (Definition 4.2, p. 17) is `ConicalLine.closure`. The half-line `C_J` of a `ℚ`-isotropic plane is
  carried by `ConicalPlane`, and its class in the fibre of a line `I ⊆ J` is `fibreRay` (§1B: `Λ²J`
  is a line in `I ⊗ I^⊥/I`).
* **the oriented plane, §1A p. 10 and Example 6.3 p. 29**: `ConicalPlane` carries the plane together
  with the *positive rational generator* `r_J ∈ ⋀²J(ℚ)` of the distinguished component `C_J` of
  `⋀²J(ℝ) − {0}`, realised as the ordered basis `(dir, dirAlt)` of `J` with `r_J = dir ∧ dirAlt`.
  Its ray in the fibre of a witnessing line `I = ℚ g` is *derived* from `r_J`, not stored:
  `ConicalPlane.rayOf` is the vector `ρ ∈ J` with `g ∧ ρ = r_J`, and `fibreRayProj` is its class in
  `I^⊥/I`. (The carrier at `55966097` stored one vector required to lie outside *every* line of the
  plane, so it had no instance at all: `I = ⟨ray⟩` is a line of the plane containing `ray`. See
  `tests/regression/ConicalPlaneSplit22.lean` for the recorded contradiction and a genuine plane on
  a split space of signature `(2,2)` with two witnessing lines.)
* **the coherence of a plane with the sheet of a fibre, `ConicalPlane.IsPositiveAt`**: the
  sheet of a `ConicalLine` is a choice of cone `C_I` at the fibre, and the orientation of a
  `ConicalPlane` is a choice of generator `r_J ∈ ⋀²J(ℚ)`; the two are independent data. The
  source's `C_J ⊂ ∂C_I` (§1B, p. 11) and "`r_J` can be regarded as an isotropic vector in
  `(C_I)_+`" (Example 6.3, p. 29) say that the class of `r_J` pairs *positively* with the
  sheet, which is `ConicalPlane.IsPositiveAt`. At a presentation satisfying it the fibre half
  line is the class of `r_J` (`fibreRay_eq_fibreRayProj_of_isPositiveAt`) and the plane
  member's carrier in `⋀²V(ℝ)` is the closed ray `{t • r_J | 0 ≤ t}`
  (`ConicalMember.carrier_plane_eq_positiveRay`). Without it the carrier is the *opposite* ray:
  `tests/regression/ConicalPlaneSplit22.lean` computes both for the two sheets of one fibre, and
  `ConicalMember.plane` requires the coherent one.
* **Definition 6.1, p. 28** (text line 769): `IsAdmissibleDecomposition`, with `Γ`-invariance of the
  collection (`IsGammaInvariantLocus`), condition (i) — the members of `Σ` in `C_{I,+}` are a
  locally rational decomposition of it, Definition 4.2 through
  `IsLocallyRationalDecomposition` — and condition (ii) — the `Σ`-support space of `C_{J,+}` is
  independent of the line `I ⊆ J`.
* **the `Σ`-support space `V_σ`** of every member: `vSigma` for the members of a fibre (case (i) of
  the source's definition, the subspace of `I^⊥` containing `I` corresponding to the span of `σ`),
  `vSigmaPlane` for the plane members (case (ii), through Lemma-Definition 4.5's
  `sigmaSupportSpace`, whose `C` is the open cone `C_I` of the fibre and not its closure), and the
  **isotropic center** `I(σ) = V_σ ∩ V_σ^⊥` as `isotropicCenter`.
* **Lemma 6.6, p. 30** (text line 821), the inclusion `V_σ ⊂ V_{σ'}`: `vSigma_mono`.

## What is not here

* **Examples 6.2 and 6.4 are not theorems here**: they are stated in `Semifan`, which instantiates
  §4 at each fibre. That needs `sigPos` of a fibre form to be `1` and the fibre form to be
  nondegenerate — the source's "this signature remains `(1, n-1)`" (§1B, p. 11). The sharp
  statements are `Semifan.sigPos_fibreForm` and `Semifan.fibreForm_nondegenerate`; Example 6.2 is
  `Semifan.bailyBorel_isAdmissibleDecomposition`. For Example 6.4, `Σ(ℋ)` is
  `SemifanArrangement.semifanArrangement` and the `≤` half of `J_{Σ(ℋ)} = J_ℋ` is
  `SemifanArrangement.vSigmaPlane_semifanArrangement_le_JH` — `J^⊥` through both generators of the
  plane, `⟨gen⟩^⊥ ∩ ⟨ray⟩^⊥`, and the traces of the hyperplanes containing the plane; the `≥` half
  is `SemifanArrangement.fibreJH_le_span_of_member`, on the primal side — a member of `Σ(ℋ)` above
  the half line meeting the open cone spans the common kernel of its own walls — and the two
  halves assemble into `SemifanArrangement.vSigmaPlane_semifanArrangement_eq_JH`.
* The `Γ`-invariance in `IsGammaInvariantLocus` is stated at the level of the images of members in
  `V(ℝ)`, and it takes the image *under the isometry*: `γ` carries the fibre of `I` to the fibre of
  `γI` (§1B, p. 11), so the members of the second are the images of the members of the first.
  Comparing the two collections without moving one of them would ask two different subspaces of
  `V(ℝ)` to agree, which no nontrivial isometry of an indefinite form does. The transport itself is
  `Semifan.ConicalLine.map`, and the predicate is discharged for the facial decomposition by
  `Semifan.bailyBorel_gammaInvariant`.

## The carriers of a fibre

`ConicalLine.space` is an `abbrev`, and `ConicalLine.cone` and `ConicalLine.closure` are typed by
the explicit `planeComplement BQ gen partner` rather than by `F.space`. This makes the carrier of a
fibre and the types of its sheet, its cone and its closure *syntactically* the same expression, so
that transporting a fibre along an isometry moves all of them at once (`Semifan.ConicalLine.map`)
and the support spaces of §6 can be compared across two fibres. Naming the carrier only through
`F.space` leaves the unfolded and the folded form definitionally but not syntactically equal, and
the operations of §6 (`fibreForm`, `closedSheet`, `rationalClosure`) do not accept one where they
expect the other.

## References

* E. Looijenga, *Compactifications defined by arrangements II: locally symmetric varieties of type
  IV*, arXiv math/0201218v2 (2002), §1B (p. 11), §2 (Definition 2.1, p. 10), §4 (Definitions 4.1 and
  4.2, Lemma-Definition 4.5), §6 (Definition 6.1, p. 28, and Lemma 6.6, p. 30).
* The reductions of §1B and the support spaces of Lemma-Definition 4.5 are the repository's
  `IsotropicQuotientSignature` (#119) and `LocallyRationalDecomposition` (#159).
-/

@[expose] public section

open PointedCone QuadraticMap

open scoped TensorProduct

namespace LeanCategories.Lattices.Valued

variable {V : Type} [AddCommGroup V] [Module ℚ V] [Module.Finite ℚ V]

/-! ## The real form of a rational subspace -/

/-- The real form `W(ℝ) ⊂ V(ℝ)` of a `ℚ`-subspace `W ≤ V`, as the image of `ℝ ⊗_ℚ W`. -/
noncomputable def realifyMap (W : Submodule ℚ V) :
    (realified ↥W) →ₗ[ℝ] (realified V) :=
  TensorProduct.AlgebraTensorModule.map (LinearMap.id : ℝ →ₗ[ℝ] ℝ) W.subtype

omit [Module.Finite ℚ V] in
theorem realifyMap_rationalPoint (W : Submodule ℚ V) (w : ↥W) :
    realifyMap W (rationalPoint w) = rationalPoint (w : V) := by
  simp [realifyMap, rationalPoint, TensorProduct.AlgebraTensorModule.map_tmul]

/-- The real form of `W` as a subspace of `V(ℝ)`. -/
noncomputable def realify (W : Submodule ℚ V) : Submodule ℝ (realified V) :=
  LinearMap.range (realifyMap W)

omit [Module.Finite ℚ V] in
theorem mem_realify_iff (W : Submodule ℚ V) (x : realified V) :
    x ∈ realify W ↔ x ∈ Submodule.span ℝ (rationalPoint '' (W : Set V)) := by
  constructor
  · rintro ⟨y, rfl⟩
    have hy : y ∈ Submodule.span ℝ (Set.range (rationalPoint (V := ↥W))) := by
      rw [span_range_rationalPoint]; trivial
    have hmap : Submodule.span ℝ (Set.range (rationalPoint (V := ↥W))) ≤
        Submodule.comap (realifyMap W)
          (Submodule.span ℝ (rationalPoint '' (W : Set V))) := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨w, rfl⟩
      exact Submodule.subset_span ⟨(w : V), w.2, realifyMap_rationalPoint W w⟩
    exact hmap hy
  · intro hx
    refine Submodule.span_le.2 ?_ hx
    rintro _ ⟨v, hv, rfl⟩
    exact ⟨rationalPoint ⟨v, hv⟩, realifyMap_rationalPoint W ⟨v, hv⟩⟩

omit [Module.Finite ℚ V] in
/-- The inclusion of the real form of a subspace is injective: `ℝ` is flat over `ℚ`. -/
theorem realifyMap_injective (W : Submodule ℚ V) : Function.Injective (realifyMap W) := by
  have key : ∀ x : realified ↥W, realifyMap W x = (W.subtype.lTensor ℝ) x := by
    intro x
    induction x using TensorProduct.inductionOn with
    | tmul r w => simp [realifyMap, TensorProduct.AlgebraTensorModule.map_tmul]
    | add a b ha hb => rw [map_add, map_add, ha, hb]
  intro x y h
  rw [key x, key y] at h
  exact Module.Flat.lTensor_preserves_injective_linearMap (M := ℝ) W.subtype
    Subtype.val_injective h

omit [Module.Finite ℚ V] in
theorem realify_mono {A B : Submodule ℚ V} (h : A ≤ B) : realify A ≤ realify B := by
  intro x hx
  rw [mem_realify_iff] at hx ⊢
  exact Submodule.span_mono (Set.image_mono h) hx

omit [Module.Finite ℚ V] in
theorem realify_sup (A B : Submodule ℚ V) : realify (A ⊔ B) = realify A ⊔ realify B := by
  refine le_antisymm ?_ (sup_le (realify_mono le_sup_left) (realify_mono le_sup_right))
  intro x hx
  rw [mem_realify_iff] at hx
  refine Submodule.span_le.2 ?_ hx
  rintro _ ⟨v, hv, rfl⟩
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hv
  rw [map_add]
  refine Submodule.add_mem _
    (Submodule.mem_sup_left ((mem_realify_iff A _).2 (Submodule.subset_span ⟨a, ha, rfl⟩)))
    (Submodule.mem_sup_right ((mem_realify_iff B _).2 (Submodule.subset_span ⟨b, hb, rfl⟩)))

omit [Module.Finite ℚ V] in
theorem realify_top : realify (⊤ : Submodule ℚ V) = ⊤ := by
  refine le_antisymm le_top ?_
  intro x _
  rw [mem_realify_iff]
  have hle : Submodule.span ℝ (Set.range (rationalPoint (V := V))) ≤
      Submodule.span ℝ (rationalPoint '' ((⊤ : Submodule ℚ V) : Set V)) := by
    refine Submodule.span_mono ?_
    rintro _ ⟨v, rfl⟩
    exact ⟨v, trivial, rfl⟩
  exact hle (by rw [span_range_rationalPoint]; trivial)

/-! ## The induced form on a conical fibre -/

/-- The form of a conical fibre: the restriction of the ambient form `Q` to `W(ℝ) ⊆ V(ℝ)`.
For `W` a complement of a `ℚ`-isotropic line `I` in `I^⊥` this is the form on `I^⊥/I ⊗ I` of
Looijenga §1B, p. 11 (text line 251). -/
noncomputable def fibreForm (Q : QuadraticForm ℝ (realified V))
    (W : Submodule ℚ V) : QuadraticForm ℝ (realified ↥W) :=
  Q.comp (realifyMap W)

variable {Q : QuadraticForm ℝ (realified V)}

omit [Module.Finite ℚ V] in
theorem fibreForm_rationalPoint {BQ : LinearMap.BilinForm ℚ V} (hBQ : ∀ u w : V,
    (associated Q) (rationalPoint u) (rationalPoint w) = (BQ u w : ℝ)) (W : Submodule ℚ V)
    (w : ↥W) : fibreForm Q W (rationalPoint w) = (BQ (w : V) (w : V) : ℝ) := by
  rw [fibreForm, QuadraticMap.comp_apply, realifyMap_rationalPoint, ← hBQ,
    QuadraticMap.associated_eq_self_apply]

omit [Module.Finite ℚ V] in
theorem associated_fibreForm (W : Submodule ℚ V) (x y : realified ↥W) :
    (associated (fibreForm Q W)) x y = (associated Q) (realifyMap W x) (realifyMap W y) := by
  rw [fibreForm, QuadraticMap.associated_comp]
  rfl


/-! ## The complement of a hyperbolic plane: the carrier of `I^⊥/I`

Looijenga §1B, p. 11 (text line 251): for a `ℚ`-isotropic line `I = ℚ e` and a hyperbolic partner
`f` (`f` isotropic, `e · f = 1`), the reduction `I^⊥/I` is carried by the orthogonal complement of
the plane `⟨e, f⟩`. The form on it is the restriction of the ambient form, and it has signature
`(1, n - 1)`: the source's "this signature remains `(1, n-1)`". -/

/-- The orthogonal complement of the hyperbolic plane `⟨e, f⟩`, the carrier of `I^⊥/I` for
`I = ℚ e` (Looijenga §1B, p. 11). -/
noncomputable def planeComplement (BQ : LinearMap.BilinForm ℚ V) (e f : V) : Submodule ℚ V :=
  BQ.orthogonal (Submodule.span ℚ ({e, f} : Set V))

omit [Module.Finite ℚ V] in
theorem mem_planeComplement_iff (BQ : LinearMap.BilinForm ℚ V) {e f x : V} :
    x ∈ planeComplement BQ e f ↔ BQ e x = 0 ∧ BQ f x = 0 := by
  rw [planeComplement, LinearMap.BilinForm.mem_orthogonal_iff]
  constructor
  · intro h
    exact ⟨h e (Submodule.subset_span (by simp)), h f (Submodule.subset_span (by simp))⟩
  · rintro ⟨h1, h2⟩ z hz
    obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.mp hz
    rw [← hab, map_add, map_smul, map_smul]
    simp only [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, h1, h2]
    ring

section HyperbolicPlane

variable {BQ : LinearMap.BilinForm ℚ V} {e f : V}

omit [Module.Finite ℚ V] in
/-- The complement of the hyperbolic plane and the plane itself span `V`. -/
theorem planeComplement_sup (hBsym : BQ.IsSymm) (he : BQ e e = 0) (hf : BQ f f = 0)
    (hef : BQ e f = 1) :
    planeComplement BQ e f ⊔ Submodule.span ℚ ({e, f} : Set V) = ⊤ := by
  refine Submodule.eq_top_iff'.2 fun x => ?_
  have hfe : BQ f e = 1 := by rw [hBsym.eq]; exact hef
  have hxe : BQ x e = BQ e x := hBsym.eq x e
  have hxf : BQ x f = BQ f x := hBsym.eq x f
  have hx : x - BQ x f • e - BQ x e • f ∈ planeComplement BQ e f := by
    rw [mem_planeComplement_iff]
    constructor
    · show BQ e (x - BQ x f • e - BQ x e • f) = 0
      rw [map_sub, map_sub, map_smul, map_smul, smul_eq_mul, smul_eq_mul, he, hef, hxe]
      ring
    · show BQ f (x - BQ x f • e - BQ x e • f) = 0
      rw [map_sub, map_sub, map_smul, map_smul, smul_eq_mul, smul_eq_mul, hfe, hf, hxf]
      ring
  have hsum : (x - BQ x f • e - BQ x e • f) + BQ x f • e + BQ x e • f = x := by abel
  have hmem : (x - BQ x f • e - BQ x e • f) + BQ x f • e + BQ x e • f
      ∈ planeComplement BQ e f ⊔ Submodule.span ℚ ({e, f} : Set V) := by
    have h1 : x - BQ x f • e - BQ x e • f
        ∈ planeComplement BQ e f ⊔ Submodule.span ℚ ({e, f} : Set V) :=
      Submodule.mem_sup_left hx
    have h2 : BQ x f • e ∈ planeComplement BQ e f ⊔ Submodule.span ℚ ({e, f} : Set V) :=
      Submodule.mem_sup_right (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
    have h3 : BQ x e • f ∈ planeComplement BQ e f ⊔ Submodule.span ℚ ({e, f} : Set V) :=
      Submodule.mem_sup_right (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
    exact Submodule.add_mem _ (Submodule.add_mem _ h1 h2) h3
  simpa only [hsum] using hmem

end HyperbolicPlane

section ConicalFibre

variable {BQ : LinearMap.BilinForm ℚ V} {Q : QuadraticForm ℝ (realified V)} {e f : V}

omit [Module.Finite ℚ V] in
theorem realified_span_pair :
    realify (Submodule.span ℚ ({e, f} : Set V)) =
      Submodule.span ℝ ({rationalPoint e, rationalPoint f} : Set (realified V)) := by
  refine le_antisymm ?_ ?_
  · intro x hx
    rw [mem_realify_iff] at hx
    refine Submodule.span_le.2 ?_ hx
    rintro _ ⟨v, hv, rfl⟩
    obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.mp hv
    rw [← hab, map_add, map_smul, map_smul]
    exact Submodule.add_mem _
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
  · intro x hx
    rw [mem_realify_iff]
    refine Submodule.span_le.2 ?_ hx
    intro y hy
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl
    · exact Submodule.subset_span ⟨e, Submodule.subset_span (by simp), rfl⟩
    · exact Submodule.subset_span ⟨f, Submodule.subset_span (by simp), rfl⟩

/-- **The complement of the hyperbolic plane is contained in the orthogonal complement of the
isotropic line**, in the real form: the source's `I^⊥/I → I^⊥`. -/
theorem realify_planeComplement_le_planePerp (hBQ : ∀ u w : V,
    (associated Q) (rationalPoint u) (rationalPoint w) = (BQ u w : ℝ)) :
    realify (planeComplement BQ e f) ≤ planePerp Q (rationalPoint e) (rationalPoint f) := by
  intro x hx
  rw [mem_realify_iff] at hx
  refine Submodule.span_le.2 ?_ hx
  rintro _ ⟨w, hw, rfl⟩
  refine mem_planePerp_iff.2 ⟨?_, ?_⟩
  · rw [hBQ, ((mem_planeComplement_iff BQ).1 hw).1]
    norm_num
  · rw [hBQ, ((mem_planeComplement_iff BQ).1 hw).2]
    norm_num

omit [Module.Finite ℚ V] in
/-- The span of the complement of the hyperbolic plane and of the plane is everything. -/
theorem realify_planeComplement_sup (hBsym : BQ.IsSymm) (he : BQ e e = 0) (hf : BQ f f = 0)
    (hef : BQ e f = 1) :
    realify (planeComplement BQ e f) ⊔
      Submodule.span ℝ ({rationalPoint e, rationalPoint f} : Set (realified V)) = ⊤ := by
  rw [← realified_span_pair, ← realify_sup, planeComplement_sup hBsym he hf hef, realify_top]

end ConicalFibre

/-! ## The conical locus and its members

Definition 2.1 (p. 10, text line 279) and Definition 6.1 (p. 28, text line 769) of the source. The
conical locus is the disjoint union of the cones `C_I` over the `ℚ`-isotropic subspaces `I` of `V`
(`I = {0}`, an isotropic line, or an isotropic plane); each cone sits in `Λ²V(ℝ) ≅ so(φ)(ℝ)`.

**The carrier.** The fibre of a `ℚ`-isotropic line `I = ℚ e` is carried as `I^⊥/I ≅ ⟨e, f⟩^⊥`
(`planeComplement`), and that of an isotropic plane `J` is the line `J/I` inside the fibre of any
of its lines `I`. Every fibre is thus a `ℚ`-subspace of `V` (via `realify`), which is what makes the
support spaces of Definition 6.1 — subspaces of `V` — statements about one ambient space. -/

/-- The conical fibre at a `ℚ`-isotropic line `I`: Looijenga §1B, p. 11, and Definition 2.1, p. 10.
The line `I` is `ℚ gen`, `partner` is a hyperbolic partner (so that the reduction `I^⊥/I` is carried
by `⟨gen, partner⟩^⊥`), and `sheet` is a positive vector of that reduction, which is the choice of
the cone `C_I` among the two sheets. -/
structure ConicalLine (BQ : LinearMap.BilinForm ℚ V) (Q : QuadraticForm ℝ (realified V)) where
  /-- the isotropic line -/
  line : Submodule ℚ V
  /-- it is totally isotropic -/
  isotropic : ∀ x ∈ line, ∀ y ∈ line, BQ x y = 0
  /-- it is a line -/
  one_dim : Module.finrank ℚ ↥line = 1
  /-- a `ℚ`-generator of the line -/
  gen : V
  line_eq : line = Submodule.span ℚ {gen}
  gen_iso : BQ gen gen = 0
  gen_ne : gen ≠ 0
  /-- a hyperbolic partner of the generator (Looijenga §1B, p. 11) -/
  partner : V
  partner_iso : BQ partner partner = 0
  pairing : BQ gen partner = 1
  /-- a positive vector of the reduction `I^⊥/I`: the choice of the cone `C_I` -/
  sheet : realified ↥(planeComplement BQ gen partner)
  sheet_pos : 0 < fibreForm Q (planeComplement BQ gen partner) sheet

namespace ConicalLine

variable {BQ : LinearMap.BilinForm ℚ V} {Q : QuadraticForm ℝ (realified V)} (F : ConicalLine BQ Q)

/-- The carrier of the reduction `I^⊥/I` of a conical fibre. It is an `abbrev` and the cone and
the closure below are typed by the explicit `planeComplement`, so that the *carrier* of a fibre and
the types of its sheet, its cone and its closure are interchangeable syntactically: transporting a
fibre along an isometry of `V` (`Semifan.ConicalLine.map`) moves all of them at once, and the
support spaces of §6 can be compared across two fibres without a transport isomorphism of
realifications. -/
noncomputable abbrev space : Submodule ℚ V :=
  planeComplement BQ F.gen F.partner

omit [Module.Finite ℚ V] in
theorem mem_space_iff {x : V} : x ∈ F.space ↔ BQ F.gen x = 0 ∧ BQ F.partner x = 0 :=
  mem_planeComplement_iff BQ

/-- The open cone `C_I` of Definition 2.1, p. 10: the upper sheet of the reduction `I^⊥/I` at the
chosen positive vector. -/
noncomputable def cone : PointedCone ℝ (realified ↥(planeComplement BQ F.gen F.partner)) :=
  PointedCone.hull ℝ
    (positiveCone.upper (fibreForm Q (planeComplement BQ F.gen F.partner)) F.sheet)

/-- The rational closure `C_{I,+}` of Definition 4.2, p. 17, at the conical fibre: the carrier of
the locally rational decomposition that condition (i) of Definition 6.1 asks for. -/
noncomputable def closure : PointedCone ℝ (realified ↥(planeComplement BQ F.gen F.partner)) :=
  rationalClosure (F.cone : PointedCone ℝ (realified ↥(planeComplement BQ F.gen F.partner)))

end ConicalLine

/-- **An oriented `ℚ`-isotropic plane of the conical locus**: Looijenga §1A, p. 10, with the
positive rational generator of Example 6.3, p. 29.

The data of the source is the *positive rational generator* `r_J ∈ ⋀²J(ℚ)`. The choice of the
component `D` "determines an orientation of `J(ℝ)`. This means that the punctured line
`⋀²J(ℝ) − {0}` has a distinguished component. We shall denote this component by `C_J`" (§1A,
p. 10), and Example 6.3 (p. 29) asks for a positive rational generator `r_J` for every plane `J`;
the half line `C_J` is then `{t • r_J | 0 < t}`.

`r_J` is carried by the ordered `ℚ`-basis `(dir, dirAlt)` of `J` with `r_J = dir ∧ dirAlt`: every
generator of `⋀²J(ℚ)` is the wedge of a basis, and exchanging the two vectors negates the wedge, so
an orientation of `J` is exactly an ordered basis up to the sign of its wedge.

**The plane's ray in a fibre is derived, not stored.** A single vector cannot generate `J` modulo
*every* line of `J`: a vector that generates `J` modulo `I` must lie outside `I`, so no vector does
so for `I = ℚ ray` itself — which is exactly what the discarded field `ray_not_mem_of_line`
demanded, and that field made the carrier empty. `rayOf` instead computes the ray relative to each
witnessing line `I = ℚ g` from `r_J`: it is the vector `ρ ∈ J` with `g ∧ ρ = r_J`, so that `g ⊗ ρ`
is the image of `r_J` under the inclusion `⋀²J ⊂ I ⊗ I^⊥/I` of §1B, p. 11. -/
structure ConicalPlane (BQ : LinearMap.BilinForm ℚ V) where
  /-- the isotropic plane -/
  plane : Submodule ℚ V
  /-- it is totally isotropic -/
  isotropic : ∀ x ∈ plane, ∀ y ∈ plane, BQ x y = 0
  /-- it is a plane -/
  two_dim : Module.finrank ℚ ↥plane = 2
  /-- the positively oriented basis `(e, f)` of `J`: its wedge `e ∧ f` is the positive rational
  generator `r_J ∈ ⋀²J(ℚ)` of Example 6.3, p. 29 -/
  basis : Module.Basis (Fin 2) ℚ ↥plane

namespace ConicalPlane

variable {BQ : LinearMap.BilinForm ℚ V} (G : ConicalPlane BQ)

omit [Module.Finite ℚ V]

/-- The first vector `e` of the positive basis of the plane. -/
noncomputable def dir : V := (G.basis 0 : V)

/-- The second vector `f` of the positive basis of the plane; the positive rational generator of
`⋀²J(ℚ)` is `dir ∧ dirAlt`. -/
noncomputable def dirAlt : V := (G.basis 1 : V)

theorem dir_mem : G.dir ∈ G.plane := (G.basis 0).2

theorem dirAlt_mem : G.dirAlt ∈ G.plane := (G.basis 1).2

theorem dir_iso : BQ G.dir G.dir = 0 := G.isotropic G.dir G.dir_mem G.dir G.dir_mem

theorem dirAlt_iso : BQ G.dirAlt G.dirAlt = 0 :=
  G.isotropic G.dirAlt G.dirAlt_mem G.dirAlt G.dirAlt_mem

theorem dir_pairing : BQ G.dir G.dirAlt = 0 :=
  G.isotropic G.dir G.dir_mem G.dirAlt G.dirAlt_mem

theorem dir_ne : G.dir ≠ 0 := by
  intro h
  exact G.basis.ne_zero 0 (Subtype.ext h)

theorem dirAlt_ne : G.dirAlt ≠ 0 := by
  intro h
  exact G.basis.ne_zero 1 (Subtype.ext h)

/-- The coordinates of a vector of the plane are the coordinates of its class in the positive
basis. -/
theorem repr_eq (x : ↥G.plane) :
    (x : V) = G.basis.repr x 0 • G.dir + G.basis.repr x 1 • G.dirAlt := by
  have h := G.basis.sum_repr x
  rw [Fin.sum_univ_two] at h
  rw [← h]
  simp [dir, dirAlt]

theorem repr_zero_eq_zero_of_eq_zero {x : ↥G.plane} (h : (x : V) = 0) :
    G.basis.repr x 0 = 0 ∧ G.basis.repr x 1 = 0 := by
  have hx : x = 0 := Subtype.ext h
  rw [hx]
  simp

/-- **The ray of the plane in the fibre of a witnessing line** `I = ℚ g` (`g ∈ J`, `g ≠ 0`): the
vector `ρ ∈ J` with `g ∧ ρ = r_J`, written in the positive basis `(e, f)` of `J`. If the coefficient
`a` of `g` along `e` does not vanish, `ρ = a⁻¹ f`; if it does, `g` is a multiple `b f` of `f` and
`ρ = −b⁻¹ e`. The class of `ρ` in the reduction `I^⊥/I` is the image of `r_J` under the inclusion
`⋀²J ⊂ I ⊗ I^⊥/I` of §1B, p. 11, and it is a ray: a positive rescaling of `g` rescales `ρ` by the
inverse positive scalar, so the half line is unchanged. -/
noncomputable def rayOf (g : V) (hg : g ∈ G.plane) (_hg0 : g ≠ 0) : V :=
  if G.basis.repr ⟨g, hg⟩ 0 = 0 then -(G.basis.repr ⟨g, hg⟩ 1)⁻¹ • G.dir
  else (G.basis.repr ⟨g, hg⟩ 0)⁻¹ • G.dirAlt

/-- The ray written with a nonvanishing coefficient along `e`. -/
theorem rayOf_eq_smul_dirAlt {g : V} (hg : g ∈ G.plane) (hg0 : g ≠ 0)
    (h : G.basis.repr ⟨g, hg⟩ 0 ≠ 0) :
    G.rayOf g hg hg0 = (G.basis.repr ⟨g, hg⟩ 0)⁻¹ • G.dirAlt := by
  rw [rayOf]
  simp only [h, ite_false]

/-- The ray written when `g` is a multiple of `f`. -/
theorem rayOf_eq_smul_dir {g : V} (hg : g ∈ G.plane) (hg0 : g ≠ 0)
    (h : G.basis.repr ⟨g, hg⟩ 0 = 0) :
    G.rayOf g hg hg0 = -(G.basis.repr ⟨g, hg⟩ 1)⁻¹ • G.dir := by
  rw [rayOf]
  simp only [h, ite_true]

/-- In the second case of `rayOf`, the coefficient along `f` does not vanish. -/
theorem repr_one_ne_zero_of_repr_zero_eq_zero {g : V} (hg : g ∈ G.plane) (hg0 : g ≠ 0)
    (h : G.basis.repr ⟨g, hg⟩ 0 = 0) : G.basis.repr ⟨g, hg⟩ 1 ≠ 0 := by
  intro hb
  apply hg0
  have := G.repr_eq ⟨g, hg⟩
  rw [h, hb] at this
  simpa using this

theorem rayOf_mem {g : V} (hg : g ∈ G.plane) (hg0 : g ≠ 0) : G.rayOf g hg hg0 ∈ G.plane := by
  by_cases h : G.basis.repr ⟨g, hg⟩ 0 = 0
  · rw [rayOf_eq_smul_dir G hg hg0 h]
    exact Submodule.smul_mem _ _ G.dir_mem
  · rw [rayOf_eq_smul_dirAlt G hg hg0 h]
    exact Submodule.smul_mem _ _ G.dirAlt_mem

theorem rayOf_ne {g : V} (hg : g ∈ G.plane) (hg0 : g ≠ 0) : G.rayOf g hg hg0 ≠ 0 := by
  by_cases h : G.basis.repr ⟨g, hg⟩ 0 = 0
  · rw [rayOf_eq_smul_dir G hg hg0 h]
    have hb := G.repr_one_ne_zero_of_repr_zero_eq_zero hg hg0 h
    have hb' : -((G.basis.repr ⟨g, hg⟩ 1)⁻¹) ≠ 0 := by
      simp [hb]
    simpa using smul_ne_zero hb' G.dir_ne
  · rw [rayOf_eq_smul_dirAlt G hg hg0 h]
    have ha : (G.basis.repr ⟨g, hg⟩ 0)⁻¹ ≠ 0 := by simp [h]
    simpa using smul_ne_zero ha G.dirAlt_ne

/-- The ray pairs trivially with the line's generator: both lie in the totally isotropic plane. -/
theorem rayOf_pairing {g : V} (hg : g ∈ G.plane) (hg0 : g ≠ 0) :
    BQ g (G.rayOf g hg hg0) = 0 :=
  G.isotropic g hg (G.rayOf g hg hg0) (G.rayOf_mem hg hg0)

theorem rayOf_iso {g : V} (hg : g ∈ G.plane) (hg0 : g ≠ 0) :
    BQ (G.rayOf g hg hg0) (G.rayOf g hg hg0) = 0 :=
  G.isotropic (G.rayOf g hg hg0) (G.rayOf_mem hg hg0) (G.rayOf g hg hg0) (G.rayOf_mem hg hg0)

/-- The ray does not lie on the line it is taken relative to. -/
theorem rayOf_not_mem_span {g : V} (hg : g ∈ G.plane) (hg0 : g ≠ 0) :
    G.rayOf g hg hg0 ∉ Submodule.span ℚ ({g} : Set V) := by
  intro hmem
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 hmem
  have hsub : (⟨c • g, G.plane.smul_mem c hg⟩ : ↥G.plane)
      = ⟨G.rayOf g hg hg0, G.rayOf_mem hg hg0⟩ := Subtype.ext hc
  have hsm : (⟨c • g, G.plane.smul_mem c hg⟩ : ↥G.plane) = c • ⟨g, hg⟩ := Subtype.ext rfl
  set a : ℚ := G.basis.repr ⟨g, hg⟩ 0 with ha
  set b : ℚ := G.basis.repr ⟨g, hg⟩ 1 with hb
  have hz10 : G.basis.repr (G.basis 0) 1 = 0 := by
    rw [G.basis.repr_self]
    simp
  have hz01 : G.basis.repr (G.basis 1) 0 = 0 := by
    rw [G.basis.repr_self]
    simp
  by_cases h : a = 0
  · have hb0 : b ≠ 0 := G.repr_one_ne_zero_of_repr_zero_eq_zero hg hg0 h
    have hray : (⟨G.rayOf g hg hg0, G.rayOf_mem hg hg0⟩ : ↥G.plane)
        = -(b⁻¹) • G.basis 0 := by
      have h1 : (⟨G.rayOf g hg hg0, G.rayOf_mem hg hg0⟩ : ↥G.plane)
          = ⟨-(b⁻¹) • G.dir, G.plane.smul_mem _ G.dir_mem⟩ :=
        Subtype.ext (rayOf_eq_smul_dir G hg hg0 h)
      rw [h1]
      rfl
    have h1 := congrArg (fun x : ↥G.plane => G.basis.repr x 1) hsub
    rw [hsm, hray] at h1
    simp only [map_smul, Finsupp.smul_apply, smul_eq_mul, ← hb, hz10, mul_zero] at h1
    have hc0 : c = 0 := by
      rcases mul_eq_zero.1 h1 with h' | h'
      · exact h'
      · exact absurd h' hb0
    apply G.rayOf_ne hg hg0
    rw [← hc, hc0, zero_smul]
  · have hray : (⟨G.rayOf g hg hg0, G.rayOf_mem hg hg0⟩ : ↥G.plane)
        = a⁻¹ • G.basis 1 := by
      have h1 : (⟨G.rayOf g hg hg0, G.rayOf_mem hg hg0⟩ : ↥G.plane)
          = ⟨a⁻¹ • G.dirAlt, G.plane.smul_mem _ G.dirAlt_mem⟩ :=
        Subtype.ext (rayOf_eq_smul_dirAlt G hg hg0 h)
      rw [h1]
      rfl
    have h1 := congrArg (fun x : ↥G.plane => G.basis.repr x 0) hsub
    rw [hsm, hray] at h1
    simp only [map_smul, Finsupp.smul_apply, smul_eq_mul, ← ha, hz01, mul_zero] at h1
    have hc0 : c = 0 := by
      rcases mul_eq_zero.1 h1 with h' | h'
      · exact h'
      · exact absurd h' h
    apply G.rayOf_ne hg hg0
    rw [← hc, hc0, zero_smul]

theorem span_dir_eq : Submodule.span ℚ ({G.dir, G.dirAlt} : Set V) = G.plane := by
  refine le_antisymm ?_ ?_
  · refine Submodule.span_le.2 ?_
    intro x hx
    rcases Set.mem_insert_iff.1 hx with rfl | hx
    · exact G.dir_mem
    · rw [Set.mem_singleton_iff] at hx
      subst hx
      exact G.dirAlt_mem
  · intro x hx
    rw [show x = G.basis.repr ⟨x, hx⟩ 0 • G.dir + G.basis.repr ⟨x, hx⟩ 1 • G.dirAlt
      from G.repr_eq ⟨x, hx⟩]
    exact Submodule.add_mem _
      (Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_insert _ _)))
      (Submodule.smul_mem _ _
        (Submodule.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))))

end ConicalPlane

section Fibre

variable {BQ : LinearMap.BilinForm ℚ V} {Q : QuadraticForm ℝ (realified V)}
variable (hBsym : BQ.IsSymm)

/-- The hyperbolic projection of a vector to the fibre of a conical line: `x ↦ x - (x·f) e -
(x·e) f`, which kills the components along `e` and `f` (`planeComplement`). -/
noncomputable def fibreProj (F : ConicalLine BQ Q) (x : V) : ↥F.space :=
  ⟨x - BQ x F.partner • F.gen - BQ x F.gen • F.partner, by
    rw [ConicalLine.mem_space_iff]
    have hxe : BQ x F.gen = BQ F.gen x := hBsym.eq x F.gen
    have hxf : BQ x F.partner = BQ F.partner x := hBsym.eq x F.partner
    have hfe : BQ F.partner F.gen = 1 := by rw [hBsym.eq]; exact F.pairing
    constructor
    · show BQ F.gen (x - BQ x F.partner • F.gen - BQ x F.gen • F.partner) = 0
      rw [map_sub, map_sub, map_smul, map_smul, smul_eq_mul, smul_eq_mul, F.gen_iso, F.pairing,
        hxe]
      ring
    · show BQ F.partner (x - BQ x F.partner • F.gen - BQ x F.gen • F.partner) = 0
      rw [map_sub, map_sub, map_smul, map_smul, smul_eq_mul, smul_eq_mul, hfe,
        F.partner_iso, hxf]
      ring⟩

omit [Module.Finite ℚ V] in
/-- The generator of a witnessing line `I ≤ J` lies in the plane. -/
theorem ConicalLine.gen_mem_of_le (F : ConicalLine BQ Q) (G : ConicalPlane BQ)
    (h : F.line ≤ G.plane) : F.gen ∈ G.plane := by
  refine h ?_
  rw [F.line_eq]
  exact Submodule.subset_span (Set.mem_singleton F.gen)

/-- **The ray of an oriented plane in the fibre of a witnessing line**, as a `ℚ`-vector of `V`: the
vector `ρ ∈ J` with `F.gen ∧ ρ = r_J` (`ConicalPlane.rayOf`). Its class in the fibre is
`fibreRayProj`. -/
noncomputable def ConicalLine.planeRay (F : ConicalLine BQ Q) (G : ConicalPlane BQ)
    (h : F.line ≤ G.plane) : V :=
  G.rayOf F.gen (F.gen_mem_of_le G h) F.gen_ne

omit [Module.Finite ℚ V] in
theorem ConicalLine.planeRay_mem (F : ConicalLine BQ Q) (G : ConicalPlane BQ)
    (h : F.line ≤ G.plane) : F.planeRay G h ∈ G.plane :=
  G.rayOf_mem (F.gen_mem_of_le G h) F.gen_ne

omit [Module.Finite ℚ V] in
theorem ConicalLine.planeRay_ne (F : ConicalLine BQ Q) (G : ConicalPlane BQ)
    (h : F.line ≤ G.plane) : F.planeRay G h ≠ 0 :=
  G.rayOf_ne (F.gen_mem_of_le G h) F.gen_ne

omit [Module.Finite ℚ V] in
theorem ConicalLine.planeRay_self (F : ConicalLine BQ Q) (G : ConicalPlane BQ)
    (h : F.line ≤ G.plane) : BQ (F.planeRay G h) (F.planeRay G h) = 0 :=
  G.rayOf_iso (F.gen_mem_of_le G h) F.gen_ne

omit [Module.Finite ℚ V] in
theorem ConicalLine.planeRay_gen (F : ConicalLine BQ Q) (G : ConicalPlane BQ)
    (h : F.line ≤ G.plane) : BQ F.gen (F.planeRay G h) = 0 :=
  G.rayOf_pairing (F.gen_mem_of_le G h) F.gen_ne

omit [Module.Finite ℚ V] in
/-- The ray of the plane in the fibre of `I` does not lie in `I` (the true form of the discarded
field `ConicalPlane.ray_not_mem_of_line`, whose quantifier over all lines of the plane no vector
satisfies). -/
theorem ConicalLine.planeRay_not_mem_line (F : ConicalLine BQ Q) (G : ConicalPlane BQ)
    (h : F.line ≤ G.plane) : F.planeRay G h ∉ F.line := by
  rw [F.line_eq]
  exact G.rayOf_not_mem_span (F.gen_mem_of_le G h) F.gen_ne

/-- **The class of the plane's ray in the conical fibre of one of its lines**, *without* the choice
of half line: Looijenga §1B, p. 11 (text line 265), "`Λ²J` can be regarded as a line in
`I ⊗ I^⊥/I`". It is the class of `G.rayOf` at the line's generator: the vector `ρ ∈ J` with
`gen ∧ ρ = r_J`, so that `gen ⊗ ρ` is the image of the positive generator `r_J` of `⋀²J(ℚ)`
(`ConicalPlane.basis`) under the inclusion of §1B. The scan is the one of `fibreProj`: the
adjustment is along the hyperbolic partner only, because `ρ · gen = 0` (both lie in the totally
isotropic plane). -/
noncomputable def fibreRayProj (F : ConicalLine BQ Q) (G : ConicalPlane BQ)
    (h : F.line ≤ G.plane) : ↥F.space :=
  fibreProj hBsym F (G.rayOf F.gen (F.gen_mem_of_le G h) F.gen_ne)

omit [Module.Finite ℚ V] in
/-- **The class of a plane's ray in the fibre of one of its lines**: Looijenga §1B, p. 11 (text
line 265), "`Λ²J` can be regarded as a line in `I ⊗ I^⊥/I`". The representative in the carrier
`planeComplement` of the fibre is `ray - (ray · f) e`: the adjustment is along the hyperbolic
partner `f` only, because `ray · e = 0` (both lie in the totally isotropic plane). -/
theorem fibreRayProj_val (hBsym : BQ.IsSymm) (F : ConicalLine BQ Q) (G : ConicalPlane BQ)
    (h : F.line ≤ G.plane) :
    ((fibreRayProj hBsym F G h : ↥F.space) : V) =
      F.planeRay G h - BQ (F.planeRay G h) F.partner • F.gen := by
  have hge : BQ (G.rayOf F.gen (F.gen_mem_of_le G h) F.gen_ne) F.gen = 0 := by
    rw [hBsym.eq]
    exact G.rayOf_pairing (F.gen_mem_of_le G h) F.gen_ne
  simp only [fibreRayProj, fibreProj, ConicalLine.planeRay, hge, zero_smul, sub_zero]

/-- **The coherence of an oriented plane with the sheet of an incident fibre** — Looijenga §1B,
p. 11 (text line 267) and Example 6.3, p. 29 (text line 785). The source states it as: for a
`ℚ`-isotropic plane `J ⊇ I`, "`r_J` can be regarded as an isotropic vector in `(C_I)_+` via the
inclusion `⋀²J ⊂ I ⊗ I^⊥/I`", and "`C_J` is contained in the boundary of `C_I`". Here `C_J ⊂ ⋀²J(ℝ)`
is the distinguished component of the punctured line, generated by the plane's positive rational
generator `r_J = dir ∧ dirAlt` (`ConicalPlane.basis`), and `C_I` is the cone of the fibre, named by
its positive vector `sheet`. The class of `r_J` in the reduction `I^⊥/I` therefore pairs
*positively* with `sheet`: that is exactly the statement that the half line of `r_J` lies in the
closed cone `C_{I,+}` rather than in its antipode.

The two pieces of data are independent in `ConicalLine` and `ConicalPlane` — a sheet is a choice of
cone at a fibre, an orientation is a choice of generator in `⋀²J` — so this is a genuine condition
on the *pair* (plane, fibre), not a definitional fact. `ConicalLine.sheet` and its negation are both
valid `ConicalLine`s, and they induce the two opposite classes of `r_J` in `I^⊥/I`
(`fibreRay_eq_or_neg`); only one of them is coherent with the plane's orientation. -/
def ConicalPlane.IsPositiveAt (F : ConicalLine BQ Q) (G : ConicalPlane BQ)
    (h : F.line ≤ G.plane) : Prop :=
  0 < (associated Q) (rationalPoint (F.planeRay G h - BQ (F.planeRay G h) F.partner • F.gen))
    (realifyMap F.space F.sheet)

/-- **The half line `C_{J,+}` of a `ℚ`-isotropic plane in the fibre of one of its lines**: the class
of the plane's ray, or its opposite, whichever lies on the **closed sheet** of the fibre's cone —
the isotropic ray `r` of the fibre with `0 ≤ r · t` at the fibre's positive vector `t`.

Looijenga §1B, p. 11 (text line 267): "`Λ²J` can be regarded as a line in `I ⊗ I^⊥/I` and via this
inclusion, `C_J` is contained in the boundary of `C_I`". The fibre `ConicalLine` carries its sheet
`C_I` as data, and of the two half lines of the isotropic line `J/I` exactly one is a boundary ray
of the closed sheet of `C_I` (`0 < r · t` for a positive `t` in signature `(1, n-1)`, so the two
have opposite signs at `t`); this is that half line. It is the member `σ = C_{J,+}` of Definition
6.1 (ii), the one whose `Σ`-support space the definition names. -/
noncomputable def fibreRay (F : ConicalLine BQ Q) (G : ConicalPlane BQ)
    (h : F.line ≤ G.plane) : ↥F.space :=
  if 0 ≤ (associated (fibreForm Q F.space)) (rationalPoint (fibreRayProj hBsym F G h)) F.sheet
  then fibreRayProj hBsym F G h else -fibreRayProj hBsym F G h

omit [Module.Finite ℚ V] in
/-- The half line is one of the two generators of the plane's class in the fibre. -/
theorem fibreRay_eq_or_neg (F : ConicalLine BQ Q) (G : ConicalPlane BQ)
    (h : F.line ≤ G.plane) :
    fibreRay hBsym F G h = fibreRayProj hBsym F G h ∨
      fibreRay hBsym F G h = -fibreRayProj hBsym F G h := by
  rw [fibreRay]
  split_ifs with h
  · exact Or.inl rfl
  · exact Or.inr rfl

omit [Module.Finite ℚ V] in
/-- **The half line lies on the closed sheet of the fibre's cone**: `0 ≤ r · t`. -/
theorem fibreRay_sheet_nonneg (F : ConicalLine BQ Q) (G : ConicalPlane BQ)
    (h : F.line ≤ G.plane) :
    0 ≤ (associated (fibreForm Q F.space)) (rationalPoint (fibreRay hBsym F G h)) F.sheet := by
  rw [fibreRay]
  split_ifs with h
  · exact h
  · rw [map_neg, LinearMap.BilinForm.neg_left]
    linarith [lt_of_not_ge h]

omit [Module.Finite ℚ V] in
/-- **The half line is the class of `r_J` itself** when that class already lies on the closed sheet
of the fibre's cone: the source's `C_J ⊂ ∂C_I` (§1B, p. 11), `C_J` being the half line of the
positive rational generator `r_J` (`ConicalPlane.basis`). No sign is changed in that case, so the
half line the plane contributes to the fibre of `I` is the image of `r_J` and not of `-r_J`. -/
theorem fibreRay_eq_fibreRayProj_of_nonneg (F : ConicalLine BQ Q) (G : ConicalPlane BQ)
    (h : F.line ≤ G.plane)
    (hC : 0 ≤ (associated (fibreForm Q F.space))
      (rationalPoint (fibreRayProj hBsym F G h)) F.sheet) :
    fibreRay hBsym F G h = fibreRayProj hBsym F G h := by
  rw [fibreRay]
  simp only [hC, ite_true]

omit [Module.Finite ℚ V] in
/-- **A presentation is coherent exactly when the class of `r_J` pairs positively with the sheet**:
the canonical lift `fibreProj` of the class moves the plane's ray by a multiple of `gen`, which the
sheet is orthogonal to, so the two pairings agree. -/
theorem fibreRayProj_sheet_pos_iff (hBsym : BQ.IsSymm) (F : ConicalLine BQ Q)
    (G : ConicalPlane BQ) (h : F.line ≤ G.plane) :
    0 < (associated (fibreForm Q F.space)) (rationalPoint (fibreRayProj hBsym F G h)) F.sheet ↔
      G.IsPositiveAt F h := by
  simp only [ConicalPlane.IsPositiveAt]
  rw [associated_fibreForm, realifyMap_rationalPoint, fibreRayProj_val]

omit [Module.Finite ℚ V] in
/-- A coherent presentation pairs positively: `fibreRayProj_sheet_pos_iff`, forwards. -/
theorem fibreRay_sheet_pos_of_isPositiveAt (hBsym : BQ.IsSymm) (F : ConicalLine BQ Q)
    (G : ConicalPlane BQ) (h : F.line ≤ G.plane) (hpos : G.IsPositiveAt F h) :
    0 < (associated (fibreForm Q F.space)) (rationalPoint (fibreRayProj hBsym F G h)) F.sheet :=
  (fibreRayProj_sheet_pos_iff hBsym F G h).mpr hpos

omit [Module.Finite ℚ V] in
/-- **At a coherent presentation the fibre half line is the class of `r_J` itself**, not of `-r_J`:
`C_J ⊂ ∂C_I` (§1B, p. 11) means that the positive generator, and not its negative, is the boundary
ray of the fibre's cone. -/
theorem fibreRay_eq_fibreRayProj_of_isPositiveAt (hBsym : BQ.IsSymm) (F : ConicalLine BQ Q)
    (G : ConicalPlane BQ) (h : F.line ≤ G.plane) (hpos : G.IsPositiveAt F h) :
    fibreRay hBsym F G h = fibreRayProj hBsym F G h :=
  fibreRay_eq_fibreRayProj_of_nonneg hBsym F G h
    (le_of_lt (fibreRay_sheet_pos_of_isPositiveAt hBsym F G h hpos))

omit [Module.Finite ℚ V] in
/-- The incoherent case, for completeness: a fibre whose sheet pairs negatively with the plane's ray
carries the opposite half line. -/
theorem fibreRay_eq_neg_of_pairing_neg (hBsym : BQ.IsSymm) (F : ConicalLine BQ Q)
    (G : ConicalPlane BQ) (h : F.line ≤ G.plane)
    (hC : (associated (fibreForm Q F.space)) (rationalPoint (fibreRayProj hBsym F G h)) F.sheet
      < 0) :
    fibreRay hBsym F G h = -fibreRayProj hBsym F G h := by
  rw [fibreRay]
  have hnot : ¬ (0 ≤ (associated (fibreForm Q F.space))
      (rationalPoint (fibreRayProj hBsym F G h)) F.sheet) := by linarith
  simp only [hnot, ite_false]

omit [Module.Finite ℚ V] in
/-- The fibre form does not see which of the two generators is taken: it is even. -/
theorem fibreForm_fibreRay_eq (F : ConicalLine BQ Q) (G : ConicalPlane BQ)
    (hF : F.line ≤ G.plane) :
    (fibreForm Q F.space) (rationalPoint (fibreRay hBsym F G hF)) =
      (fibreForm Q F.space) (rationalPoint (fibreRayProj hBsym F G hF)) := by
  rcases fibreRay_eq_or_neg hBsym F G hF with h | h
  · rw [h]
  · rw [h, map_neg, QuadraticMap.map_neg]

omit [Module.Finite ℚ V] in
/-- The half line is not zero when the plane's class is not zero. -/
theorem fibreRay_ne_zero_of (F : ConicalLine BQ Q) (G : ConicalPlane BQ)
    (hF : F.line ≤ G.plane) (h : fibreRayProj hBsym F G hF ≠ 0) :
    fibreRay hBsym F G hF ≠ 0 := by
  rcases fibreRay_eq_or_neg hBsym F G hF with h' | h'
  · rw [h']; exact h
  · rw [h']
    simpa using h

end Fibre

/-! ## Definition 6.1: admissible decompositions of the conical locus -/

section Definition61

variable {BQ : LinearMap.BilinForm ℚ V} {Q : QuadraticForm ℝ (realified V)}

/-- The image in `V(ℝ)` of a member of a conical fibre. -/
noncomputable def memberImage (F : ConicalLine BQ Q)
    (σ : PointedCone ℝ (realified ↥F.space)) : Set (realified V) :=
  (σ.map (realifyMap F.space) : Set (realified V))

/-- The line `I` of a conical fibre inside `V(ℝ)`: the span of its generator. -/
noncomputable def lineSpan (F : ConicalLine BQ Q) : Submodule ℝ (realified V) :=
  Submodule.span ℝ ({rationalPoint F.gen} : Set (realified V))

/-- **the Σ-support space `V_σ` of a member of a conical fibre**, Definition 6.1, p. 28, case (i):
for a member `σ` of the fibre of an isotropic line which is not an isotropic half-line, `V_σ` is
the subspace of `I^⊥` containing `I` corresponding to the complex-linear span of `σ`. -/
noncomputable def vSigma (F : ConicalLine BQ Q)
    (σ : PointedCone ℝ (realified ↥F.space)) : Submodule ℝ (realified V) :=
  lineSpan F ⊔ Submodule.map (realifyMap F.space)
    (Submodule.span ℝ (σ : Set (realified ↥F.space)))

/-- **the Σ-support space `V_σ` of a plane member**, Definition 6.1, p. 28, case (ii): the support
space of the half-line `C_{J,+}` in the fibre of a line `I ≤ J`, computed by
Lemma-Definition 4.5 relative to the decomposition, and carried to `V`. The cones of the
intersection are the members of the decomposition above the half-line that meet the **open**
cone `C_I` of the fibre (`positiveCone.upper (fibreForm Q F.space) F.sheet`), as the source has
them (`.tmp-sources/looijenga-math0201218v2.md:519`); the closed closure `F.closure` puts the
half-line itself in the range and makes the answer its span. Condition (ii) of Definition 6.1 is
precisely that this is independent of `I`. -/
noncomputable def vSigmaPlane {BQ : LinearMap.BilinForm ℚ V} {Q : QuadraticForm ℝ (realified V)}
    (hBsym : BQ.IsSymm) (F : ConicalLine BQ Q)
    (S : Set (PointedCone ℝ (realified ↥F.space)))
    (G : ConicalPlane BQ) (_h : F.line ≤ G.plane) : Submodule ℝ (realified V) :=
  lineSpan F ⊔ (sigmaSupportSpace (positiveCone.upper (fibreForm Q F.space) F.sheet) S
    (PointedCone.hull ℝ ({rationalPoint (fibreRay hBsym F G _h)} :
      Set (realified ↥F.space)))).map (realifyMap F.space)

/-- The isotropic center `I(σ) = V_σ ∩ V_σ^⊥` of a member of a conical fibre (Definition 6.1,
p. 28). -/
noncomputable def isotropicCenter (Q : QuadraticForm ℝ (realified V))
    (Vσ : Submodule ℝ (realified V)) : Submodule ℝ (realified V) :=
  Vσ ⊓ LinearMap.BilinForm.orthogonal (associated Q) Vσ

/-- `Γ`-invariance of a conical decomposition (Definition 6.1, p. 28, the hypothesis on the
collection `Σ`): every isometry of `V` in `Γ` carries the *members* of one conical fibre onto the
members of a fibre over the image line, and the images are taken under the isometry — `γ` moves the
fibre of `I` to the fibre of `γI` (§1B, p. 11).

Stated at the level of the images in `V(ℝ)`, in both directions: the collection of the images of
the members of the fibre of `I` is the collection of the images of the members of the fibre of `γI`.
A statement about the union of those images instead would be implied by any family of members
covering `C_{I,+}` and would not say that the *cones* are permuted. -/
def IsGammaInvariantLocus (BQ : LinearMap.BilinForm ℚ V) (Q : QuadraticForm ℝ (realified V))
    (Γ : Set (V ≃ₗ[ℚ] V))
    (locus : ∀ F : ConicalLine BQ Q, Set (PointedCone ℝ (realified ↥F.space))) : Prop :=
  ∀ g ∈ Γ, (∀ x y : V, BQ (g x) (g y) = BQ x y) → ∀ F : ConicalLine BQ Q,
    ∃ F' : ConicalLine BQ Q, F'.line = Submodule.map (g : V →ₗ[ℚ] V) F.line ∧
      (∀ σ ∈ locus F, ∃ σ' ∈ locus F',
        memberImage F' σ' = (realifiedEquiv g) '' (memberImage F σ)) ∧
      (∀ σ' ∈ locus F', ∃ σ ∈ locus F,
        memberImage F' σ' = (realifiedEquiv g) '' (memberImage F σ))

/-- **Looijenga, Definition 6.1, p. 28** (text line 769): an admissible decomposition of the conical
locus is a `Γ`-invariant collection `Σ` of cones in the faces of the conical locus such that

(i) for every `ℚ`-isotropic line `I`, the members of `Σ` contained in `C_{I,+}` define a locally
rational decomposition of `C_{I,+}`, and
(ii) for a `ℚ`-isotropic plane `J` and any two `ℚ`-isotropic lines `I, I' ⊆ J`, the support spaces
of `C_{J,+}` in `I^⊥/I` and in `I'^⊥/I'` relative to the decompositions `Σ|C_{I,+}` and
`Σ|C_{I',+}` are the same subspace of `V`. -/
structure IsAdmissibleDecomposition (BQ : LinearMap.BilinForm ℚ V)
    (Q : QuadraticForm ℝ (realified V)) (Γ : Set (V ≃ₗ[ℚ] V))
    (locus : ∀ F : ConicalLine BQ Q, Set (PointedCone ℝ (realified ↥F.space))) : Prop where
  /-- `Σ` is `Γ`-invariant. -/
  gammaInvariant : IsGammaInvariantLocus BQ Q Γ locus
  /-- Definition 6.1 (i). -/
  condition_i : ∀ F : ConicalLine BQ Q,
    IsLocallyRationalDecomposition F.closure (locus F)
  /-- Definition 6.1 (ii). -/
  condition_ii : ∀ (hBsym : BQ.IsSymm) (F F' : ConicalLine BQ Q) (G : ConicalPlane BQ)
    (h : F.line ≤ G.plane) (h' : F'.line ≤ G.plane),
    vSigmaPlane hBsym F (locus F) G h = vSigmaPlane hBsym F' (locus F') G h'

omit [Module.Finite ℚ V] in
/-- **Definition 6.1 (ii) from the pointwise identity `V_σ = J_Σ`**: condition (ii) asks that the
support space of a plane's half line be the same for every `ℚ`-isotropic line `I ⊆ J`; if that
support space is a subspace `J_H` depending only on the plane, the condition is transitivity.

This is the assembly step of Example 6.4, p. 29: the source computes `J_{Σ(ℋ)}` as "the common
intersection of `J^⊥` and the hyperplanes `H ∈ ℋ` containing `J`", a subspace attached to `J` alone,
and condition (ii) then follows for `Σ(ℋ)`. The identity is
`SemifanArrangement.vSigmaPlane_semifanArrangement_eq_JH`: `J_{Σ(ℋ)} ⊆ J_ℋ` is
`SemifanArrangement.supportSpace_halfLine_le_ker`, and `J_ℋ ⊆ J_{Σ(ℋ)}` is
`SemifanArrangement.fibreJH_le_span_of_member` together with Lemma-Definition 4.5. -/
theorem isAdmissibleDecomposition_of_vSigmaPlane_eq
    {BQ : LinearMap.BilinForm ℚ V} {Q : QuadraticForm ℝ (realified V)}
    {Γ : Set (V ≃ₗ[ℚ] V)}
    {locus : ∀ F : ConicalLine BQ Q, Set (PointedCone ℝ (realified ↥F.space))}
    (hgamma : IsGammaInvariantLocus BQ Q Γ locus)
    (hcond_i : ∀ F : ConicalLine BQ Q, IsLocallyRationalDecomposition F.closure (locus F))
    (J : ConicalPlane BQ → Submodule ℝ (realified V))
    (hJ : ∀ (hBsym : BQ.IsSymm) (F : ConicalLine BQ Q) (G : ConicalPlane BQ)
      (h : F.line ≤ G.plane), vSigmaPlane hBsym F (locus F) G h = J G) :
    IsAdmissibleDecomposition BQ Q Γ locus :=
  { gammaInvariant := hgamma
    condition_i := hcond_i
    condition_ii := fun hBsym F F' G h h' => by
      rw [hJ hBsym F G h, hJ hBsym F' G h'] }

end Definition61

/-! ## Lemma 6.6: a refinement shrinks the Σ-support space -/

section Lemma66

variable {BQ : LinearMap.BilinForm ℚ V} {Q : QuadraticForm ℝ (realified V)}

omit [Module.Finite ℚ V] in
/-- **Looijenga, Lemma 6.6, p. 30** (text line 821), the inclusion `V_σ ⊂ V_{σ'}`: for members
`σ ⊂ σ'` of one conical fibre the Σ-support spaces are nested. The source states it for `σ'` the
smallest member of a refining decomposition `Σ'` containing `σ`; the content is the monotonicity of
the support space in the member, which is what this states. -/
theorem vSigma_mono {F : ConicalLine BQ Q}
    {σ σ' : PointedCone ℝ (realified ↥F.space)} (h : σ ≤ σ') :
    vSigma F σ ≤ vSigma F σ' := by
  refine sup_le_sup_left ?_ _
  exact Submodule.map_mono (Submodule.span_mono (SetLike.coe_subset_coe.2 h))

end Lemma66

end LeanCategories.Lattices.Valued
