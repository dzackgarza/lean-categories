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
  `Semifan.bailyBorel_isAdmissibleDecomposition`, and Example 6.4 is still owed.
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

/-- A `ℚ`-isotropic plane of the conical locus with the choice of its half-line `C_{J,+}`
(Definition 2.1, p. 10; the cone `C_J` is a half-line in `Λ²J(ℝ)`). `ray` is a `ℚ`-rational
generator of `J/I` for every isotropic line `I ≤ J`. -/
structure ConicalPlane (BQ : LinearMap.BilinForm ℚ V) where
  /-- the isotropic plane -/
  plane : Submodule ℚ V
  /-- it is totally isotropic -/
  isotropic : ∀ x ∈ plane, ∀ y ∈ plane, BQ x y = 0
  /-- it is a plane -/
  two_dim : Module.finrank ℚ ↥plane = 2
  /-- a `ℚ`-rational direction of the half-line -/
  ray : V
  ray_mem : ray ∈ plane
  ray_ne : ray ≠ 0
  /-- the ray generates the plane over each of its isotropic lines -/
  ray_not_mem_of_line : ∀ (I : Submodule ℚ V), I ≤ plane → Module.finrank ℚ ↥I = 1 → ray ∉ I

namespace ConicalPlane

variable {BQ : LinearMap.BilinForm ℚ V} (G : ConicalPlane BQ)

omit [Module.Finite ℚ V] in
theorem ray_iso : BQ G.ray G.ray = 0 :=
  G.isotropic G.ray G.ray_mem G.ray G.ray_mem

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

/-- The class of a `ℚ`-isotropic plane's ray in the conical fibre of one of its lines, *without* the
choice of half line: Looijenga §1B, p. 11 (text line 265), "`Λ²J` can be regarded as a line in
`I ⊗ I^⊥/I`". -/
noncomputable def fibreRayProj (F : ConicalLine BQ Q) (G : ConicalPlane BQ) : ↥F.space :=
  fibreProj hBsym F G.ray

/-- **The half line `C_{J,+}` of a `ℚ`-isotropic plane in the fibre of one of its lines**: the class
of the plane's ray, or its opposite, whichever lies on the **closed sheet** of the fibre's cone —
the isotropic ray `r` of the fibre with `0 ≤ r · t` at the fibre's positive vector `t`.

Looijenga §1B, p. 11 (text line 267): "`Λ²J` can be regarded as a line in `I ⊗ I^⊥/I` and via this
inclusion, `C_J` is contained in the boundary of `C_I`". The fibre `ConicalLine` carries its sheet
`C_I` as data, and of the two half lines of the isotropic line `J/I` exactly one is a boundary ray
of the closed sheet of `C_I` (`0 < r · t` for a positive `t` in signature `(1, n-1)`, so the two
have opposite signs at `t`); this is that half line. It is the member `σ = C_{J,+}` of Definition
6.1 (ii), the one whose `Σ`-support space the definition names. -/
noncomputable def fibreRay (F : ConicalLine BQ Q) (G : ConicalPlane BQ) : ↥F.space :=
  if 0 ≤ (associated (fibreForm Q F.space)) (rationalPoint (fibreRayProj hBsym F G)) F.sheet
  then fibreRayProj hBsym F G else -fibreRayProj hBsym F G

omit [Module.Finite ℚ V] in
/-- The half line is one of the two generators of the plane's class in the fibre. -/
theorem fibreRay_eq_or_neg (F : ConicalLine BQ Q) (G : ConicalPlane BQ) :
    fibreRay hBsym F G = fibreRayProj hBsym F G ∨
      fibreRay hBsym F G = -fibreRayProj hBsym F G := by
  rw [fibreRay]
  split_ifs with h
  · exact Or.inl rfl
  · exact Or.inr rfl

omit [Module.Finite ℚ V] in
/-- **The half line lies on the closed sheet of the fibre's cone**: `0 ≤ r · t`. -/
theorem fibreRay_sheet_nonneg (F : ConicalLine BQ Q) (G : ConicalPlane BQ) :
    0 ≤ (associated (fibreForm Q F.space)) (rationalPoint (fibreRay hBsym F G)) F.sheet := by
  rw [fibreRay]
  split_ifs with h
  · exact h
  · rw [map_neg, LinearMap.BilinForm.neg_left]
    linarith [lt_of_not_ge h]

omit [Module.Finite ℚ V] in
/-- The fibre form does not see which of the two generators is taken: it is even. -/
theorem fibreForm_fibreRay_eq (F : ConicalLine BQ Q) (G : ConicalPlane BQ) :
    (fibreForm Q F.space) (rationalPoint (fibreRay hBsym F G)) =
      (fibreForm Q F.space) (rationalPoint (fibreRayProj hBsym F G)) := by
  rcases fibreRay_eq_or_neg hBsym F G with h | h
  · rw [h]
  · rw [h, map_neg, QuadraticMap.map_neg]

omit [Module.Finite ℚ V] in
/-- The half line is not zero when the plane's class is not zero. -/
theorem fibreRay_ne_zero_of (F : ConicalLine BQ Q) (G : ConicalPlane BQ)
    (h : fibreRayProj hBsym F G ≠ 0) : fibreRay hBsym F G ≠ 0 := by
  rcases fibreRay_eq_or_neg hBsym F G with h' | h'
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
    (PointedCone.hull ℝ ({rationalPoint (fibreRay hBsym F G)} :
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
and condition (ii) then follows for `Σ(ℋ)` — what remains for that example is the identity itself
(`J_{Σ(ℋ)} ⊆ J_ℋ` is `SemifanArrangement.supportSpace_halfLine_le_ker`, and `J_ℋ ⊆ J_{Σ(ℋ)}` is
`SemifanArrangement.mem_supportSpace_halfLine_of_supportForms_span`). -/
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
