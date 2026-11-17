/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Lattices.Valued.EvenGluingGraph
public import Mathlib.LinearAlgebra.TensorProduct.Prod

/-!
# The discriminant form of an orthogonal sum `S ⊥ K` is the orthogonal sum of the discriminant
forms of the factors: the discriminant group `A_(S ⊥ K) = (S ⊥ K)^♯/(S ⊥ K)` is the product
`A_S × A_K`, and the quadratic refinement is `q_S ⊕ q_K` under that identification. This file
builds the two coordinates of the rational span of the sum and proves the first layer of that
statement.

The rational span of an orthogonal sum is `Frac(R) ⊗ (L.carrier × M.carrier)`, and its two
coordinates (`orthogonalSumSpanFst`, `orthogonalSumSpanSnd`) are defined here on the carrier of
the sum itself, so that every computation stays inside a single `TensorProduct` and no change of
module instance occurs. The two lemmas that matter later are

* `rationalizedForm_orthogonalSum_fst_snd`: the rationalized form of the sum is the sum of the
  two forms on the two coordinates (`JordanRecursion.rationalizedForm_orthogonalSum` is the same
  identity read against a lattice vector);
* `mem_metricDual_orthogonalSum_iff`: the metric dual of the sum is the product of the metric
  duals of the factors.

From those, on representatives: `metricDualToValueDual_orthogonalSum_fst`/`_snd` (the functional
of a metric-dual vector restricted to a coordinate is the functional of that coordinate),
`evenDiscriminantRestrictionMap_metricDualToDiscriminant` and
`evenDiscriminantDefectMap_metricDualToDiscriminant` (the coordinate restrictions of a
discriminant class are the classes of the two coordinates), and `isEven_orthogonalSum` from
`ScaleAndEvenness`.

The transport of the quadratic refinement is proved here for classes with a chosen metric-dual
representative: `evenDiscriminantQuadraticMap_orthogonalSum_metricDual` states
`q_(S ⊥ K)(x) = q_S(x₁) + q_K(x₂)` for `x : (S ⊥ K)^♯`, which is the form in which the classes
of an overlattice of `S ⊥ K` arise. What is not proved here is the same identity for an
arbitrary class `z : A_(S ⊥ K)`, and with it `isFractionFieldPerfect_orthogonalSum` and
bijectivity of `evenDiscriminantDefectMap` (the defect-quotient equivalence
`A_(S ⊥ K) ≃ A_S × A_K`). The obstruction is recorded in `COMPLAINTS.md`: the statement of the
general form elaborates in about a second, but its proof diverges in `whnf` as soon as a
surjectivity witness for `metricDualToDiscriminant` (or `rieszToMetricDual`) is substituted into
the goal — a `maxHeartbeats` timeout at 800000, 1000000 and 4000000 heartbeats.

## Port provenance

The splitting of the rational span and of the form follows `TauCetiProject/TauCeti` (Apache 2.0,
© The Tau Ceti contributors), `TauCeti/LinearAlgebra/IntegralLattice/Overlattice/Graph.lean`
(`discriminantGroupOrthogonalSumEquiv`, `discriminantQuadraticIsometryOrthogonalSum`,
`mem_dualCarrier_orthogonalSum_iff`) and its `Overlattice/Dual.lean`
(`mem_dualCarrier_orthogonalSum_iff`, `dual_orthogonalSumIntermediateCarrier`). TauCeti carries a
lattice as a submodule of a rational space `V` fixed in advance, so for it the orthogonal sum's
ambient space is literally `V × W` and the splitting of the dual carriers is a one-line
calculation; here the ambient space is `Frac(R) ⊗ (L.carrier × M.carrier)`, and the product
decomposition `TensorProduct.prodRight` is what has to be inserted. The Mathlib lemma used for
that is `TensorProduct.prodRight` (`LinearAlgebra/TensorProduct/Prod.lean`); the quadratic
refinement's transport is not in Mathlib and is proved here.

## LC-09 search record

Queries over the formalization corpus (`scripts/formalization_corpus.py search`):
`discriminantGroupOrthogonalSumEquiv` (TauCeti `Overlattice/Graph.lean`, the hit ported above),
`graph of an isometry orthogonal sum discriminant` (TauCeti `Overlattice/Graph.lean`,
`Overlattice/Dual.lean`), `overlattice discriminant form orthogonal complement quotient`
(TauCeti `Overlattice/Dual.lean`), `QuadraticMap.prod IsometryEquiv neg` (Mathlib
`LinearAlgebra/QuadraticForm/Prod.lean` — the product form itself, used directly),
`isotropic subgroup overlattice discriminant q|H^perp/H` (TauCeti roadmap import list only).
Mathlib's `TensorProduct.prodRight` is used directly; no statement that the discriminant form of
an orthogonal sum is the orthogonal sum of the discriminant forms exists upstream.
-/

@[expose] public section

open LeanCategories.Modules.Bilinear.Valued
open LeanCategories.Modules.Quadratic.Valued

namespace LeanCategories.Lattices.Valued

universe u

variable {R : Type u} [CommRing R] [IsDomain R]

variable (L M : IntegralLatticeCat R)

/-! ## The two coordinate projections of the rational span of an orthogonal sum

The rational span of the orthogonal sum is `Frac(R) ⊗ (L.carrier × M.carrier)`. Its two
coordinates are defined here as the `Frac(R)`-linear maps induced by the two product
projections; both are stated on the carrier of the sum itself, so that every later
computation stays in one `TensorProduct`, with no change of instance. -/

/-- The first coordinate of the rational span of an orthogonal sum. -/
noncomputable def orthogonalSumSpanFst :
    RationalSpan R (orthogonalSum L M) →ₗ[FractionRing R] RationalSpan R L :=
  TensorProduct.AlgebraTensorModule.lift (A := FractionRing R)
    (LinearMap.mk₂ R
      (fun (a : FractionRing R) (z : ↥(orthogonalSum L M).obj.carrier) =>
        a • toRationalSpan R L z.1)
      (fun a a' z => add_smul a a' _)
      (fun c a z => smul_assoc c a _)
      (fun a z z' => by
        rw [show (z + z').1 = z.1 + z'.1 from rfl, map_add, smul_add])
      (fun (c : R) (a : FractionRing R) (z : ↥(orthogonalSum L M).obj.carrier) => by
        rw [show (c • z).1 = c • z.1 from rfl, map_smul, smul_comm]))

/-- The second coordinate of the rational span of an orthogonal sum. -/
noncomputable def orthogonalSumSpanSnd :
    RationalSpan R (orthogonalSum L M) →ₗ[FractionRing R] RationalSpan R M :=
  TensorProduct.AlgebraTensorModule.lift (A := FractionRing R)
    (LinearMap.mk₂ R
      (fun (a : FractionRing R) (z : ↥(orthogonalSum L M).obj.carrier) =>
        a • toRationalSpan R M z.2)
      (fun a a' z => add_smul a a' _)
      (fun c a z => smul_assoc c a _)
      (fun a z z' => by
        rw [show (z + z').2 = z.2 + z'.2 from rfl, map_add, smul_add])
      (fun (c : R) (a : FractionRing R) (z : ↥(orthogonalSum L M).obj.carrier) => by
        rw [show (c • z).2 = c • z.2 from rfl, map_smul, smul_comm]))

variable {L M}

omit [IsDomain R] in
@[simp]
theorem orthogonalSumSpanFst_tmul (a : FractionRing R)
    (z : ↥(orthogonalSum L M).obj.carrier) :
    orthogonalSumSpanFst L M (a ⊗ₜ[R] z) = a • toRationalSpan R L z.1 :=
  rfl

omit [IsDomain R] in
@[simp]
theorem orthogonalSumSpanSnd_tmul (a : FractionRing R)
    (z : ↥(orthogonalSum L M).obj.carrier) :
    orthogonalSumSpanSnd L M (a ⊗ₜ[R] z) = a • toRationalSpan R M z.2 :=
  rfl

@[simp]
theorem orthogonalSumSpanFst_toRationalSpan (s : L.obj.carrier) (k : M.obj.carrier) :
    orthogonalSumSpanFst L M
        (toRationalSpan R (orthogonalSum L M) ((s, k) : ↥(orthogonalSum L M).obj.carrier)) =
      toRationalSpan R L s := by
  show (1 : FractionRing R) • toRationalSpan R L ((s, k) : ↥(orthogonalSum L M).obj.carrier).1 =
    toRationalSpan R L s
  rw [one_smul]

@[simp]
theorem orthogonalSumSpanSnd_toRationalSpan (s : L.obj.carrier) (k : M.obj.carrier) :
    orthogonalSumSpanSnd L M
        (toRationalSpan R (orthogonalSum L M) ((s, k) : ↥(orthogonalSum L M).obj.carrier)) =
      toRationalSpan R M k := by
  show (1 : FractionRing R) • toRationalSpan R M ((s, k) : ↥(orthogonalSum L M).obj.carrier).2 =
    toRationalSpan R M k
  rw [one_smul]

/-- The pairing of an orthogonal sum, on the carrier of the sum: the bridge between
`orthogonalSum_pairing` (stated on the product type) and the carrier of the orthogonal sum. -/
theorem orthogonalSum_pairing_carrier (z z' : ↥(orthogonalSum L M).obj.carrier) :
    (orthogonalSum L M).obj.pairing z z' =
      L.obj.pairing z.1 z'.1 + M.obj.pairing z.2 z'.2 :=
  orthogonalSum_pairing L M z z'

/-- The rationalized form of a lattice on lattice vectors.
`AmbientSchreierImage.rationalizedForm_toRationalSpan` states the same identity for an
arbitrary lattice; it is restated here so that this module does not import the descent layer. -/
theorem rationalizedForm_toRationalSpan_pairing (x x' : L.obj.carrier) :
    rationalizedForm R L (toRationalSpan R L x) (toRationalSpan R L x') =
      algebraMap R (FractionRing R) (L.obj.pairing x x') :=
  rationalizedForm_toMetricDual R L x x'

/-- The rationalized form on `Frac(R)`-multiples of lattice vectors. -/
theorem rationalizedForm_smul_toRationalSpan (a b : FractionRing R)
    (x x' : L.obj.carrier) :
    rationalizedForm R L (a • toRationalSpan R L x) (b • toRationalSpan R L x') =
      (a * b) * algebraMap R (FractionRing R) (L.obj.pairing x x') := by
  simp only [LinearMap.map_smul, LinearMap.smul_apply, smul_eq_mul,
    rationalizedForm_toRationalSpan_pairing]
  ring

/-- **The rationalized form of an orthogonal sum is the sum of the two forms**, along the two
coordinates of the rational span. `JordanRecursion.rationalizedForm_orthogonalSum` is the same
identity read against a single lattice vector, through the `R`-linear product decomposition
`rationalSpanProdEquiv`; this version is stated for two arbitrary elements of the rational span,
which is what the discriminant computations below need. -/
theorem rationalizedForm_orthogonalSum_fst_snd (u v : RationalSpan R (orthogonalSum L M)) :
    rationalizedForm R (orthogonalSum L M) u v =
      rationalizedForm R L (orthogonalSumSpanFst L M u) (orthogonalSumSpanFst L M v) +
        rationalizedForm R M (orthogonalSumSpanSnd L M u) (orthogonalSumSpanSnd L M v) := by
  induction u using TensorProduct.inductionOn with
  | tmul a z =>
    induction v using TensorProduct.inductionOn with
    | tmul b z' =>
      rw [rationalizedForm_tmul, orthogonalSumSpanFst_tmul, orthogonalSumSpanSnd_tmul,
        orthogonalSumSpanFst_tmul, orthogonalSumSpanSnd_tmul,
        rationalizedForm_smul_toRationalSpan (L := L),
        rationalizedForm_smul_toRationalSpan (L := M),
        orthogonalSum_pairing_carrier, map_add, mul_add]
    | add v₁ v₂ h₁ h₂ =>
      rw [LinearMap.map_add, h₁, h₂]
      simp only [LinearMap.map_add, LinearMap.add_apply, Prod.fst_add, Prod.snd_add]
      abel
  | add u₁ u₂ h₁ h₂ =>
    rw [LinearMap.map_add, LinearMap.add_apply, h₁, h₂]
    simp only [LinearMap.map_add, LinearMap.add_apply, Prod.fst_add, Prod.snd_add]
    abel

/-- The metric dual of an orthogonal sum splits componentwise. -/
theorem mem_metricDual_orthogonalSum_iff (x : RationalSpan R (orthogonalSum L M)) :
    x ∈ metricDual R (orthogonalSum L M) ↔
      orthogonalSumSpanFst L M x ∈ metricDual R L ∧
        orthogonalSumSpanSnd L M x ∈ metricDual R M := by
  constructor
  · intro h
    have hx : ∀ y ∈ integralImage R (orthogonalSum L M),
        rationalizedForm R (orthogonalSum L M) x y ∈ (1 : Submodule R (FractionRing R)) :=
      fun y hy =>
        (LinearMap.BilinForm.mem_dualSubmodule (rationalizedForm R (orthogonalSum L M))).mp
          h y hy
    have hleft : orthogonalSumSpanFst L M x ∈ metricDual R L := by
      rw [metricDual, LinearMap.BilinForm.mem_dualSubmodule]
      rintro _ ⟨s, rfl⟩
      have hy := hx _ (LinearMap.mem_range_self (toRationalSpan R (orthogonalSum L M))
        ((s, 0) : ↥(orthogonalSum L M).obj.carrier))
      rw [rationalizedForm_orthogonalSum_fst_snd, orthogonalSumSpanFst_toRationalSpan,
        orthogonalSumSpanSnd_toRationalSpan] at hy
      simpa using hy
    refine ⟨hleft, ?_⟩
    rw [metricDual, LinearMap.BilinForm.mem_dualSubmodule]
    rintro _ ⟨k, rfl⟩
    have hy := hx _ (LinearMap.mem_range_self (toRationalSpan R (orthogonalSum L M))
      ((0, k) : ↥(orthogonalSum L M).obj.carrier))
    rw [rationalizedForm_orthogonalSum_fst_snd, orthogonalSumSpanFst_toRationalSpan,
      orthogonalSumSpanSnd_toRationalSpan] at hy
    simpa using hy
  · rintro ⟨h₁, h₂⟩
    have hleft : ∀ s : L.obj.carrier,
        rationalizedForm R L (orthogonalSumSpanFst L M x) (toRationalSpan R L s) ∈
          (1 : Submodule R (FractionRing R)) :=
      fun s => (LinearMap.BilinForm.mem_dualSubmodule (rationalizedForm R L)).mp h₁
        (toRationalSpan R L s) (LinearMap.mem_range_self (toRationalSpan R L) s)
    have hright : ∀ k : M.obj.carrier,
        rationalizedForm R M (orthogonalSumSpanSnd L M x) (toRationalSpan R M k) ∈
          (1 : Submodule R (FractionRing R)) :=
      fun k => (LinearMap.BilinForm.mem_dualSubmodule (rationalizedForm R M)).mp h₂
        (toRationalSpan R M k) (LinearMap.mem_range_self (toRationalSpan R M) k)
    rw [metricDual, LinearMap.BilinForm.mem_dualSubmodule]
    rintro y ⟨z, rfl⟩
    obtain ⟨s, k⟩ := z
    rw [rationalizedForm_orthogonalSum_fst_snd, orthogonalSumSpanFst_toRationalSpan,
      orthogonalSumSpanSnd_toRationalSpan]
    exact add_mem (hleft s) (hright k)

/-! ## The value dual, the defect and the quadratic refinement -/

/-- A metric-dual vector of an orthogonal sum is integral against a first-factor vector exactly
when its first coordinate is integral against that vector. -/
theorem metricDualToValueDual_orthogonalSum_fst (x : metricDual R (orthogonalSum L M))
    (hx : orthogonalSumSpanFst L M x ∈ metricDual R L) (s : L.obj.carrier) :
    metricDualToValueDual R (orthogonalSum L M) x
        ((s, 0) : ↥(orthogonalSum L M).obj.carrier) =
      metricDualToValueDual R L ⟨orthogonalSumSpanFst L M x, hx⟩ s := by
  apply IsFractionRing.injective R (FractionRing R)
  rw [metricDualToValueDual_apply R (v := x) ((s, 0) : ↥(orthogonalSum L M).obj.carrier),
    metricDualToValueDual_apply R (v := (⟨orthogonalSumSpanFst L M x, hx⟩ : metricDual R L)) s]
  rw [rationalizedForm_orthogonalSum_fst_snd, orthogonalSumSpanFst_toRationalSpan,
    orthogonalSumSpanSnd_toRationalSpan]
  simp

/-- A metric-dual vector of an orthogonal sum is integral against a second-factor vector exactly
when its second coordinate is integral against that vector. -/
theorem metricDualToValueDual_orthogonalSum_snd (x : metricDual R (orthogonalSum L M))
    (hx : orthogonalSumSpanSnd L M x ∈ metricDual R M) (k : M.obj.carrier) :
    metricDualToValueDual R (orthogonalSum L M) x
        ((0, k) : ↥(orthogonalSum L M).obj.carrier) =
      metricDualToValueDual R M ⟨orthogonalSumSpanSnd L M x, hx⟩ k := by
  apply IsFractionRing.injective R (FractionRing R)
  rw [metricDualToValueDual_apply R (v := x) ((0, k) : ↥(orthogonalSum L M).obj.carrier),
    metricDualToValueDual_apply R (v := (⟨orthogonalSumSpanSnd L M x, hx⟩ : metricDual R M)) k]
  rw [rationalizedForm_orthogonalSum_fst_snd, orthogonalSumSpanFst_toRationalSpan,
    orthogonalSumSpanSnd_toRationalSpan]
  simp

/-- The two coordinate restrictions of a discriminant class of an orthogonal sum are the
discriminant classes of the two coordinates of any metric-dual representative. -/
theorem evenDiscriminantRestrictionMap_metricDualToDiscriminant
    (x : metricDual R (orthogonalSum L M))
    (hx : orthogonalSumSpanFst L M x ∈ metricDual R L)
    (hx' : orthogonalSumSpanSnd L M x ∈ metricDual R M) :
    evenDiscriminantRestrictionMap L M (metricDualToValueDual R (orthogonalSum L M) x) =
      (metricDualToDiscriminant R L ⟨orthogonalSumSpanFst L M x, hx⟩,
        metricDualToDiscriminant R M ⟨orthogonalSumSpanSnd L M x, hx'⟩) := by
  have hfst : evenDiscriminantFstRestriction L M
        (metricDualToValueDual R (orthogonalSum L M) x) =
      metricDualToValueDual R L ⟨orthogonalSumSpanFst L M x, hx⟩ := by
    ext s
    exact metricDualToValueDual_orthogonalSum_fst x hx s
  have hsnd : evenDiscriminantSndRestriction L M
        (metricDualToValueDual R (orthogonalSum L M) x) =
      metricDualToValueDual R M ⟨orthogonalSumSpanSnd L M x, hx'⟩ := by
    ext k
    exact metricDualToValueDual_orthogonalSum_snd x hx' k
  change (L.obj.defectProjection
      (evenDiscriminantFstRestriction L M (metricDualToValueDual R (orthogonalSum L M) x)),
    M.obj.defectProjection
      (evenDiscriminantSndRestriction L M (metricDualToValueDual R (orthogonalSum L M) x))) = _
  rw [hfst, hsnd]
  rfl

/-- The defect splitting of an orthogonal sum, on a metric-dual representative: the two
coordinates of a discriminant class are the discriminant classes of the two coordinates. -/
theorem evenDiscriminantDefectMap_metricDualToDiscriminant
    (x : metricDual R (orthogonalSum L M))
    (hx : orthogonalSumSpanFst L M x ∈ metricDual R L)
    (hx' : orthogonalSumSpanSnd L M x ∈ metricDual R M) :
    evenDiscriminantDefectMap L M (metricDualToDiscriminant R (orthogonalSum L M) x) =
      (metricDualToDiscriminant R L ⟨orthogonalSumSpanFst L M x, hx⟩,
        metricDualToDiscriminant R M ⟨orthogonalSumSpanSnd L M x, hx'⟩) := by
  rw [metricDualToDiscriminant, LinearMap.comp_apply, evenDiscriminantDefectMap_mk]
  exact evenDiscriminantRestrictionMap_metricDualToDiscriminant x hx hx'

set_option maxHeartbeats 800000 in
/-- **The quadratic refinement of an orthogonal sum is the sum of the two refinements** on a class
with a chosen metric-dual representative. This is the form in which the discriminant classes of an
overlattice of `S ⊥ K` arise: an element of the rational span, not an arbitrary quotient class. -/
theorem evenDiscriminantQuadraticMap_orthogonalSum_metricDual
    (hL : IsFractionFieldPerfect R L) (hM : IsFractionFieldPerfect R M)
    (hLM : IsFractionFieldPerfect R (orthogonalSum L M))
    (hEvenL : IsEven L) (hEvenM : IsEven M) (hEvenLM : IsEven (orthogonalSum L M))
    (x : metricDual R (orthogonalSum L M))
    (hx : orthogonalSumSpanFst L M x ∈ metricDual R L)
    (hx' : orthogonalSumSpanSnd L M x ∈ metricDual R M) :
    evenDiscriminantQuadraticMap (L := orthogonalSum L M) hLM hEvenLM
        (metricDualToDiscriminant R (orthogonalSum L M) x) =
      evenDiscriminantQuadraticMap (L := L) hL hEvenL
          (metricDualToDiscriminant R L ⟨orthogonalSumSpanFst L M x, hx⟩) +
        evenDiscriminantQuadraticMap (L := M) hM hEvenM
          (metricDualToDiscriminant R M ⟨orthogonalSumSpanSnd L M x, hx'⟩) := by
  rw [evenDiscriminantQuadraticMap_metricDualToDiscriminant (L := orthogonalSum L M) hLM hEvenLM,
    evenDiscriminantQuadraticMap_metricDualToDiscriminant (L := L) hL hEvenL,
    evenDiscriminantQuadraticMap_metricDualToDiscriminant (L := M) hM hEvenM,
    rationalizedForm_orthogonalSum_fst_snd, map_add]

end LeanCategories.Lattices.Valued
