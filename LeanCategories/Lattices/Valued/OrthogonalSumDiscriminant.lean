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

The transport of the quadratic refinement is proved twice, in the two forms its consumers need.
`evenDiscriminantQuadraticMap_orthogonalSum_metricDual` states
`q_(S ⊥ K)(x) = q_S(x₁) + q_K(x₂)` for `x : (S ⊥ K)^♯`, a class with a chosen metric-dual
representative. `evenDiscriminantQuadraticMap_orthogonalSum` states the same identity for an
arbitrary class `z : A_(S ⊥ K)` along the defect splitting, which is the form the gluing graph
`Γ_γ ⊆ A_S ⊕ A_K` needs: a graph is a subgroup of `A_S ⊕ A_K`, not of `(S ⊥ K)^♯`.

The general form was long blocked, and both the resolution and the cause of the block are worth
recording. The identity is proved through `rieszEmbedding` alone: the two coordinates of a Riesz
vector are the Riesz vectors of the two coordinate restrictions
(`orthogonalSumSpanFst_rieszEmbedding`, `orthogonalSumSpanSnd_rieszEmbedding`), so it reduces to
`rationalizedForm_orthogonalSum_fst_snd` at a single element of the rational span, and the class is
handled by `Submodule.Quotient.induction_on` on its representative. No `metricDual` coercion, no
`LinearEquiv` supplied by a surjectivity witness and no `mem_metricDual_orthogonalSum_iff` occurs
in the proofs below, and that is the whole of why they elaborate.

The earlier route went through `metricDualToDiscriminant` and a surjectivity witness. Its block was
not the substitution: `obtain ⟨x, rfl⟩ := metricDualToDiscriminant_surjective …` is cheap, and so is
the same witness at a single lattice. It was `isDefEq` between two presentations of
`metricDual R (S ⊥ K)` when the lattice arguments of `mem_metricDual_orthogonalSum_iff` are left to
unification — `metricDual` and `rationalizedForm` (`Lattices/Valued/MetricDual.lean:34`,
`Rationalization.lean:54`) are both `abbrev`s, so `whnf` runs through them into
`orthogonalSum`'s `bilinMap` at unsolved lattice metavariables, and it does not terminate within
4000000 heartbeats; naming the lattices (`(L := L) (M := M)`) makes it instant. `COMPLAINTS.md`
carries the minimal divergent goal state and the diagnosis.

`isFractionFieldPerfect_orthogonalSum` and `rationalizedForm_orthogonalSum_prodEquiv` supply the
perfection hypothesis at the sum, in the joint product coordinates of the rational span.

## Port provenance

The splitting of the rational span and of the form follows `TauCetiProject/TauCeti` (Apache 2.0,
© The Tau Ceti contributors), whose `LinearAlgebra/IntegralLattice/Discriminant/Operations.lean`
carries `mem_dualCarrier_orthogonalSum`, `dualCarrier_orthogonalSum`,
`orthogonalSumDualCarrierEquiv`, `discriminantGroupOrthogonalSumEquiv` and the quadratic isometry
`discriminantQuadraticIsometryOrthogonalSum` — the transport proved below is the port of that
isometry's `map_app'`, which is consumed in `Overlattice/Graph.lean` (`glueAlongDiscriminant` and
`exists_eq_glueAlongDiscriminant`, Nikulin Prop. 1.6.1); `Overlattice/Dual.lean` supplies
`dual_orthogonalSumIntermediateCarrier`. TauCeti carries a lattice as a submodule of a rational
space `V` fixed in advance, so for it the orthogonal sum's ambient space is literally `V × W`, the
splitting of the dual carriers is a one-line calculation, and its transport proof closes on a
representative with `orthogonalSum_form`, `prod_apply` and `ring`. Here the ambient space is
`Frac(R) ⊗ (L.carrier × M.carrier)`, so the representative has to be replaced by a Riesz vector:
`TensorProduct.prodRight` (`Mathlib/LinearAlgebra/TensorProduct/Prod.lean`) splits both the span
and the dual, and `orthogonalSumSpanFst_rieszEmbedding`/`orthogonalSumSpanSnd_rieszEmbedding` stand
in for TauCeti's componentwise `dualCarrier` membership. The general transport is therefore a port
with a changed proof, not a Mathlib gap filled from scratch.

## LC-09 search record

Queries over the formalization corpus (`scripts/formalization_corpus.py search`):
`discriminantGroupOrthogonalSumEquiv` (TauCeti `Overlattice/Graph.lean`, the hit ported above),
`graph of an isometry orthogonal sum discriminant` (TauCeti `Overlattice/Graph.lean`,
`Overlattice/Dual.lean`), `overlattice discriminant form orthogonal complement quotient`
(TauCeti `Overlattice/Dual.lean`), `QuadraticMap.prod IsometryEquiv neg` (Mathlib
`LinearAlgebra/QuadraticForm/Prod.lean` — the product form itself, used directly),
`isotropic subgroup overlattice discriminant q|H^perp/H` (TauCeti roadmap import list only).
Added in the transport unit: repository-wide `rg` for `isFractionFieldPerfect_orthogonalSum`,
`evenDiscriminantDefectMap_surjective`, `rationalSpanProdEquiv`, `rationalizedForm_orthogonalSum`,
`rationalizedForm.*[Ii]nject` and `SeparatingLeft.*rationalizedForm` — the last two matter, because
the repository has `SeparatingLeft` proofs (`ReductionDiscriminant`, `PrimitiveReduction`) but
nothing deriving an *element* equality from pairings against lattice vectors, which is why
`orthogonalSumSpanFst_rieszEmbedding` is proved by `TensorProduct.inductionOn`; and
`rationalSpanProdEquiv` is the `R`-linear predecessor of `orthogonalSumSpanProdEquiv`
(`JordanRecursion.lean:58`, reused rather than restated, and recorded above). Mathlib source on
disk: `TensorProduct.tmul_eq_smul_one_tmul` (`Defs.lean:315`, the `a ⊗ₜ x = a • (1 ⊗ₜ x)` step),
`TensorProduct.prodRight_tmul` (`Prod.lean:50`, `rfl`), `TensorProduct.span_tmul_eq_top`
(`Defs.lean:418`, found and not needed), `Module.dualProdDualEquivDual` (`Dual/Lemmas.lean:89`,
found and not needed — the two dual coordinates are split by hand along `LinearMap.inl`/`inr`).
Corpus: `discriminant form of an orthogonal sum is the orthogonal sum of discriminant forms`,
`riesz embedding orthogonal sum coordinate restriction`,
`fraction field perfect orthogonal sum nondegenerate`, `discriminantQuadraticIsometryOrthogonalSum`
and `dualCarrier orthogonal sum product isometry quadratic discriminant`. The fourth returned
`Discriminant/Operations.lean`, the port source named in the provenance above — a file the earlier
record did not name, and which settles that the transport is a port; the others returned no
declaration-level hit.
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

/-! ## The product decomposition of the rational span

`orthogonalSumSpanFst` and `orthogonalSumSpanSnd` give the two coordinates separately. For the
perfectness of the sum's rationalized form the two coordinates are needed jointly, as a
`Frac(R)`-linear equivalence; that is what makes the correlation map of the sum the composite of
the two correlation maps with the product-dual splitting, and hence a bijection.

`JordanRecursion.rationalSpanProdEquiv` is the same `TensorProduct.prodRight` decomposition with
`R`-scalars only (`S := R`); it is stated there at a single lattice vector, which is what the
fractional-ideal layer needs. The equivalence here is the `Frac(R)`-linear one (`S := Frac(R)`),
because `rationalizedForm` is `Frac(R)`-bilinear and its coordinates have to be `Frac(R)`-linear
functionals for the dual arguments below. The two are the same map on the same carrier. -/

/-- The rational span of an orthogonal sum splits, `Frac(R)`-linearly, as the product of the
rational spans of the two factors. -/
noncomputable def orthogonalSumSpanProdEquiv :
    RationalSpan R (orthogonalSum L M) ≃ₗ[FractionRing R]
      (RationalSpan R L × RationalSpan R M) :=
  TensorProduct.prodRight R (FractionRing R) (FractionRing R) L.obj.carrier M.obj.carrier

omit [IsDomain R] in
@[simp]
theorem orthogonalSumSpanProdEquiv_tmul (a : FractionRing R)
    (z : ↥(orthogonalSum L M).obj.carrier) :
    orthogonalSumSpanProdEquiv (a ⊗ₜ[R] z) = (a ⊗ₜ[R] z.1, a ⊗ₜ[R] z.2) :=
  rfl

/-- **The rationalized form of an orthogonal sum is the sum of the two forms**, in the product
coordinates. `rationalizedForm_orthogonalSum_fst_snd` states the same identity along
`orthogonalSumSpanFst`/`orthogonalSumSpanSnd`, and `JordanRecursion.rationalizedForm_orthogonalSum`
is the case where the second argument is a lattice vector. The version below is the one the
perfectness of the sum needs: both arguments arbitrary, so that the identity can be evaluated at
the preimages `orthogonalSumSpanProdEquiv.symm (w, 0)` of an arbitrary functional. -/
theorem rationalizedForm_orthogonalSum_prodEquiv (u v : RationalSpan R (orthogonalSum L M)) :
    rationalizedForm R (orthogonalSum L M) u v =
      rationalizedForm R L (orthogonalSumSpanProdEquiv u).1 (orthogonalSumSpanProdEquiv v).1 +
        rationalizedForm R M (orthogonalSumSpanProdEquiv u).2
          (orthogonalSumSpanProdEquiv v).2 := by
  induction u using TensorProduct.inductionOn with
  | tmul a z =>
    induction v using TensorProduct.inductionOn with
    | tmul b z' =>
      rw [orthogonalSumSpanProdEquiv_tmul, orthogonalSumSpanProdEquiv_tmul, rationalizedForm_tmul,
        rationalizedForm_tmul, rationalizedForm_tmul, orthogonalSum_pairing_carrier, map_add,
        mul_add]
    | add v₁ v₂ h₁ h₂ =>
      rw [LinearMap.map_add, h₁, h₂]
      simp only [map_add, Prod.fst_add, Prod.snd_add]
      abel
  | add u₁ u₂ h₁ h₂ =>
    rw [LinearMap.map_add, LinearMap.add_apply, h₁, h₂]
    simp only [map_add, LinearMap.add_apply, Prod.fst_add, Prod.snd_add]
    abel

/-- **Fraction-field perfection is preserved by orthogonal sums.** The rationalized form of the
sum is, in the product coordinates, the composite of the two correlation maps of the factors with
the product-dual splitting, so bijectivity of the factors' correlation maps implies bijectivity of
the sum's: injectivity by evaluating at the preimages of `(w, 0)` and `(0, w)`, surjectivity by
solving each coordinate separately. -/
theorem isFractionFieldPerfect_orthogonalSum (hL : IsFractionFieldPerfect R L)
    (hM : IsFractionFieldPerfect R M) :
    IsFractionFieldPerfect R (orthogonalSum L M) := by
  constructor
  · intro u v huv
    apply (orthogonalSumSpanProdEquiv (L := L) (M := M)).injective
    refine Prod.ext ?_ ?_
    · have hinj : Function.Injective (rationalizedForm R L) := hL.1
      apply hinj
      apply LinearMap.ext
      intro w
      have h := LinearMap.congr_fun huv ((orthogonalSumSpanProdEquiv (L := L) (M := M)).symm
        (w, 0))
      rw [rationalizedForm_orthogonalSum_prodEquiv,
        rationalizedForm_orthogonalSum_prodEquiv] at h
      simpa using h
    · have hinj : Function.Injective (rationalizedForm R M) := hM.1
      apply hinj
      apply LinearMap.ext
      intro w
      have h := LinearMap.congr_fun huv ((orthogonalSumSpanProdEquiv (L := L) (M := M)).symm
        (0, w))
      rw [rationalizedForm_orthogonalSum_prodEquiv,
        rationalizedForm_orthogonalSum_prodEquiv] at h
      simpa using h
  · intro φ
    set φ' : Module.Dual (FractionRing R) (RationalSpan R L × RationalSpan R M) :=
      φ.comp (orthogonalSumSpanProdEquiv (L := L) (M := M)).symm.toLinearMap with hφ'
    let ψ₁ : Module.Dual (FractionRing R) (RationalSpan R L) :=
      φ'.comp (LinearMap.inl (FractionRing R) (RationalSpan R L) (RationalSpan R M))
    let ψ₂ : Module.Dual (FractionRing R) (RationalSpan R M) :=
      φ'.comp (LinearMap.inr (FractionRing R) (RationalSpan R L) (RationalSpan R M))
    refine ⟨(orthogonalSumSpanProdEquiv (L := L) (M := M)).symm
      ((rationalAdjointEquiv R L hL).symm ψ₁, (rationalAdjointEquiv R M hM).symm ψ₂), ?_⟩
    apply LinearMap.ext
    intro v
    have h1 : rationalizedForm R L ((rationalAdjointEquiv R L hL).symm ψ₁)
        (orthogonalSumSpanProdEquiv v).1 = ψ₁ (orthogonalSumSpanProdEquiv v).1 := by
      change (rationalAdjointEquiv R L hL) ((rationalAdjointEquiv R L hL).symm ψ₁) _ = _
      rw [LinearEquiv.apply_symm_apply]
    have h2 : rationalizedForm R M ((rationalAdjointEquiv R M hM).symm ψ₂)
        (orthogonalSumSpanProdEquiv v).2 = ψ₂ (orthogonalSumSpanProdEquiv v).2 := by
      change (rationalAdjointEquiv R M hM) ((rationalAdjointEquiv R M hM).symm ψ₂) _ = _
      rw [LinearEquiv.apply_symm_apply]
    rw [rationalizedForm_orthogonalSum_prodEquiv, LinearEquiv.apply_symm_apply, h1, h2]
    simp only [ψ₁, ψ₂, LinearMap.comp_apply, LinearMap.inl_apply, LinearMap.inr_apply]
    rw [← map_add]
    rw [show ((orthogonalSumSpanProdEquiv v).1, 0) + (0, (orthogonalSumSpanProdEquiv v).2) =
      orthogonalSumSpanProdEquiv v from by simp]
    simp [hφ', LinearEquiv.symm_apply_apply]

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

/-! ## The Riesz realizations of the two coordinates

The transport of the quadratic refinement to an arbitrary class of `A_(S ⊥ K)` needs one fact
about the Riesz realization: the two coordinates of the Riesz vector of a functional on the sum are
the Riesz vectors of its two coordinate restrictions. Pairing the identity against lattice vectors
and using injectivity of the rationalized form proves it, and — this is the point — it is a
statement about `RationalSpan` alone. No class of a metric dual and no surjectivity witness of
`metricDualToDiscriminant` is introduced anywhere, which is what clears the `whnf` divergence
recorded in `COMPLAINTS.md`.

The vector-level identity `evenDiscriminantQuadraticMap_orthogonalSum` then follows on a
representative `Submodule.Quotient.induction_on`, by `evenDiscriminantDefectMap_mk` for the two
coordinates and the splitting of the rationalized form. -/

/-- **The first coordinate of a Riesz vector.** The first coordinate of the Riesz vector of a
functional on the sum is the Riesz vector of the functional's restriction to the first factor. -/
theorem orthogonalSumSpanFst_rieszEmbedding (hL : IsFractionFieldPerfect R L)
    (hLM : IsFractionFieldPerfect R (orthogonalSum L M))
    (f : (orthogonalSum L M).obj.valueDual) :
    orthogonalSumSpanFst L M (rieszEmbedding R (orthogonalSum L M) hLM f) =
      rieszEmbedding R L hL (evenDiscriminantFstRestriction L M f) := by
  have hinj : Function.Injective (rationalizedForm R L) := hL.1
  apply hinj
  apply LinearMap.ext
  intro w
  induction w using TensorProduct.inductionOn with
  | tmul a x =>
    rw [TensorProduct.tmul_eq_smul_one_tmul, LinearMap.map_smul, LinearMap.map_smul]
    congr 1
    rw [show (1 : FractionRing R) ⊗ₜ[R] x = toRationalSpan R L x from rfl]
    have h := rationalizedForm_orthogonalSum_fst_snd
      (rieszEmbedding R (orthogonalSum L M) hLM f)
      (toRationalSpan R (orthogonalSum L M) ((x, 0) : ↥(orthogonalSum L M).obj.carrier))
    rw [orthogonalSumSpanFst_toRationalSpan, orthogonalSumSpanSnd_toRationalSpan] at h
    simp only [map_zero, add_zero] at h
    rw [← h, rationalizedForm_rieszEmbedding R (orthogonalSum L M) hLM f
        ((x, 0) : ↥(orthogonalSum L M).obj.carrier),
      rationalizedForm_rieszEmbedding R L hL (evenDiscriminantFstRestriction L M f) x]
    rfl
  | add w₁ w₂ h₁ h₂ => simp only [map_add, h₁, h₂]

/-- **The second coordinate of a Riesz vector.** The second coordinate of the Riesz vector of a
functional on the sum is the Riesz vector of the functional's restriction to the second factor. -/
theorem orthogonalSumSpanSnd_rieszEmbedding (hM : IsFractionFieldPerfect R M)
    (hLM : IsFractionFieldPerfect R (orthogonalSum L M))
    (f : (orthogonalSum L M).obj.valueDual) :
    orthogonalSumSpanSnd L M (rieszEmbedding R (orthogonalSum L M) hLM f) =
      rieszEmbedding R M hM (evenDiscriminantSndRestriction L M f) := by
  have hinj : Function.Injective (rationalizedForm R M) := hM.1
  apply hinj
  apply LinearMap.ext
  intro w
  induction w using TensorProduct.inductionOn with
  | tmul a y =>
    rw [TensorProduct.tmul_eq_smul_one_tmul, LinearMap.map_smul, LinearMap.map_smul]
    congr 1
    rw [show (1 : FractionRing R) ⊗ₜ[R] y = toRationalSpan R M y from rfl]
    have h := rationalizedForm_orthogonalSum_fst_snd
      (rieszEmbedding R (orthogonalSum L M) hLM f)
      (toRationalSpan R (orthogonalSum L M) ((0, y) : ↥(orthogonalSum L M).obj.carrier))
    rw [orthogonalSumSpanFst_toRationalSpan, orthogonalSumSpanSnd_toRationalSpan] at h
    simp only [map_zero, zero_add] at h
    rw [← h, rationalizedForm_rieszEmbedding R (orthogonalSum L M) hLM f
        ((0, y) : ↥(orthogonalSum L M).obj.carrier),
      rationalizedForm_rieszEmbedding R M hM (evenDiscriminantSndRestriction L M f) y]
    rfl
  | add w₁ w₂ h₁ h₂ => simp only [map_add, h₁, h₂]

/-- **The quadratic refinement of an orthogonal sum is the sum of the two refinements.**
For every class `z` of the discriminant form of `S ⊥ K`,
`q_(S ⊥ K)(z) = q_S(z₁) + q_K(z₂)` along the defect splitting `z ↦ (z₁, z₂)`. This is Nikulin,
*Integral symmetric bilinear forms and some of their applications*, Math. USSR Izv. 14 (1980),
§1.5, Prop. 1.5.1, p. 111: the quadratic form of the orthogonal sum is `q_S ⊕ q_K` under the
identification `A_(S ⊥ K) = A_S × A_K`.

`evenDiscriminantQuadraticMap_orthogonalSum_metricDual` is the same identity on a class with a
chosen metric-dual representative; this version is stated over an arbitrary class, which is the
form the gluing graph `Γ_γ ⊆ A_S ⊕ A_K` needs. -/
theorem evenDiscriminantQuadraticMap_orthogonalSum
    (hL : IsFractionFieldPerfect R L) (hM : IsFractionFieldPerfect R M)
    (hLM : IsFractionFieldPerfect R (orthogonalSum L M))
    (hEvenL : IsEven L) (hEvenM : IsEven M) (hEvenLM : IsEven (orthogonalSum L M))
    (z : (orthogonalSum L M).obj.defect) :
    evenDiscriminantQuadraticMap (L := orthogonalSum L M) hLM hEvenLM z =
      evenDiscriminantQuadraticMap (L := L) hL hEvenL (evenDiscriminantDefectMap L M z).1 +
        evenDiscriminantQuadraticMap (L := M) hM hEvenM (evenDiscriminantDefectMap L M z).2 := by
  induction z using Submodule.Quotient.induction_on with
  | _ f =>
    change doubleFractionValueProjection R
        (rationalizedForm R (orthogonalSum L M)
          (rieszEmbedding R (orthogonalSum L M) hLM f)
          (rieszEmbedding R (orthogonalSum L M) hLM f)) =
      doubleFractionValueProjection R
          (rationalizedForm R L (rieszEmbedding R L hL (evenDiscriminantFstRestriction L M f))
            (rieszEmbedding R L hL (evenDiscriminantFstRestriction L M f))) +
        doubleFractionValueProjection R
          (rationalizedForm R M (rieszEmbedding R M hM (evenDiscriminantSndRestriction L M f))
            (rieszEmbedding R M hM (evenDiscriminantSndRestriction L M f)))
    rw [rationalizedForm_orthogonalSum_fst_snd,
      orthogonalSumSpanFst_rieszEmbedding (L := L) (M := M) hL hLM f,
      orthogonalSumSpanSnd_rieszEmbedding (L := L) (M := M) hM hLM f, map_add]

end LeanCategories.Lattices.Valued
