/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Geometry.Manifold.IsManifold.Basic
public import Mathlib.Topology.Algebra.Module.Basic
public import Mathlib.Topology.Covering.Quotient

/-!
# The manifold structure on the quotient of a normed space by a discrete subgroup

Let `E` be a real or complex normed space and `L : Submodule ℤ E` a discrete subgroup. This file
puts a charted space structure and a `C^n` manifold structure on `E ⧸ L`, for every smoothness
exponent `n` and every base field over which `E` is a normed space. The complex torus `E ⧸ L` of a
lattice in a complex vector space is the case `𝕜 = ℂ`.

## Main results

* `LeanCategories.ForMathlib.instChartedSpaceQuotient`: `E ⧸ L` is a charted space over `E`. The
  charts are the local sections of the quotient map.
* `LeanCategories.ForMathlib.instIsManifoldQuotient`: `E ⧸ L` is a `C^n` manifold modelled on
  `𝓘(𝕜, E)`, for every `n` and every normed field `𝕜` acting on `E`.
* `LeanCategories.ForMathlib.isManifold_quotient_complex`: the complex case, stated separately.

## Construction

Mathlib supplies the charted space half almost directly. A discrete subgroup of a topological
group gives a quotient covering map
(`Topology.IsQuotientMap.isAddQuotientCoveringMap_of_addSubgroup`), a covering
map is a local homeomorphism, and a surjective local homeomorphism transports a charted space
structure (`IsLocalHomeomorph.chartedSpace`). Mathlib already applies this pattern to the orbit
quotient of a properly discontinuous action in `Mathlib.Geometry.Manifold.Instances.Quotient`, but
that file leaves the smooth structure as an explicit `TODO`, and its quotient is
`orbitRel.Quotient G M`, not the subgroup quotient `E ⧸ L`.

The smooth structure is the new content. A transition map `f` between two of these charts is a
continuous self map of an open subset of `E` with `f x - x ∈ L` for every `x`. Discreteness of `L`
forces `x ↦ f x - x` to be locally constant, so `f` is locally a translation and therefore `C^n`
for every `n`. This is `contDiffOn_of_sub_mem` below, and it does not use finite dimensionality,
completeness, or full rank of `L`.
-/

@[expose] public section

noncomputable section

namespace LeanCategories.ForMathlib

open Set Topology
open scoped ContDiff Manifold

universe u

variable {E : Type u} [NormedAddCommGroup E]

section Separation

variable (L : Submodule ℤ E) [DiscreteTopology L]

/-- A discrete subgroup of a normed space has a positive separation radius: no nonzero element
has norm below it. -/
theorem exists_separation_radius : ∃ r > 0, ∀ v ∈ L, ‖v‖ < r → v = 0 := by
  have hd : IsDiscrete (L : Set E) := SetLike.isDiscrete_iff_discreteTopology.mpr ‹_›
  obtain ⟨u, hu, huL⟩ := isDiscrete_iff_forall_mem_exists_isOpen.mp hd 0 L.zero_mem
  obtain ⟨r, hr, hru⟩ := Metric.isOpen_iff.mp hu 0 (huL.ge rfl).1
  refine ⟨r, hr, fun v hv hlt ↦ ?_⟩
  have hmem : v ∈ u ∩ (L : Set E) :=
    ⟨hru (by simpa [Metric.mem_ball, dist_eq_norm] using hlt), hv⟩
  rw [huL] at hmem
  simpa using hmem

end Separation

section Transition

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 E]
variable {L : Submodule ℤ E} [DiscreteTopology L]

/-- A continuous self map of an open set that moves every point by an element of a discrete
subgroup is locally a translation, hence `C^n` for every `n`. -/
theorem contDiffOn_of_sub_mem {n : ℕ∞ω} {f : E → E} {s : Set E}
    (hf : ContinuousOn f s) (hmem : ∀ x ∈ s, f x - x ∈ L) :
    ContDiffOn 𝕜 n f s := by
  obtain ⟨r, hr, hL⟩ := exists_separation_radius L
  refine contDiffOn_of_locally_contDiffOn fun x hx ↦ ?_
  have hg : ContinuousOn (fun y ↦ f y - y) s := hf.sub continuousOn_id
  obtain ⟨δ, hδ, hball⟩ :=
    Metric.continuousWithinAt_iff.mp (hg.continuousWithinAt hx) r hr
  refine ⟨Metric.ball x δ, Metric.isOpen_ball, Metric.mem_ball_self hδ, ?_⟩
  have key : ∀ y ∈ s ∩ Metric.ball x δ, f y = id y + (f x - x) := by
    intro y hy
    have h1 : f y - y - (f x - x) ∈ L := L.sub_mem (hmem y hy.1) (hmem x hx)
    have h2 : ‖f y - y - (f x - x)‖ < r := by
      simpa [dist_eq_norm] using hball hy.1 (Metric.mem_ball.mp hy.2)
    have h3 := hL _ h1 h2
    rw [sub_eq_zero] at h3
    simp only [id_eq, ← h3]
    abel
  exact ((contDiff_id.add contDiff_const).contDiffOn).congr key

end Transition

section ChartedSpace

variable (L : Submodule ℤ E) [DiscreteTopology L]

/-- The projection `E → E ⧸ L` onto the quotient by a discrete subgroup is a quotient covering
map for the translation action of `L`. -/
theorem isAddQuotientCoveringMap_mk :
    IsAddQuotientCoveringMap (Submodule.Quotient.mk : E → E ⧸ L) L.toAddSubgroup := by
  refine isQuotientMap_quotient_mk'.isAddQuotientCoveringMap_of_addSubgroup L.toAddSubgroup
    (SetLike.isDiscrete_iff_discreteTopology.mpr ‹_›) fun {x y} ↦ ?_
  change (Submodule.Quotient.mk x : E ⧸ L) = Submodule.Quotient.mk y ↔ _
  rw [Submodule.Quotient.eq, show y + -x = -(x - y) by abel]
  exact (Submodule.neg_mem_iff L).symm

/-- The projection `E → E ⧸ L` onto the quotient by a discrete subgroup is a local
homeomorphism. -/
theorem isLocalHomeomorph_mk :
    IsLocalHomeomorph (Submodule.Quotient.mk : E → E ⧸ L) :=
  (isAddQuotientCoveringMap_mk L).isCoveringMap.isLocalHomeomorph

/-- Charts on `E ⧸ L`: the local sections of the quotient map, transported along
`IsLocalHomeomorph.chartedSpace`. -/
instance instChartedSpaceQuotient : ChartedSpace E (E ⧸ L) :=
  (isLocalHomeomorph_mk L).chartedSpace (Submodule.Quotient.mk_surjective L)

variable {L}

/-- Every chart of `E ⧸ L` is a section of the quotient map: its inverse is the projection. -/
theorem symm_eq_mk_of_mem_atlas {e : OpenPartialHomeomorph (E ⧸ L) E}
    (he : e ∈ atlas E (E ⧸ L)) :
    ⇑e.symm = (Submodule.Quotient.mk : E → E ⧸ L) := by
  obtain ⟨q, rfl⟩ := he
  simp

/-- A chart of `E ⧸ L` composed with the projection is the identity on its source. -/
theorem mk_chart_apply {e : OpenPartialHomeomorph (E ⧸ L) E} (he : e ∈ atlas E (E ⧸ L))
    {x : E ⧸ L} (hx : x ∈ e.source) :
    (Submodule.Quotient.mk (e x) : E ⧸ L) = x := by
  rw [← congrFun (symm_eq_mk_of_mem_atlas he) (e x)]
  exact e.left_inv hx

end ChartedSpace

section IsManifold

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 E]
variable (L : Submodule ℤ E) [DiscreteTopology L]

/-- The quotient of a normed space by a discrete subgroup is a `C^n` manifold modelled on the
space itself. The transition maps between the sections of the quotient map are translations by
elements of `L`. -/
instance instIsManifoldQuotient (n : ℕ∞ω) :
    IsManifold (modelWithCornersSelf 𝕜 E) n (E ⧸ L) := by
  refine isManifold_of_contDiffOn _ _ _ fun e e' he he' ↦ ?_
  simp only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, Set.range_id,
    Set.preimage_id, Set.inter_univ, Function.id_comp, Function.comp_id]
  refine contDiffOn_of_sub_mem (L := L) (e.symm ≫ₕ e').continuousOn fun u hu ↦ ?_
  rw [OpenPartialHomeomorph.trans_source] at hu
  have hsymm : e.symm u = (Submodule.Quotient.mk u : E ⧸ L) :=
    congrFun (symm_eq_mk_of_mem_atlas he) u
  have hmem : (Submodule.Quotient.mk u : E ⧸ L) ∈ e'.source := hsymm ▸ hu.2
  have : (Submodule.Quotient.mk ((e.symm ≫ₕ e') u) : E ⧸ L) = Submodule.Quotient.mk u := by
    rw [OpenPartialHomeomorph.coe_trans, Function.comp_apply, hsymm]
    exact mk_chart_apply he' hmem
  exact (Submodule.Quotient.eq L).mp this

/-- The complex case: for a discrete subgroup `L` of a complex normed space `E`, the quotient
`E ⧸ L` is a complex manifold modelled on `𝓘(ℂ, E)`, since the transition maps are translations
and hence `ℂ`-analytic. Taking `E` finite dimensional over `ℂ` and `L` a full lattice gives the
complex torus. -/
theorem isManifold_quotient_complex [NormedSpace ℂ E] (n : ℕ∞ω) :
    IsManifold (modelWithCornersSelf ℂ E) n (E ⧸ L) :=
  inferInstance

end IsManifold

end LeanCategories.ForMathlib
