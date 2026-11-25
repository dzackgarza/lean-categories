/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Lattices.Valued.SemifanArrangement
public import LeanCategories.Lattices.Valued.ConicalRefinement
public import LeanCategories.Lattices.Valued.FibreArithmetic

/-!
# The assembly of the phase: `Σ(ℋ)` as an admissible decomposition, and `J_{Σ(ℋ)} = J_ℋ`

E. Looijenga, *Compactifications defined by arrangements II: locally symmetric varieties of type
IV*, arXiv math/0201218v2 (2002), text version `.tmp-sources/looijenga-math0201218v2.md`:
Definition 6.1 (p. 28, text line 769), Example 6.4 (p. 29, text line 791) and Lemma 6.6 (p. 30,
text line 821). The parent issue is lean-categories#162; this module is what the parent retains
after its children close — the three residual connections, and nothing the children prove again.

## The three connections

1. **The arithmetic input of #167 applied to #166's geometric object.** `Σ(ℋ)` is
   `SemifanArrangement.semifanArrangement`; its members are the members of #166's `ConicalMember`
   (`ConicalMember.fibre`, `ConicalMember.plane`); and the counting input is read, at every fibre,
   from the reduced lattice `(Λ ⊓ I^⊥)/(Λ ⊓ I)` of §1B (`FibreReducedLatticeInput`,
   `cutsFinitelyOnTraces_semifanArrangement_of_reducedLattice`) rather than assumed as an
   ambient-indexed `hcut`. `isAdmissibleDecomposition_semifanArrangement_of_reducedLattice` is the
   object, `vSigmaPlane_semifanArrangement_eq_JH_of_reducedLattice` is its plane support, and
   `example64_vSigma_le_of_subfamily` feeds it to #169's refinement: a subfamily `ℋ' ⊆ ℋ` inherits
   the same arithmetic input (its traces are among `ℋ`'s), `semifanArrangement_refinesConicalLocus`
   gives the containment *and* covering, and `vSigma_le_of_refinesConicalLocus` then gives Lemma
   6.6's inclusion `V_σ ⊆ V_{σ'}`.
2. **`J_{Σ(ℋ)} = J_ℋ` on #165's plane data**, with the counting read as #167's `Set` of traces:
   `vSigmaPlane_semifanArrangement_eq_JH_of_traces`. The two sides are
   `sigmaSupportSpace (positiveCone.upper …) (semifanArrangement ψ F) ⟨r_J⟩` — the operation on the
   half line `σ = C_{J,+}` of Definition 6.1 (ii) — and
   `JH ψ G = J^⊥ ⊓ ⋂ {H ∈ ℋ : J ⊆ H}` (`SemifanArrangement.JH`).
3. **The four acceptance items together**: section "The four items of #162" below.

## The two records the issue asks for

**The zero and fibre-bottom defect is repaired, at #166's member type.** The geometric member type
at `55966097` had two presentations of the point `{0}` of the conical locus — the apex
`ConicalMember.zero` and a zero-cone of a fibre `ConicalMember.fibre F ⊥` — with the *same* carrier
and *different* support spaces (`{0}` versus `lineSpan F`). #166 repairs it at the definition of the
member-level support space: `ConicalMember.fibreVSigma` takes the apex's value `{0}` at `σ = ⊥`
(`ConicalMember.fibreVSigma_bot`), and the reconciliation is exported as
`ConicalMember.vSigma_fibre_bot` (support spaces), `ConicalMember.carrier_fibre_bot` (carriers) and
`ConicalMember.isotropicCenter_zero_member` (centres). `zero_presentation_agrees` below states the
three together at one object, so the repair is part of the assembly and not only of the child.

**The arrangement caller's ambient-indexed `hcut` is replaced by #167's trace interface.** The
caller that Example 6.4 inherited,
`SemifanArrangement.isAdmissibleDecomposition_semifanArrangement_of_signature`
(`SemifanArrangement.lean:2662`), takes
`hcut : ∀ F, CutsFinitelyOnRational F.closure (fun i : fibreWalls ψ F => fibreFormC F (ψ ↑i))`: a
count *indexed by the ambient walls*. For an infinite `ℋ` — the source's `ℋ` is a finite union of
`Γ`-orbits, so infinite — that statement is false whenever one trace is repeated infinitely often,
and it is strictly stronger than the source's count of hyperplanes of the Grassmannian. #167's
interface is `FibreArithmetic.CutsFinitelyOnTraces F (distinctTraces ψ F)`, a predicate on a `Set`
of traces. The replacement happens in three places:
`cutsFinitelyOnRational_traceForm_of_cutsFinitelyOnTraces` (the `Set`-count as the trace-indexed
count, through `cutsFinitelyOnRational_iff_cutsFinitelyOnTraces`),
`cutsFinitelyOnTraces_semifanArrangement_of_reducedLattice` (`CutsFinitelyOnTraces` derived from the
reduced lattice by `cutsFinitelyOnTraces_orbitFamily`), and
`rayTraceKernels_eq_iInf_fibreWalls` (the intersection over the trace index is the intersection
over the ambient walls, so the existing ambient-indexed consumers — `fibreJH`,
`JH_le_lineSpan_sup_fibreJH` — are read through it instead of assumed). The ambient-indexed theorems
stay in `SemifanArrangement` as the stronger-hypothesis form for finite `ℋ`; nothing in this module
assumes them.
-/

@[expose] public section

open PointedCone QuadraticMap

open scoped TensorProduct

namespace LeanCategories.Lattices.Valued

variable {V : Type} [AddCommGroup V] [Module ℚ V] [Module.Finite ℚ V]

/-! ## The trace index and the ambient index

#167's counting interface is a predicate on the fibre's `Set` of traces; `Σ(ℋ)`'s own statements
(`semifanArrangement`, `fibreJH`) are indexed by the ambient walls containing the line. The two
indices cut the same cones out, because a wall's trace form is the wall's own form restricted to the
fibre and the scalar relating a wall to a representative of its trace is nonzero. -/

section TraceIndex

variable {BQ : LinearMap.BilinForm ℚ V} {Q : QuadraticForm ℝ (realified V)}
variable {ι : Type*} {ψ : ι → V →ₗ[ℚ] ℚ} {F : ConicalLine BQ Q}

omit [Module.Finite ℚ V] in
/-- **The common kernel of the traces vanishing at a point of the fibre is the common kernel of the
walls vanishing there**: the intersection over the fibre's `Set` of distinct traces
(`FibreArithmetic.rayTraceKernels`) is the intersection over the ambient walls that contain the line
and whose form vanishes at the point. Both directions are the scalar relation between a wall's form
and the trace form of its trace (`exists_smul_traceForm`, `traceRep_spec`), which preserves kernels
and vanishing at a point.

This is the lemma that lets #167's `Set`-count and #166's ambient-indexed object be compared: the
`J_ℋ` of Example 6.4 is written on either index. -/
theorem rayTraceKernels_eq_iInf_fibreWalls (ψ : ι → V →ₗ[ℚ] ℚ) (F : ConicalLine BQ Q)
    (ρ : ↥F.space) :
    rayTraceKernels ψ F ρ =
      ⨅ i : {i : fibreWalls ψ F // fibreFormC F (ψ ↑i) (rationalPoint ρ) = 0},
        LinearMap.ker (fibreFormC F (ψ ↑i)).toLinearMap := by
  refine le_antisymm ?_ ?_
  · refine le_iInf fun j => ?_
    obtain ⟨c, hc0, hc⟩ := exists_smul_traceForm ψ F j.1
    have hzero : traceForm ψ F (traceProj ψ F j.1) (rationalPoint ρ) = 0 := by
      have h := j.2
      rw [hc, smul_apply, smul_eq_mul] at h
      exact (mul_eq_zero.1 h).resolve_left hc0
    refine (iInf_le (fun T : {T : distinctTraces ψ F // traceForm ψ F T (rationalPoint ρ) = 0} =>
      LinearMap.ker (traceForm ψ F T.1).toLinearMap) ⟨traceProj ψ F j.1, hzero⟩).trans ?_
    intro x hx
    have hx' : traceForm ψ F (traceProj ψ F j.1) x = 0 := by
      simpa [LinearMap.mem_ker] using hx
    change fibreFormC F (ψ ↑j.1) x = 0
    rw [hc, smul_apply, smul_eq_mul, hx', mul_zero]
  · refine le_iInf fun T => ?_
    exact iInf_le (fun i : {i : fibreWalls ψ F // fibreFormC F (ψ ↑i) (rationalPoint ρ) = 0} =>
      LinearMap.ker (fibreFormC F (ψ ↑i)).toLinearMap) ⟨traceRep ψ F T.1, T.2⟩

omit [Module.Finite ℚ V] in
/-- **`fibreJH` is the fibre's `J_ℋ`, read on the trace index**: the vectors of the fibre orthogonal
to the half line and killed by every wall through it. The statement is the definition of
`SemifanArrangement.fibreJH` with the ambient index replaced through
`rayTraceKernels_eq_iInf_fibreWalls`. -/
theorem fibreJH_eq_ker_rayTraceKernels (ψ : ι → V →ₗ[ℚ] ℚ) (hBsym : BQ.IsSymm)
    (F : ConicalLine BQ Q) (G : ConicalPlane BQ) (h : F.line ≤ G.plane) :
    fibreJH ψ hBsym F G h =
      LinearMap.ker ((associated (fibreForm Q F.space)) (rationalPoint (fibreRay hBsym F G h))) ⊓
        rayTraceKernels ψ F (fibreRay hBsym F G h) := by
  rw [rayTraceKernels_eq_iInf_fibreWalls]
  rfl

omit [Module.Finite ℚ V] in
/-- **#167's count, as the count of trace forms**: a `Set` of traces cutting finitely often is the
indexed count of any family of trace forms indexed by those traces. Applied to the fibre's own
`traceForm`, this is the hypothesis `SemifanArrangement`'s support statements take, derived from the
duplicate-insensitive predicate. -/
theorem cutsFinitelyOnRational_traceForm_of_cutsFinitelyOnTraces
    (hcut : CutsFinitelyOnTraces F (distinctTraces ψ F)) :
    CutsFinitelyOnRational F.closure (traceForm ψ F) := by
  refine (cutsFinitelyOnRational_iff_cutsFinitelyOnTraces (F := F) ?_).2 hcut
  intro T
  exact ⟨(ψ ↑(traceRep ψ F T)).comp F.space.subtype, traceRep_spec ψ F T,
    fibreFormC_eq_fibreTraceCLM (ψ ↑(traceRep ψ F T)) F⟩

end TraceIndex

/-! ## `J_{Σ(ℋ)} = J_ℋ` at a plane of #165's type, on #167's count

Example 6.4, p. 29: "the space `J_ℋ` associated to a `ℚ`-isotropic plane `J` is the common
intersection of `J^⊥` and the hyperplanes `H ∈ ℋ` containing `J`", and `J_{Σ(ℋ)}` is the
`Σ`-support space of the half line `C_{J,+}`.

The two halves at the trace index: `sigmaSupportSpace` of the half line is inside the kernel of the
ray's own metric dual (`sigmaSupportSpace_semifanArrangement_le_ker_fibreRay`) and inside each
vanishing trace (`sigmaSupportSpace_semifanArrangement_le_ker_wall`), which give `≤` after the
metrically-shifted bound on the plane's ray
(`sigmaSupportSpace_semifanArrangement_map_le_ker_planeRay`); and `≥` is the source's
`inf_ker_iInf_span_le_sigmaSupportSpace` fed by the primal description of a cell by its walls
(`FibreArithmetic.iInf_traceKernel_le_span_of_member`), which is the fibre form of `fibreJH` —
`fibreJH_eq_ker_rayTraceKernels` and `JH_le_lineSpan_sup_fibreJH`. -/

section PlaneSupport

variable {BQ : LinearMap.BilinForm ℚ V} {Q : QuadraticForm ℝ (realified V)}
variable {ι : Type*} {ψ : ι → V →ₗ[ℚ] ℚ}

omit [Module.Finite ℚ V] in
/-- **The two indexings of `Σ(ℋ)` give the same `Σ`-support space**: `semifanArrangementTraces_eq`
read under `sigmaSupportSpace`. Stated as its own equality because the support statements of
`FibreArithmetic` are indexed by the fibre's `Set` of traces (#167) and the object of §6 by the
ambient walls, and the two families of cones agree by that equality. -/
theorem sigmaSupportSpace_semifanArrangement_eq_traces (ψ : ι → V →ₗ[ℚ] ℚ) (F : ConicalLine BQ Q)
    (C : Set (realified ↥F.space)) (σ : PointedCone ℝ (realified ↥F.space)) :
    sigmaSupportSpace C (semifanArrangement ψ F) σ =
      sigmaSupportSpace C (semifanArrangementTraces ψ F) σ := by
  rw [semifanArrangementTraces_eq]

/-- **The Σ-support space of the half line lies in the kernel of the ray's metric dual**, with the
count read from #167's traces. The half line is the class of the plane's positive generator `r_J`
(`ConicalPlane.IsPositiveAt` at a coherent presentation), and the fibre has signature `(1, n-1)`, so
the metric dual of an isotropic vector of the closed sheet is nonnegative on the sheet and vanishes
at the ray. -/
theorem sigmaSupportSpace_semifanArrangement_le_ker_fibreRay (ψ : ι → V →ₗ[ℚ] ℚ)
    (hBQ : ∀ u w : V, (associated Q) (rationalPoint u) (rationalPoint w) = (BQ u w : ℝ))
    (hBsym : BQ.IsSymm) (F : ConicalLine BQ Q) (G : ConicalPlane BQ) (h : F.line ≤ G.plane)
    (hpos : sigPos (fibreForm Q F.space) = 1)
    (hnd : (fibreForm Q F.space).Nondegenerate)
    (hcut : CutsFinitelyOnTraces F (distinctTraces ψ F)) :
    sigmaSupportSpace (positiveCone.upper (fibreForm Q F.space) F.sheet) (semifanArrangement ψ F)
        (PointedCone.hull ℝ ({rationalPoint (fibreRay hBsym F G h)} : Set (realified ↥F.space))) ≤
      LinearMap.ker ((associated (fibreForm Q F.space))
        (rationalPoint (fibreRay hBsym F G h))) := by
  have h := sigmaSupportSpace_ray_le_ker (Q := Q) (ψ := ψ) (F := F) hpos hnd
    (cutsFinitelyOnRational_traceForm_of_cutsFinitelyOnTraces hcut)
    (fibreRay_isotropic hBQ hBsym F G h) (fibreRay_ne_zero hBsym F G h)
    (fibreRay_sheet_nonneg hBsym F G h)
  exact le_of_eq_of_le (sigmaSupportSpace_semifanArrangement_eq_traces ψ F _ _) h

/-- **The Σ-support space of the half line lies in the kernel of every vanishing wall's trace**,
with the count read from #167's traces. This is the half of `J_{Σ(ℋ)} ⊆ J_ℋ` that runs through the
walls of `ℋ` itself. -/
theorem sigmaSupportSpace_semifanArrangement_le_ker_wall (ψ : ι → V →ₗ[ℚ] ℚ)
    (hBQ : ∀ u w : V, (associated Q) (rationalPoint u) (rationalPoint w) = (BQ u w : ℝ))
    (hBsym : BQ.IsSymm) (F : ConicalLine BQ Q) (G : ConicalPlane BQ) (h : F.line ≤ G.plane)
    (hpos : sigPos (fibreForm Q F.space) = 1)
    (hnd : (fibreForm Q F.space).Nondegenerate)
    (hcut : CutsFinitelyOnTraces F (distinctTraces ψ F))
    (i : fibreWalls ψ F)
    (hi : fibreFormC F (ψ ↑i) (rationalPoint (fibreRay hBsym F G h)) = 0) :
    sigmaSupportSpace (positiveCone.upper (fibreForm Q F.space) F.sheet) (semifanArrangement ψ F)
        (PointedCone.hull ℝ ({rationalPoint (fibreRay hBsym F G h)} : Set (realified ↥F.space))) ≤
      LinearMap.ker (fibreFormC F (ψ ↑i)).toLinearMap := by
  have hR : sigmaSupportSpace (positiveCone.upper (fibreForm Q F.space) F.sheet)
      (semifanArrangementTraces ψ F)
      (PointedCone.hull ℝ ({rationalPoint (fibreRay hBsym F G h)} : Set (realified ↥F.space))) ≤
      rayTraceKernels ψ F (fibreRay hBsym F G h) :=
    sigmaSupportSpace_ray_le_traceKernels (Q := Q) (ψ := ψ) (F := F) hpos hnd
      (cutsFinitelyOnRational_traceForm_of_cutsFinitelyOnTraces hcut)
      (fibreRay_isotropic hBQ hBsym F G h) (fibreRay_ne_zero hBsym F G h)
      (fibreRay_sheet_nonneg hBsym F G h)
  have hwall : rayTraceKernels ψ F (fibreRay hBsym F G h) ≤
      LinearMap.ker (fibreFormC F (ψ ↑i)).toLinearMap := by
    rw [rayTraceKernels_eq_iInf_fibreWalls]
    exact iInf_le (fun j : {j : fibreWalls ψ F //
        fibreFormC F (ψ ↑j) (rationalPoint (fibreRay hBsym F G h)) = 0} =>
        LinearMap.ker (fibreFormC F (ψ ↑j)).toLinearMap) ⟨i, hi⟩
  exact le_of_eq_of_le (sigmaSupportSpace_semifanArrangement_eq_traces ψ F _ _) (hR.trans hwall)

/-- **The half line's Σ-support space lies in the orthogonal complement of the plane's ray**: the
`⟨r_J⟩^⊥` half of `J^⊥` in Example 6.4, p. 29, carried from the fibre to `V(ℝ)`. The class of `r_J`
in the fibre differs from `r_J` by a multiple of the line's generator (`fibreRayProj_val`), which
the fibre is orthogonal to. -/
theorem sigmaSupportSpace_semifanArrangement_map_le_ker_planeRay (ψ : ι → V →ₗ[ℚ] ℚ)
    (hBQ : ∀ u w : V, (associated Q) (rationalPoint u) (rationalPoint w) = (BQ u w : ℝ))
    (hBsym : BQ.IsSymm) (F : ConicalLine BQ Q) (G : ConicalPlane BQ) (h : F.line ≤ G.plane)
    (hpos : sigPos (fibreForm Q F.space) = 1)
    (hnd : (fibreForm Q F.space).Nondegenerate)
    (hcut : CutsFinitelyOnTraces F (distinctTraces ψ F)) :
    (sigmaSupportSpace (positiveCone.upper (fibreForm Q F.space) F.sheet) (semifanArrangement ψ F)
        (PointedCone.hull ℝ ({rationalPoint (fibreRay hBsym F G h)} :
          Set (realified ↥F.space)))).map (realifyMap F.space) ≤
      LinearMap.ker ((associated Q) (rationalPoint (F.planeRay G h))) := by
  intro z hz
  obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.1 hz
  have hker := sigmaSupportSpace_semifanArrangement_le_ker_fibreRay ψ hBQ hBsym F G h hpos hnd hcut
    hy
  change (associated Q (rationalPoint (F.planeRay G h))) (realifyMap F.space y) = 0
  have hgen0 : (associated Q) (rationalPoint F.gen) (realifyMap F.space y) = 0 :=
    (mem_planePerp_iff.1 (realify_planeComplement_le_planePerp (Q := Q) (e := F.gen)
      (f := F.partner) hBQ ⟨y, rfl⟩)).1
  have hproj : rationalPoint ((fibreRayProj hBsym F G h : ↥F.space) : V) =
      rationalPoint (F.planeRay G h) - (BQ (F.planeRay G h) F.partner : ℝ) • rationalPoint F.gen :=
    by
    rw [fibreRayProj_val hBsym F G h, map_sub]
    congr 1
    exact rationalPoint_rat_smul (BQ (F.planeRay G h) F.partner) F.gen
  have hshift : (associated Q) (rationalPoint (F.planeRay G h)) (realifyMap F.space y) =
      (associated Q) (rationalPoint ((fibreRayProj hBsym F G h : ↥F.space) : V))
        (realifyMap F.space y) := by
    rw [hproj, LinearMap.BilinForm.sub_left, LinearMap.BilinForm.smul_left, hgen0, mul_zero,
      sub_zero]
  rw [hshift]
  have hfib : (associated (fibreForm Q F.space)) (rationalPoint (fibreRayProj hBsym F G h)) y =
      (associated Q) (rationalPoint ((fibreRayProj hBsym F G h : ↥F.space) : V))
        (realifyMap F.space y) := by
    rw [associated_fibreForm, realifyMap_rationalPoint]
  rw [← hfib]
  rcases fibreRay_eq_or_neg hBsym F G h with h' | h'
  · have h0 := LinearMap.mem_ker.1 hker
    rw [h'] at h0
    exact h0
  · have h0 := LinearMap.mem_ker.1 hker
    rw [h'] at h0
    simpa using h0

/-- **Looijenga, Example 6.4, p. 29: `J_{Σ(ℋ)} = J_ℋ`, on #167's count.** For a `ℚ`-isotropic plane
`J` of a `ConicalLine` fibre `I ⊆ J`, the `Σ(ℋ)`-support space of the half line `C_{J,+}` is the
source's `J_ℋ`:

  `lineSpan I ⊔ (Σ-support space of C_{J,+} in I^⊥/I) = J^⊥ ⊓ ⋂ {H ∈ ℋ : J ⊆ H}`.

The only counting input is `CutsFinitelyOnTraces F (distinctTraces ψ F)` — a predicate on a `Set`
of traces, so it is not defeated by an ambient family that repeats a trace — and the condition (i)
input `hS`; no ambient-indexed `hcut` appears. -/
theorem vSigmaPlane_semifanArrangement_eq_JH_of_traces (ψ : ι → V →ₗ[ℚ] ℚ)
    (hBQ : ∀ u w : V, (associated Q) (rationalPoint u) (rationalPoint w) = (BQ u w : ℝ))
    (hBsym : BQ.IsSymm) (F : ConicalLine BQ Q) (G : ConicalPlane BQ) (h : F.line ≤ G.plane)
    (hpos : sigPos (fibreForm Q F.space) = 1)
    (hnd : (fibreForm Q F.space).Nondegenerate)
    (hcut : CutsFinitelyOnTraces F (distinctTraces ψ F))
    (hS : IsLocallyRationalDecomposition F.closure (semifanArrangement ψ F)) :
    vSigmaPlane hBsym F (semifanArrangement ψ F) G h = JH (Q := Q) ψ G := by
  have hX : sigmaSupportSpace (positiveCone.upper (fibreForm Q F.space) F.sheet)
      (semifanArrangement ψ F)
      (PointedCone.hull ℝ ({rationalPoint (fibreRay hBsym F G h)} :
        Set (realified ↥F.space))) =
      LinearMap.ker ((associated (fibreForm Q F.space)) (rationalPoint (fibreRay hBsym F G h))) ⊓
        rayTraceKernels ψ F (fibreRay hBsym F G h) := by
    rw [sigmaSupportSpace_semifanArrangement_eq_traces]
    exact sigmaSupportSpace_ray_eq (ψ := ψ) hpos hnd
      (cutsFinitelyOnRational_traceForm_of_cutsFinitelyOnTraces hcut)
      (by rw [semifanArrangementTraces_eq]; exact hS)
      (fibreRay_isotropic hBQ hBsym F G h) (fibreRay_ne_zero hBsym F G h)
      (fibreRay_sheet_nonneg hBsym F G h)
  refine le_antisymm ?_ ?_
  · rw [vSigmaPlane]
    refine sup_le ?_ ?_
    · rw [JH]
      refine le_inf ?_ (le_iInf fun i => ?_)
      · rw [planePerpQ]
        refine le_iInf fun a => ?_
        rw [lineSpan, Submodule.span_le]
        rintro x hx
        rw [Set.mem_singleton_iff] at hx
        subst hx
        change (associated Q (rationalPoint (a : V))) (rationalPoint F.gen) = 0
        rw [hBQ]
        exact_mod_cast G.isotropic (a : V) a.2 F.gen (F.gen_mem_plane G h)
      · rw [lineSpan, Submodule.span_le]
        rintro x hx
        rw [Set.mem_singleton_iff] at hx
        subst hx
        rw [realifiedFormC_toLinearMap]
        change realifiedForm (ψ (i : ι)) (rationalPoint F.gen) = 0
        rw [realifiedForm_rationalPoint]
        exact_mod_cast i.2 F.gen (F.gen_mem_plane G h)
    · intro z hz
      obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.1 hz
      rw [JH, Submodule.mem_inf]
      refine ⟨?_, ?_⟩
      · rw [planePerpQ, ← ker_inf_ker_eq F G h]
        exact Submodule.mem_inf.2
          ⟨(mem_planePerp_iff.1 (realify_planeComplement_le_planePerp (Q := Q) (e := F.gen)
            (f := F.partner) hBQ ⟨y, rfl⟩)).1,
            sigmaSupportSpace_semifanArrangement_map_le_ker_planeRay ψ hBQ hBsym F G h hpos hnd
              hcut (Submodule.mem_map_of_mem hy)⟩
      · rw [Submodule.mem_iInf]
        intro i
        have hline : F.line ≤ LinearMap.ker (ψ (i : ι)) := by
          rw [F.line_eq]
          refine Submodule.span_le.2 ?_
          rintro x hx
          rw [Set.mem_singleton_iff] at hx
          subst hx
          exact i.2 F.gen (F.gen_mem_plane G h)
        have hi : fibreFormC F (ψ (i : ι)) (rationalPoint (fibreRay hBsym F G h)) = 0 :=
          fibreFormC_fibreRay_eq_zero_of_vanishes_plane ψ hBsym F G h i.2
        have hwall := sigmaSupportSpace_semifanArrangement_le_ker_wall ψ hBQ hBsym F G h hpos hnd
          hcut ⟨i.1, hline⟩ hi
        have hy' : fibreFormC F (ψ (i : ι)) y = 0 := hwall hy
        rw [realifiedFormC_toLinearMap, LinearMap.mem_ker, ← fibreFormC_apply F (ψ (i : ι)) y]
        exact hy'
  · rw [vSigmaPlane, hX]
    refine (JH_le_lineSpan_sup_fibreJH ψ hBQ hBsym F G h).trans (sup_le_sup_left ?_ _)
    exact Submodule.map_mono (le_of_eq (fibreJH_eq_ker_rayTraceKernels ψ hBsym F G h))

end PlaneSupport


/-! ## Item 1: the arithmetic input of #167 read from the reduced lattice, and the object it makes

Example 6.4, p. 29 (text line 791): "`H` is a finite union of `Γ`-orbits of hyperplanes of signature
`(2, n-1)` ... the `H ∈ H` containing `I` correspond to `ℚ`-hyperplanes in `I^⊥/I ⊗ I` of signature
`(1, n-2)` and so according to example 4.3-b these decompose `C_{I,+}` into locally rational cones".
Read at the fibre, that hypothesis is: the traces of `ℋ` at `I` are one `Γ_I`-orbit family of
`ℚ`-hyperplanes of the reduced lattice `(Λ ⊓ I^⊥)/(Λ ⊓ I)`, with primitive generators. It is
`FibreReducedLatticeInput` below, and it is *all* the counting input the assembly takes: nothing of
the shape `∀ F, CutsFinitelyOnRational F.closure (fun i => ...)` remains. -/

section ReducedLatticeInput

variable {BQ : LinearMap.BilinForm ℚ V} {Q : QuadraticForm ℝ (realified V)} {ι : Type*}

/-- **The arithmetic input of Example 6.4 at every fibre, read from the reduced lattice.** At each
`ℚ`-isotropic line `I` (`F : ConicalLine BQ Q`), `Γ_I` is an arithmetic group of the reduced lattice
`(Λ ⊓ I^⊥)/(Λ ⊓ I)` of §1B, p. 11 — it preserves the lattice (`lattice_stable`) and the fibre's form
(`isometry`) — and `H₀` is a finite set of `ℚ`-hyperplanes of the fibre whose `Γ_I`-orbit family
generates the traces of `ℋ` at `I` primitively (`generator`, `traces`).

The fields are the source's data, not a child's conclusion: `traces` is the correspondence "the
`H ∈ ℋ` containing `I` correspond to `ℚ`-hyperplanes in `I^⊥/I`", and the finite orbit family is the
finiteness of `ℋ` as a union of `Γ`-orbits at the fibre. What the fibre then proves is
`cutsFinitelyOnTraces_semifanArrangement_of_reducedLattice`. -/
structure FibreReducedLatticeInput (hBsym : BQ.IsSymm) (Λ : Submodule ℤ V)
    (ψ : ι → V →ₗ[ℚ] ℚ) where
  /-- the arithmetic group `Γ_I` of the reduced lattice of each fibre -/
  ΓI : ∀ F : ConicalLine BQ Q, Set (↥F.space ≃ₗ[ℚ] ↥F.space)
  /-- `Γ_I` contains the identity -/
  one_mem : ∀ F : ConicalLine BQ Q, (1 : ↥F.space ≃ₗ[ℚ] ↥F.space) ∈ ΓI F
  /-- a finite set of hyperplanes of the fibre whose `Γ_I`-orbit family is the family of traces -/
  H₀ : ∀ F : ConicalLine BQ Q, Finset (Submodule ℚ ↥F.space)
  /-- a primitive generator of each line of the orbit family -/
  gen : ∀ F : ConicalLine BQ Q, ↥(orbitFamily (H₀ F) (ΓI F)) → ↥F.space
  /-- `Γ_I` acts on the reduced lattice by lattice isomorphisms -/
  lattice_stable : ∀ (F : ConicalLine BQ Q) (e : ↥F.space ≃ₗ[ℚ] ↥F.space), e ∈ ΓI F →
    Submodule.map ((e : ↥F.space →ₗ[ℚ] ↥F.space).restrictScalars ℤ) (reducedLattice hBsym F Λ) =
      reducedLattice hBsym F Λ
  /-- `Γ_I` acts by isometries of the fibre's form -/
  isometry : ∀ (F : ConicalLine BQ Q) (e : ↥F.space ≃ₗ[ℚ] ↥F.space), e ∈ ΓI F →
    ∀ x y : ↥F.space, restrictBilinForm BQ F.space (e x) (e y) = restrictBilinForm BQ F.space x y
  /-- the generator spans the line of the orbit family inside the reduced lattice -/
  generator : ∀ (F : ConicalLine BQ Q) (ℓ : ↥(orbitFamily (H₀ F) (ΓI F))), gen F ℓ ≠ 0 ∧
    reducedLattice hBsym F Λ ⊓ (ℓ.1).restrictScalars ℤ =
      Submodule.span ℤ ({gen F ℓ} : Set ↥F.space)
  /-- the traces of `ℋ` at the fibre are that orbit family -/
  traces : ∀ F : ConicalLine BQ Q, distinctTraces ψ F ⊆ orbitFamilyTraces BQ F (gen F)

variable {ψ : ι → V →ₗ[ℚ] ℚ}

set_option linter.style.haveILetI false in
/-- **#167's duplicate-insensitive count, derived from the reduced lattice at every fibre**: the
count `CutsFinitelyOnTraces F (distinctTraces ψ F)` of
`FibreArithmetic.cutsFinitelyOnTraces_orbitFamily` read through `FibreReducedLatticeInput`. The
fibre basis is the one `exists_basis_reducedLattice` produces from the ambient lattice, so no basis
of a reduced lattice is an input. -/
theorem cutsFinitelyOnTraces_semifanArrangement_of_reducedLattice
    (hBQsym : BQ.IsSymm)
    (hBQ : ∀ u w : V, (associated Q) (rationalPoint u) (rationalPoint w) = (BQ u w : ℝ))
    (hsig : sigPos Q = 2) (hnd : Q.Nondegenerate)
    {κ₀ : Type} [Finite κ₀] (bs₀ : Module.Basis κ₀ ℚ V)
    (hint₀ : ∀ x ∈ Submodule.span ℤ (Set.range bs₀), ∀ y ∈ Submodule.span ℤ (Set.range bs₀),
      ∃ n : ℤ, BQ x y = (n : ℚ))
    (A : FibreReducedLatticeInput (Q := Q) hBQsym (Submodule.span ℤ (Set.range bs₀)) ψ)
    (F : ConicalLine BQ Q) :
    CutsFinitelyOnTraces F (distinctTraces ψ F) := by
  classical
  obtain ⟨κ, hκ, bs, hbs⟩ := exists_basis_reducedLattice hBQsym F bs₀
  haveI : Fintype κ := hκ
  have hΓΛ : ∀ e ∈ A.ΓI F,
      Submodule.map ((e : ↥F.space →ₗ[ℚ] ↥F.space).restrictScalars ℤ)
        (Submodule.span ℤ (Set.range bs)) = Submodule.span ℤ (Set.range bs) := by
    intro e he
    rw [hbs]
    exact A.lattice_stable F e he
  have hgen : ∀ ℓ : ↥(orbitFamily (A.H₀ F) (A.ΓI F)), A.gen F ℓ ≠ 0 ∧
      Submodule.span ℤ (Set.range bs) ⊓ (ℓ.1).restrictScalars ℤ =
        Submodule.span ℤ ({A.gen F ℓ} : Set ↥F.space) := by
    intro ℓ
    obtain ⟨h1, h2⟩ := A.generator F ℓ
    exact ⟨h1, by rw [hbs]; exact h2⟩
  exact (cutsFinitelyOnTraces_orbitFamily hBQsym hBQ hsig hnd F bs₀ hint₀ bs hbs (A.ΓI F)
    (A.one_mem F) (A.H₀ F) hΓΛ (A.isometry F) (A.gen F) hgen).mono (A.traces F)

set_option linter.style.haveILetI false in
/-- **Condition (i) of Definition 6.1 for `Σ(ℋ)`, from the reduced lattice alone**: the members of
`Σ(ℋ)` in `C_{I,+}` are a locally rational decomposition, because Example 4.3 (b) at the reduced
lattice counts the cutting traces. No counting hypothesis is carried. -/
theorem semifanArrangement_isLocallyRational_of_reducedLattice
    (hBQsym : BQ.IsSymm)
    (hBQ : ∀ u w : V, (associated Q) (rationalPoint u) (rationalPoint w) = (BQ u w : ℝ))
    (hsig : sigPos Q = 2) (hnd : Q.Nondegenerate)
    {κ₀ : Type} [Finite κ₀] (bs₀ : Module.Basis κ₀ ℚ V)
    (hint₀ : ∀ x ∈ Submodule.span ℤ (Set.range bs₀), ∀ y ∈ Submodule.span ℤ (Set.range bs₀),
      ∃ n : ℤ, BQ x y = (n : ℚ))
    (A : FibreReducedLatticeInput (Q := Q) hBQsym (Submodule.span ℤ (Set.range bs₀)) ψ)
    (F : ConicalLine BQ Q) :
    IsLocallyRationalDecomposition F.closure (semifanArrangement ψ F) := by
  classical
  obtain ⟨κ, hκ, bs, hbs⟩ := exists_basis_reducedLattice hBQsym F bs₀
  haveI : Fintype κ := hκ
  have hΓΛ : ∀ e ∈ A.ΓI F,
      Submodule.map ((e : ↥F.space →ₗ[ℚ] ↥F.space).restrictScalars ℤ)
        (Submodule.span ℤ (Set.range bs)) = Submodule.span ℤ (Set.range bs) := by
    intro e he
    rw [hbs]
    exact A.lattice_stable F e he
  have hgen : ∀ ℓ : ↥(orbitFamily (A.H₀ F) (A.ΓI F)), A.gen F ℓ ≠ 0 ∧
      Submodule.span ℤ (Set.range bs) ⊓ (ℓ.1).restrictScalars ℤ =
        Submodule.span ℤ ({A.gen F ℓ} : Set ↥F.space) := by
    intro ℓ
    obtain ⟨h1, h2⟩ := A.generator F ℓ
    exact ⟨h1, by rw [hbs]; exact h2⟩
  exact semifanArrangement_isLocallyRational_of_orbitFamily hBQsym hBQ hsig hnd F bs₀ hint₀ bs hbs
    (A.ΓI F) (A.one_mem F) (A.H₀ F) hΓΛ (A.isometry F) (A.gen F) hgen ψ (A.traces F)

/-- **Item 2's equality from the reduced-lattice input, with neither `hcut` nor condition (i) as a
hypothesis**: `J_{Σ(ℋ)} = J_ℋ` for every `ℚ`-isotropic plane of every fibre of `Σ(ℋ)`. -/
theorem vSigmaPlane_semifanArrangement_eq_JH_of_reducedLattice
    (hBQsym : BQ.IsSymm)
    (hBQ : ∀ u w : V, (associated Q) (rationalPoint u) (rationalPoint w) = (BQ u w : ℝ))
    (hsig : sigPos Q = 2) (hnd : Q.Nondegenerate)
    {κ₀ : Type} [Finite κ₀] (bs₀ : Module.Basis κ₀ ℚ V)
    (hint₀ : ∀ x ∈ Submodule.span ℤ (Set.range bs₀), ∀ y ∈ Submodule.span ℤ (Set.range bs₀),
      ∃ n : ℤ, BQ x y = (n : ℚ))
    (A : FibreReducedLatticeInput (Q := Q) hBQsym (Submodule.span ℤ (Set.range bs₀)) ψ)
    (F : ConicalLine BQ Q) (G : ConicalPlane BQ) (h : F.line ≤ G.plane) :
    vSigmaPlane hBQsym F (semifanArrangement ψ F) G h = JH (Q := Q) ψ G :=
  vSigmaPlane_semifanArrangement_eq_JH_of_traces ψ hBQ hBQsym F G h
    (sigPos_fibreForm_eq_one hBQ hBQsym hsig F)
    (fibreForm_space_nondegenerate hBQ hBQsym hnd F)
    (cutsFinitelyOnTraces_semifanArrangement_of_reducedLattice hBQsym hBQ hsig hnd bs₀ hint₀ A F)
    (semifanArrangement_isLocallyRational_of_reducedLattice hBQsym hBQ hsig hnd bs₀ hint₀ A F)

/-- **Item 1: `Σ(ℋ)` is an admissible decomposition of the conical locus** (Looijenga,
Definition 6.1, p. 28 and Example 6.4, p. 29), from a form of signature `(2, n)`, an integral
ambient lattice, and the arithmetic input of the reduced lattice at every fibre. Condition (i) is
`semifanArrangement_isLocallyRational_of_reducedLattice`, condition (ii) is
`vSigmaPlane_semifanArrangement_eq_JH_of_reducedLattice` through
`isAdmissibleDecomposition_of_vSigmaPlane_eq`, and `Γ`-invariance is the source's hypothesis on `ℋ`
as a `Γ`-invariant collection (`IsGammaInvariantLocus`); the finite-union-of-orbits form is
`isAdmissibleDecomposition_semifanArrangement_of_orbits` below. -/
theorem isAdmissibleDecomposition_semifanArrangement_of_reducedLattice
    (hBQsym : BQ.IsSymm)
    (hBQ : ∀ u w : V, (associated Q) (rationalPoint u) (rationalPoint w) = (BQ u w : ℝ))
    (hsig : sigPos Q = 2) (hnd : Q.Nondegenerate)
    {κ₀ : Type} [Finite κ₀] (bs₀ : Module.Basis κ₀ ℚ V)
    (hint₀ : ∀ x ∈ Submodule.span ℤ (Set.range bs₀), ∀ y ∈ Submodule.span ℤ (Set.range bs₀),
      ∃ n : ℤ, BQ x y = (n : ℚ))
    (A : FibreReducedLatticeInput (Q := Q) hBQsym (Submodule.span ℤ (Set.range bs₀)) ψ)
    {Γ : Set (V ≃ₗ[ℚ] V)}
    (hgamma : IsGammaInvariantLocus BQ Q Γ (semifanArrangement ψ)) :
    IsAdmissibleDecomposition BQ Q Γ (semifanArrangement ψ) where
  gammaInvariant := hgamma
  condition_i := fun F =>
    semifanArrangement_isLocallyRational_of_reducedLattice hBQsym hBQ hsig hnd bs₀ hint₀ A F
  condition_ii := by
    intro hBsym' F F' G h h'
    have hb : hBsym' = hBQsym := Subsingleton.elim _ _
    rw [hb]
    rw [vSigmaPlane_semifanArrangement_eq_JH_of_reducedLattice hBQsym hBQ hsig hnd bs₀ hint₀ A F G
        h,
      vSigmaPlane_semifanArrangement_eq_JH_of_reducedLattice hBQsym hBQ hsig hnd bs₀ hint₀ A F' G
        h']

/-- **Item 1, with the source's own form of the `Γ`-invariance**: `ℋ` is a finite union of
`Γ`-orbits of `ℚ`-hyperplanes (`IsFiniteUnionOfOrbits`), which is how Example 6.4, p. 29 states it.
The invariance is discharged by `semifanArrangement_gammaInvariant_of_finiteOrbits`. -/
theorem isAdmissibleDecomposition_semifanArrangement_of_orbits
    (hBQsym : BQ.IsSymm)
    (hBQ : ∀ u w : V, (associated Q) (rationalPoint u) (rationalPoint w) = (BQ u w : ℝ))
    (hsig : sigPos Q = 2) (hnd : Q.Nondegenerate)
    {κ₀ : Type} [Finite κ₀] (bs₀ : Module.Basis κ₀ ℚ V)
    (hint₀ : ∀ x ∈ Submodule.span ℤ (Set.range bs₀), ∀ y ∈ Submodule.span ℤ (Set.range bs₀),
      ∃ n : ℤ, BQ x y = (n : ℚ))
    (A : FibreReducedLatticeInput (Q := Q) hBQsym (Submodule.span ℤ (Set.range bs₀)) ψ)
    {Γ : Set (V ≃ₗ[ℚ] V)} (horbit : IsFiniteUnionOfOrbits Γ ψ) :
    IsAdmissibleDecomposition BQ Q Γ (semifanArrangement ψ) :=
  isAdmissibleDecomposition_semifanArrangement_of_reducedLattice hBQsym hBQ hsig hnd bs₀ hint₀ A
    (semifanArrangement_gammaInvariant_of_finiteOrbits horbit hBQ
      (fun F => sigPos_fibreForm_eq_one hBQ hBQsym hsig F))

end ReducedLatticeInput

/-! ## The four items of #162, together

One section, one hypothesis list: a form of signature `(2, n)` (`hsig`, `hnd`), an integral lattice
`Λ = span ℤ (range bs₀)` (`hint₀`), and the reduced-lattice arithmetic of Example 6.4 at every fibre
(`A`). Every statement below is a named item of the issue's original acceptance, and none of them
adds a hypothesis to another. -/

section Acceptance

variable {BQ : LinearMap.BilinForm ℚ V} {Q : QuadraticForm ℝ (realified V)} {ι : Type*}
variable {ψ : ι → V →ₗ[ℚ] ℚ} {Γ : Set (V ≃ₗ[ℚ] V)}

/-- **Acceptance item 1 — Definition 6.1, stated**: the arrangement `Σ(ℋ)` is an admissible
decomposition of the conical locus, from the reduced-lattice arithmetic at every fibre. -/
theorem example64_admissibleDecomposition
    (hBQsym : BQ.IsSymm)
    (hBQ : ∀ u w : V, (associated Q) (rationalPoint u) (rationalPoint w) = (BQ u w : ℝ))
    (hsig : sigPos Q = 2) (hnd : Q.Nondegenerate)
    {κ₀ : Type} [Finite κ₀] (bs₀ : Module.Basis κ₀ ℚ V)
    (hint₀ : ∀ x ∈ Submodule.span ℤ (Set.range bs₀), ∀ y ∈ Submodule.span ℤ (Set.range bs₀),
      ∃ n : ℤ, BQ x y = (n : ℚ))
    (A : FibreReducedLatticeInput (Q := Q) hBQsym (Submodule.span ℤ (Set.range bs₀)) ψ)
    (hgamma : IsGammaInvariantLocus BQ Q Γ (semifanArrangement ψ)) :
    IsAdmissibleDecomposition BQ Q Γ (semifanArrangement ψ) :=
  isAdmissibleDecomposition_semifanArrangement_of_reducedLattice hBQsym hBQ hsig hnd bs₀ hint₀ A
    hgamma

/-- **Acceptance item 1 — Definition 6.1, used**: condition (ii) of the decomposition just built,
at the level of the `Σ`-support spaces of the plane's half line in two fibres of one plane. The
support space of `C_{J,+}` does not depend on the `ℚ`-isotropic line `I ⊆ J` whose fibre computes
it, which is what `ConicalMember.vSigma_plane_witness` records at the member type. -/
theorem example64_vSigma_plane_independent
    (hBQsym : BQ.IsSymm)
    (hBQ : ∀ u w : V, (associated Q) (rationalPoint u) (rationalPoint w) = (BQ u w : ℝ))
    (hsig : sigPos Q = 2) (hnd : Q.Nondegenerate)
    {κ₀ : Type} [Finite κ₀] (bs₀ : Module.Basis κ₀ ℚ V)
    (hint₀ : ∀ x ∈ Submodule.span ℤ (Set.range bs₀), ∀ y ∈ Submodule.span ℤ (Set.range bs₀),
      ∃ n : ℤ, BQ x y = (n : ℚ))
    (A : FibreReducedLatticeInput (Q := Q) hBQsym (Submodule.span ℤ (Set.range bs₀)) ψ)
    (hgamma : IsGammaInvariantLocus BQ Q Γ (semifanArrangement ψ))
    (hBsym : BQ.IsSymm) (F F' : ConicalLine BQ Q) (G : ConicalPlane BQ)
    (h : F.line ≤ G.plane) (h' : F'.line ≤ G.plane) :
    vSigmaPlane hBsym F (semifanArrangement ψ F) G h =
      vSigmaPlane hBsym F' (semifanArrangement ψ F') G h' :=
  (example64_admissibleDecomposition hBQsym hBQ hsig hnd bs₀ hint₀ A hgamma).condition_ii
    hBsym F F' G h h'

omit [Module.Finite ℚ V] in
/-- **Acceptance item 2 — the `Σ`-support space `V_σ` of a member of a fibre**: Definition 6.1 (i)'s
span formula for every member of a conical fibre that the case covers. No hypothesis: it is the
member-level reading of `ConicalLocus.vSigma`. -/
theorem example64_vSigma_fibreMember (hBsym : BQ.IsSymm) (F : ConicalLine BQ Q)
    {σ : PointedCone ℝ (realified ↥F.space)} (hσ : σ ≠ ⊥) :
    (ConicalMember.fibre F σ : ConicalMember BQ Q).vSigma hBsym
        (fun F => semifanArrangement ψ F) =
      vSigma F σ :=
  ConicalMember.fibreVSigma_of_ne hσ

/-- **Acceptance item 2 — the `Σ`-support space `V_σ` of the plane member, which is `J_ℋ`**: for a
`ℚ`-isotropic plane `J` of #165's type — an oriented plane with a coherent presentation at a fibre
of one of its lines (`ConicalPlane.IsPositiveAt`) — the support space of the half line `C_{J,+}` is
the
source's `J_ℋ = J^⊥ ⊓ ⋂ {H ∈ ℋ : J ⊆ H}`. This is `J_{Σ(ℋ)} = J_ℋ` at the geometric member type. -/
theorem example64_vSigma_planeMember
    (hBQsym : BQ.IsSymm)
    (hBQ : ∀ u w : V, (associated Q) (rationalPoint u) (rationalPoint w) = (BQ u w : ℝ))
    (hsig : sigPos Q = 2) (hnd : Q.Nondegenerate)
    {κ₀ : Type} [Finite κ₀] (bs₀ : Module.Basis κ₀ ℚ V)
    (hint₀ : ∀ x ∈ Submodule.span ℤ (Set.range bs₀), ∀ y ∈ Submodule.span ℤ (Set.range bs₀),
      ∃ n : ℤ, BQ x y = (n : ℚ))
    (A : FibreReducedLatticeInput (Q := Q) hBQsym (Submodule.span ℤ (Set.range bs₀)) ψ)
    (F : ConicalLine BQ Q) (G : ConicalPlane BQ) (h : F.line ≤ G.plane)
    (hcoh : G.IsPositiveAt F h) :
    (ConicalMember.plane F G h hcoh : ConicalMember BQ Q).vSigma hBQsym
        (fun F => semifanArrangement ψ F) =
      JH (Q := Q) ψ G :=
  vSigmaPlane_semifanArrangement_eq_JH_of_reducedLattice hBQsym hBQ hsig hnd bs₀ hint₀ A F G h

/-- **Acceptance item 3 — the isotropic center `I(σ) = V_σ ∩ V_σ^⊥` of a plane member**: Definition
6.1, p. 28, at the member whose support space is `J_ℋ`. -/
theorem example64_isotropicCenter_planeMember
    (hBQsym : BQ.IsSymm)
    (hBQ : ∀ u w : V, (associated Q) (rationalPoint u) (rationalPoint w) = (BQ u w : ℝ))
    (hsig : sigPos Q = 2) (hnd : Q.Nondegenerate)
    {κ₀ : Type} [Finite κ₀] (bs₀ : Module.Basis κ₀ ℚ V)
    (hint₀ : ∀ x ∈ Submodule.span ℤ (Set.range bs₀), ∀ y ∈ Submodule.span ℤ (Set.range bs₀),
      ∃ n : ℤ, BQ x y = (n : ℚ))
    (A : FibreReducedLatticeInput (Q := Q) hBQsym (Submodule.span ℤ (Set.range bs₀)) ψ)
    (F : ConicalLine BQ Q) (G : ConicalPlane BQ) (h : F.line ≤ G.plane)
    (hcoh : G.IsPositiveAt F h) :
    (ConicalMember.plane F G h hcoh : ConicalMember BQ Q).isotropicCenter hBQsym
        (fun F => semifanArrangement ψ F) =
      JH (Q := Q) ψ G ⊓ LinearMap.BilinForm.orthogonal (associated Q) (JH (Q := Q) ψ G) := by
  have hv : ConicalMember.vSigma hBQsym (fun F => semifanArrangement ψ F)
      (ConicalMember.plane F G h hcoh) = JH (Q := Q) ψ G :=
    example64_vSigma_planeMember hBQsym hBQ hsig hnd bs₀ hint₀ A F G h hcoh
  rw [ConicalMember.isotropicCenter, hv]
  rfl

omit [Module.Finite ℚ V] in
omit [Module.Finite ℚ V] in
/-- **Acceptance item 3 — the isotropic center of a member of a fibre**: `V_σ ∩ V_σ^⊥` with `V_σ`
the span formula of Definition 6.1 (i). No hypothesis beyond the case. -/
theorem example64_isotropicCenter_fibreMember (hBsym : BQ.IsSymm) (F : ConicalLine BQ Q)
    {σ : PointedCone ℝ (realified ↥F.space)} (hσ : σ ≠ ⊥) :
    (ConicalMember.fibre F σ : ConicalMember BQ Q).isotropicCenter hBsym
        (fun F => semifanArrangement ψ F) =
      vSigma F σ ⊓ LinearMap.BilinForm.orthogonal (associated Q) (vSigma F σ) := by
  have hv : ConicalMember.vSigma hBsym (fun F => semifanArrangement ψ F)
      (ConicalMember.fibre F σ) = vSigma F σ :=
    example64_vSigma_fibreMember hBsym F hσ
  rw [ConicalMember.isotropicCenter, hv]
  rfl

omit [Module.Finite ℚ V] in
/-- **Acceptance item 4 — the example family `Σ(ℋ)`, member by member**: at the fibre of each
`ℚ`-isotropic line the members of `Σ(ℋ)` in `C_{I,+}` are the arrangement decomposition cut by the
traces of `ℋ` (Example 6.4, p. 29, read at the fibre of §1B). No hypothesis. -/
theorem example64_semifanArrangement (F : ConicalLine BQ Q) :
    semifanArrangement ψ F =
      arrangementDecomposition (fun i : fibreWalls ψ F => fibreFormC F (ψ ↑i)) F.closure :=
  rfl

/-- **Acceptance item 4 — the plane support of the example family**: `J_{Σ(ℋ)} = J_ℋ`, stated on the
family itself rather than at the member type. This is Example 6.4's equality, with
`semifanArrangement` and `sigmaSupportSpace` on one side and `J^⊥ ⊓ ⋂ {H : J ⊆ H}` on the other. -/
theorem example64_planeSupport
    (hBQsym : BQ.IsSymm)
    (hBQ : ∀ u w : V, (associated Q) (rationalPoint u) (rationalPoint w) = (BQ u w : ℝ))
    (hsig : sigPos Q = 2) (hnd : Q.Nondegenerate)
    {κ₀ : Type} [Finite κ₀] (bs₀ : Module.Basis κ₀ ℚ V)
    (hint₀ : ∀ x ∈ Submodule.span ℤ (Set.range bs₀), ∀ y ∈ Submodule.span ℤ (Set.range bs₀),
      ∃ n : ℤ, BQ x y = (n : ℚ))
    (A : FibreReducedLatticeInput (Q := Q) hBQsym (Submodule.span ℤ (Set.range bs₀)) ψ)
    (F : ConicalLine BQ Q) (G : ConicalPlane BQ) (h : F.line ≤ G.plane) :
    vSigmaPlane hBQsym F (semifanArrangement ψ F) G h = JH (Q := Q) ψ G :=
  vSigmaPlane_semifanArrangement_eq_JH_of_reducedLattice hBQsym hBQ hsig hnd bs₀ hint₀ A F G h

/-- **Acceptance item 4 — the plane support, spelled as the equality of the two definitions**:
`semifanArrangementTraces` under `sigmaSupportSpace` on the left, the source's
`J^⊥ ⊓ ⋂ {H ∈ ℋ : J ⊆ H}` on the right. The left-hand side is the `Σ`-support space of the half line
`C_{J,+}`, with the line `I`'s own span adjoined (`lineSpan`, the `I` summand of `V_σ` in
Definition 6.1 (ii)); the right-hand side is `planePerpQ G ⊓ ⋂ …`, i.e. `JH`. -/
theorem example64_planeSupport_spelled
    (hBQsym : BQ.IsSymm)
    (hBQ : ∀ u w : V, (associated Q) (rationalPoint u) (rationalPoint w) = (BQ u w : ℝ))
    (hsig : sigPos Q = 2) (hnd : Q.Nondegenerate)
    {κ₀ : Type} [Finite κ₀] (bs₀ : Module.Basis κ₀ ℚ V)
    (hint₀ : ∀ x ∈ Submodule.span ℤ (Set.range bs₀), ∀ y ∈ Submodule.span ℤ (Set.range bs₀),
      ∃ n : ℤ, BQ x y = (n : ℚ))
    (A : FibreReducedLatticeInput (Q := Q) hBQsym (Submodule.span ℤ (Set.range bs₀)) ψ)
    (F : ConicalLine BQ Q) (G : ConicalPlane BQ) (h : F.line ≤ G.plane) :
    lineSpan F ⊔
        (sigmaSupportSpace (positiveCone.upper (fibreForm Q F.space) F.sheet)
          (semifanArrangementTraces ψ F)
          (PointedCone.hull ℝ ({rationalPoint (fibreRay hBQsym F G h)} :
            Set (realified ↥F.space)))).map (realifyMap F.space) =
      planePerpQ (Q := Q) G ⊓
        ⨅ i : planeWalls ψ G, LinearMap.ker (realifiedFormC (ψ (i : ι))).toLinearMap := by
  rw [← sigmaSupportSpace_semifanArrangement_eq_traces]
  exact example64_planeSupport hBQsym hBQ hsig hnd bs₀ hint₀ A F G h

/-- **Item 1 connected to #169: Lemma 6.6, p. 30, case (i), for the assembled pair.** For a
subfamily `ℋ' ⊆ ℋ` (`hν`), the two arrangement decompositions are both admissible from the *same*
`FibreReducedLatticeInput` — the coarse family's input is the fine one's, since a subfamily's traces
are among `ℋ`'s (`htr` inside, no hypothesis) — and #169's `RefinesConicalLocus` holds for the pair
by `semifanArrangement_refinesConicalLocus` (containment *and* covering). So a member `σ` of `Σ(ℋ)`
that Definition 6.1 (i) covers has `V_σ ≤ V_{σ'}` for a member `σ'` of `Σ(ℋ')` whose carrier
contains it. -/
theorem example64_vSigma_le_of_subfamily
    {ι : Type*} {ψ : ι → V →ₗ[ℚ] ℚ} {ι' : Type*} {ψ' : ι' → V →ₗ[ℚ] ℚ} {ν : ι' → ι}
    (hBQsym : BQ.IsSymm)
    (hBQ : ∀ u w : V, (associated Q) (rationalPoint u) (rationalPoint w) = (BQ u w : ℝ))
    (hsig : sigPos Q = 2) (hnd : Q.Nondegenerate)
    {κ₀ : Type} [Finite κ₀] (bs₀ : Module.Basis κ₀ ℚ V)
    (hint₀ : ∀ x ∈ Submodule.span ℤ (Set.range bs₀), ∀ y ∈ Submodule.span ℤ (Set.range bs₀),
      ∃ n : ℤ, BQ x y = (n : ℚ))
    (A : FibreReducedLatticeInput (Q := Q) hBQsym (Submodule.span ℤ (Set.range bs₀)) ψ)
    (hν : ∀ i : ι', ψ' i = ψ (ν i))
    (hgamma : IsGammaInvariantLocus BQ Q Γ (semifanArrangement ψ))
    (hgamma' : IsGammaInvariantLocus BQ Q Γ (semifanArrangement ψ'))
    (F : ConicalLine BQ Q) {σ : PointedCone ℝ (realified ↥F.space)}
    (hσ : σ ∈ semifanArrangement ψ F) (hcase : IsCaseIFibre F σ) :
    ∃ (F' : ConicalLine BQ Q) (σ' : PointedCone ℝ (realified ↥F'.space)),
      σ' ∈ semifanArrangement ψ' F' ∧ vSigma F σ ≤ vSigma F' σ' := by
  have htr : ∀ F : ConicalLine BQ Q,
      distinctTraces ψ' F ⊆ orbitFamilyTraces BQ F (A.gen F) := by
    intro F T hT
    obtain ⟨i', hi'⟩ := mem_distinctTraces.1 hT
    refine A.traces F (mem_distinctTraces.2 ⟨fibreWallsMap (Q := Q) hν F i', ?_⟩)
    rw [← hi']
    change fibreTrace (ψ (ν i'.1)) F = fibreTrace (ψ' i'.1) F
    rw [hν i']
  let A' : FibreReducedLatticeInput (Q := Q) hBQsym (Submodule.span ℤ (Set.range bs₀)) ψ' :=
    { ΓI := A.ΓI, one_mem := A.one_mem, H₀ := A.H₀, gen := A.gen,
      lattice_stable := A.lattice_stable, isometry := A.isometry, generator := A.generator,
      traces := htr }
  exact vSigma_le_of_refinesConicalLocus hBQ hBQsym
    (example64_admissibleDecomposition hBQsym hBQ hsig hnd bs₀ hint₀ A hgamma)
    (example64_admissibleDecomposition hBQsym hBQ hsig hnd bs₀ hint₀ A' hgamma')
    (semifanArrangement_refinesConicalLocus hBQsym hν) F hσ hcase

omit [Module.Finite ℚ V] in
/-- **The zero and fibre-bottom presentations of the apex agree**, at #166's member type: the point
`{0}` of the conical locus, presented as the apex `ConicalMember.zero` and as the zero cone of a
fibre `ConicalMember.fibre F ⊥`, has **one** carrier, **one** support space and **one** isotropic
center.

This is the repair of the defect recorded by lean-categories#162 — the geometric member type at
`55966097` gave the two presentations the same carrier `{0}` and the *different* support spaces
`{0}` and `lineSpan F` — and the declarations that make it are #166's:
`ConicalMember.fibreVSigma`'s case at `σ = ⊥` (`ConicalMember.fibreVSigma_bot`), exported as
`ConicalMember.vSigma_fibre_bot`, `ConicalMember.carrier_fibre_bot` and
`ConicalMember.isotropicCenter_zero_member`. The assembly uses it rather than restating it: no
member of the conical locus now carries two support spaces. -/
theorem zero_presentation_agrees (hBsym : BQ.IsSymm) (F : ConicalLine BQ Q) :
    (ConicalMember.fibre F ⊥ : ConicalMember BQ Q).carrier hBsym =
        (ConicalMember.zero : ConicalMember BQ Q).carrier hBsym ∧
      (ConicalMember.fibre F ⊥ : ConicalMember BQ Q).vSigma hBsym
          (fun F => semifanArrangement ψ F) =
        (ConicalMember.zero : ConicalMember BQ Q).vSigma hBsym (fun F => semifanArrangement ψ F) ∧
      (ConicalMember.fibre F ⊥ : ConicalMember BQ Q).isotropicCenter hBsym
          (fun F => semifanArrangement ψ F) =
        (ConicalMember.zero : ConicalMember BQ Q).isotropicCenter hBsym
          (fun F => semifanArrangement ψ F) :=
  ⟨ConicalMember.carrier_fibre_bot hBsym F, ConicalMember.vSigma_fibre_bot hBsym _ F, by
    rw [ConicalMember.isotropicCenter_zero (hBsym := hBsym)
      (locus := fun F => semifanArrangement ψ F)]
    rw [ConicalMember.isotropicCenter, ConicalMember.vSigma_fibre_bot]
    simp [isotropicCenter]⟩

end Acceptance

end LeanCategories.Lattices.Valued
