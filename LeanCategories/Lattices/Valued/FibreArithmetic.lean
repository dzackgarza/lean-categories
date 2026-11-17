/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Lattices.Valued.SemifanArrangement

/-!
# The arithmetic fibre arrangement, from distinct traces

E. Looijenga, *Compactifications defined by arrangements II: locally symmetric varieties of
  type IV*, arXiv math/0201218v2 (2002), text version
  `.tmp-sources/looijenga-math0201218v2.md`:

* **Example 4.3 (b), pp. 17–18** (text line 487): "Let `H` be a collection of `ℚ`-hyperplanes of
  `L` which meet `C` such that the corresponding subset of the Grassmannian of `L` is a finite
  union of `Γ`-orbits. Then this collection is locally finite on `C` and decomposes `C₊` into the
  locally rational decomposition `Σ(H)`."
* **§1B, p. 11** (text line 245): "Suppose that `I` is a real isotropic line in `V`. Then the form
  on `I^⊥/I` induced by `φ` has signature `(1, n-1)`"; and at text line 269, for `I` defined over
  `ℚ`, "`Γ_{N_I}` defines a lattice in `I^⊥/I ⊗ I` (preserved by `Γ̄_I`, of course)". That lattice
  is `reducedLattice` of `SemifanArrangement`.
* **Example 6.4, p. 29** (text line 791): "the `H ∈ ℋ` containing `I` correspond to `ℚ`-hyperplanes
  in `I^⊥/I ⊗ I` of signature `(1, n-2)` and so according to example 4.3-b these decompose
  `C_{I,+}` into locally rational cones."

## Why the counting has to be about traces and not about indices

Example 4.3 (b) counts *Grassmannian points*: "the corresponding subset of the Grassmannian of `L`
is a finite union of `Γ`-orbits". A `ℚ`-hyperplane of `V` containing the isotropic line `I` is
determined by its trace in `I^⊥/I`, and **many** ambient hyperplanes have the same trace: with
`V = ℚe ⊕ ℚf ⊕ W`, `I = ℚe` and `T ⊂ W` a hyperplane, every `I ⊕ T ⊕ ℚ(f + k)`, `k ∉ I ⊕ T`, is a
`ℚ`-hyperplane containing `I` with trace `T`. So

* the ambient index set of `H` maps onto the traces with infinite fibres in general, and there is
  no `fibreWalls ψ F ≃ distinctTraces ψ F`;
* `CutsFinitelyOnRational F.closure (fun i : fibreWalls ψ F => fibreFormC F (ψ ↑i))` — the
  hypothesis the arrangement callers of `SemifanArrangement` carry, an index count — therefore
  fails for an infinite `H` as soon as one trace cuts, which is what Example 4.3 (b) is not saying.

What the source's count does give is that the *set of traces* which cut a rational cone is finite.
`CutsFinitelyOnTraces` below is that statement: a predicate on a `Set` of `ℚ`-hyperplanes of the
fibre, insensitive to how often an ambient family repeats a trace, and the counting lemma at the
reduced lattice (`cutsFinitelyOnTraces_orbitFamily`) derives it from the arithmetic data rather
than assuming it.

## What is here

* `fibreTrace`, `distinctTraces`, `traceProj`: the canonical set of distinct fibre traces and the
  surjection onto it from the ambient walls (`traceProj_surjective`).
* `exists_smul_of_fibreTrace_eq`: two ambient walls with the same trace have proportional trace
  forms — "scaling their normals".
* `arrangementCells_eq_of_surjective`, `arrangementDecomposition_eq_of_surjective`: **collapsing
  repeated trace hyperplanes does not change the arrangement**, for a surjection `ι → ι'` of index
  sets and nonzero scalars. This is the `fibreWalls ⇥ distinctTraces` form of
  `arrangementDecomposition_smul` and `arrangementDecomposition_reindex`.
* `semifanArrangementTraces` and `semifanArrangementTraces_eq`: `Σ(ℋ)` of Example 6.4 indexed by
  the fibre's own traces, equal to the ambient-indexed `semifanArrangement` of `SemifanArrangement`.
* `CutsFinitelyOnTraces`: the duplicate-insensitive counting interface;
  `cutsFinitelyOnRational_iff_cutsFinitelyOnTraces` reads it as `CutsFinitelyOnRational` of any
  trace-indexed family, so every consumer of the latter applies to it;
  `cutsFinitelyOnTraces_orbitFamily` derives it from the reduced lattice and the orbit family of
  §1B — no local-finiteness or counting certificate is assumed — and
  `cutsFinitelyOnRational_of_cutsFinitelyOnTraces` (with `_of_finite`) states exactly when the trace
  count implies the *ambient-indexed* count the existing consumers take: when no trace is repeated
  infinitely often. For an infinite `ℋ` that is what fails, and it is why the ambient count is not
  the source's hypothesis.
* `semifanArrangementTraces_isLocallyRational_of_orbitFamily`: condition (i) of Definition 6.1 for
  `Σ(ℋ)` at a fibre, from that arithmetic input alone.
* the half-line chain at an **actual isotropic ray** of the Lorentzian fibre
  (`semifanArrangementTraces_ray_meets`, `sigmaSupportSpace_ray_le_ker`,
  `iInf_traceKernel_le_span_of_member`,
  `sigmaSupportSpace_ray_le_traceKernels`, `sigmaSupportSpace_ray_eq`): the statements of
  `SemifanArrangement` that quantify over `ConicalPlane` — which is empty in the current
  development — are re-stated at a ray `ρ` of the fibre with `fibreForm Q F.space
  (rationalPoint ρ) = 0`, so that they rest on the fibre's own Lorentzian geometry.
* `sigmaSupportSpace_ray_eq`: **`J_{Σ(ℋ)} = J_ℋ` at an actual isotropic ray**, Example 6.4, p. 29 —
  the support space of the ray is the intersection of the kernel of its own metric dual with the
  common kernels `rayTraceKernels` of the distinct trace forms vanishing at it. The reverse
  inclusion is the source's Lemma-Definition 4.5 (`inf_ker_iInf_span_le_sigmaSupportSpace`, no
  minimal-member or local-finiteness input) fed by `iInf_traceKernel_le_span_of_member`; the trace
  count enters only through the nonemptiness of the support index, so an ambient family that repeats
  a wall infinitely often needs no finite-multiplicity premise.
-/

@[expose] public section

open PointedCone QuadraticMap

open scoped TensorProduct

namespace LeanCategories.Lattices.Valued

variable {V : Type} [AddCommGroup V] [Module ℚ V] [Module.Finite ℚ V]

/-! ## The trace of an ambient hyperplane on a fibre -/

section Trace

variable {BQ : LinearMap.BilinForm ℚ V} {Q : QuadraticForm ℝ (realified V)}

/-- **The trace of the hyperplane `ker ψ` on the fibre of `I`**, as a `ℚ`-subspace of the fibre's
carrier: the kernel of `ψ` restricted to `I^⊥/I`. Looijenga, Example 6.4, p. 29: "the `H ∈ ℋ`
containing `I` correspond to `ℚ`-hyperplanes in `I^⊥/I ⊗ I`". This is the *object* the source's
count is about; `fibreFormC F ψ` is one of its linear forms. -/
noncomputable def fibreTrace (ψ : V →ₗ[ℚ] ℚ) (F : ConicalLine BQ Q) :
    Submodule ℚ ↥F.space :=
  LinearMap.ker (ψ.comp F.space.subtype)

omit [Module.Finite ℚ V] in
@[simp] theorem mem_fibreTrace {ψ : V →ₗ[ℚ] ℚ} {F : ConicalLine BQ Q} {v : ↥F.space} :
    v ∈ fibreTrace ψ F ↔ ψ (v : V) = 0 :=
  Iff.rfl

omit [Module.Finite ℚ V] in
/-- The trace form vanishes at a rational point exactly on the trace. -/
theorem fibreFormC_eq_zero_iff {ψ : V →ₗ[ℚ] ℚ} {F : ConicalLine BQ Q} {v : ↥F.space} :
    fibreFormC F ψ (rationalPoint v) = 0 ↔ v ∈ fibreTrace ψ F := by
  rw [fibreFormC_apply, realifyMap_rationalPoint, realifiedForm_rationalPoint, mem_fibreTrace]
  exact ⟨fun h => by exact_mod_cast h, fun h => by rw [h]; norm_num⟩

variable {ι : Type*}

/-- **The distinct traces of a family of ambient hyperplanes at the fibre of `I`** — the image in
the Grassmannian of the fibre of the walls containing `I`, which is the set Example 4.3 (b), p. 18,
counts. It is a set, not an indexed family: an ambient family may repeat a trace. -/
noncomputable def distinctTraces (ψ : ι → V →ₗ[ℚ] ℚ) (F : ConicalLine BQ Q) :
    Set (Submodule ℚ ↥F.space) :=
  Set.range (fun i : fibreWalls ψ F => fibreTrace (ψ ↑i) F)

variable {ψ : ι → V →ₗ[ℚ] ℚ} {F : ConicalLine BQ Q}

omit [Module.Finite ℚ V] in
/-- Membership in the distinct traces is membership of the range. -/
theorem mem_distinctTraces {T : Submodule ℚ ↥F.space} :
    T ∈ distinctTraces ψ F ↔ ∃ i : fibreWalls ψ F, fibreTrace (ψ ↑i) F = T :=
  Iff.rfl

/-- **The map from the ambient walls containing `I` onto the distinct fibre traces.** -/
noncomputable def traceProj (ψ : ι → V →ₗ[ℚ] ℚ) (F : ConicalLine BQ Q) :
    fibreWalls ψ F → distinctTraces ψ F :=
  fun i => ⟨fibreTrace (ψ ↑i) F, mem_distinctTraces.2 ⟨i, rfl⟩⟩

omit [Module.Finite ℚ V] in
@[simp] theorem traceProj_val (ψ : ι → V →ₗ[ℚ] ℚ) (F : ConicalLine BQ Q) (i : fibreWalls ψ F) :
    (traceProj ψ F i).1 = fibreTrace (ψ ↑i) F := rfl

omit [Module.Finite ℚ V] in
/-- **The ambient walls containing `I` map onto the distinct traces.** Surjective and not
injective: `fibreWalls ψ F ≃ distinctTraces ψ F` is not available, and the arrangement statements
below are stated along this surjection. -/
theorem traceProj_surjective (ψ : ι → V →ₗ[ℚ] ℚ) (F : ConicalLine BQ Q) :
    Function.Surjective (traceProj ψ F) :=
  fun T => by
    obtain ⟨i, hi⟩ := mem_distinctTraces.1 T.2
    exact ⟨i, Subtype.ext hi⟩

omit [Module.Finite ℚ V] in
/-- **The distinct traces are the range of the trace map** (definitional record of
`distinctTraces`, used to compare with `Set.range` forms). -/
theorem distinctTraces_eq_range :
    distinctTraces ψ F = Set.range (fun i : fibreWalls ψ F => fibreTrace (ψ ↑i) F) := rfl

omit [Module.Finite ℚ V] in
/-- **The trace is *equivariant*, not invariant.** Composing a wall form with an isometry `g` of
`V` replaces the trace at `F` by the trace of `ψ` at the fibre `gF`, read back through `g`:
`fibreTrace (ψ ∘ g) F = F.space ∩ g⁻¹ (ker ψ)`.

No invariance of a trace under a `g` that moves the fibre is claimed or provable: `g` carries
`F.space` to `g(F.space)`, which is the carrier of the image fibre `gF` and not of `F`, so the two
traces live in different carriers and can only be compared through `g`. This is the exact form the
counting input of Looijenga, Example 4.3 (b), pp. 17–18, has at a fibre (Example 6.4, p. 29): the
walls in the `Γ`-orbit of a wall of the finite family are moved by `Γ`, so their traces at a
*fixed* `F` are the traces of the finitely many orbit representatives at the *moving* fibres `gF`,
and a statement that they are the traces at `F` itself is false whenever `Γ` is infinite. -/
theorem fibreTrace_comp (ψ : V →ₗ[ℚ] ℚ) (g : V ≃ₗ[ℚ] V) :
    fibreTrace (ψ.comp (g : V →ₗ[ℚ] V)) F =
      Submodule.comap F.space.subtype (Submodule.comap (g : V →ₗ[ℚ] V) (LinearMap.ker ψ)) := by
  ext x
  simp [fibreTrace, Submodule.mem_comap, LinearMap.mem_ker]

end Trace

/-! ## Proportionality of forms with the same trace -/

section Proportional

/-- **A form killed by the kernel of another is a multiple of it**: `ker f ≤ ker g` means `g`
vanishes wherever `f` does, and outside `ker f` the two are proportional. -/
theorem exists_smul_of_ker_le_ker {W : Type*} [AddCommGroup W] [Module ℚ W]
    {f g : W →ₗ[ℚ] ℚ} (h : LinearMap.ker f ≤ LinearMap.ker g) :
    ∃ c : ℚ, g = c • f := by
  classical
  by_cases hf : f = 0
  · rw [hf, LinearMap.ker_zero, top_le_iff, LinearMap.ker_eq_top] at h
    exact ⟨0, by rw [h, hf, smul_zero]⟩
  · obtain ⟨v, hv⟩ : ∃ v, f v ≠ 0 := by
      by_contra hcon
      rw [not_exists] at hcon
      exact hf (LinearMap.ext fun x => by simpa using hcon x)
    refine ⟨g v / f v, ?_⟩
    ext w
    have hw : w - (f w / f v) • v ∈ LinearMap.ker f := by
      rw [LinearMap.mem_ker, map_sub, map_smul, smul_eq_mul]
      field_simp
      ring
    have hwg : g (w - (f w / f v) • v) = 0 := h hw
    rw [map_sub, map_smul, smul_eq_mul] at hwg
    simp only [LinearMap.smul_apply, smul_eq_mul]
    field_simp at hwg ⊢
    linarith [hwg]

/-- **Two linear forms with equal kernel are nonzero multiples of each other.** -/
theorem exists_smul_of_ker_eq {W : Type*} [AddCommGroup W] [Module ℚ W]
    {f g : W →ₗ[ℚ] ℚ} (h : LinearMap.ker f = LinearMap.ker g) :
    ∃ c : ℚ, c ≠ 0 ∧ g = c • f := by
  obtain ⟨a, ha⟩ := exists_smul_of_ker_le_ker h.le
  rcases eq_or_ne a 0 with ha0 | ha0
  · have hg : g = 0 := by rw [ha, ha0, zero_smul]
    have hf : f = 0 := LinearMap.ker_eq_top.1 (by rw [h, hg, LinearMap.ker_zero])
    exact ⟨1, one_ne_zero, by rw [hg, hf, smul_zero]⟩
  · exact ⟨a, ha0, ha⟩

variable {BQ : LinearMap.BilinForm ℚ V} {Q : QuadraticForm ℝ (realified V)}

omit [Module.Finite ℚ V] in
/-- **Two linear forms on `V(ℝ)` that agree at the rational points are equal**: the rational points
span `V(ℝ)` (`span_range_rationalPoint`). -/
theorem linearMap_eq_of_rationalPoint_eq {L M : realified V →ₗ[ℝ] ℝ}
    (h : ∀ v : V, L (rationalPoint v) = M (rationalPoint v)) : L = M := by
  have hle : Submodule.span ℝ (Set.range (rationalPoint (V := V))) ≤
      LinearMap.ker (L - M) := by
    rw [Submodule.span_le]
    rintro - ⟨v, rfl⟩
    exact sub_eq_zero.2 (h v)
  rw [span_range_rationalPoint, top_le_iff] at hle
  refine LinearMap.ext fun x => ?_
  have hmem : x ∈ LinearMap.ker (L - M) := by rw [hle]; exact Submodule.mem_top
  have hx : (L - M) x = 0 := hmem
  exact sub_eq_zero.1 hx

omit [Module.Finite ℚ V] in
/-- The continuous form of `linearMap_eq_of_rationalPoint_eq`. -/
theorem continuousLinearMap_eq_of_rationalPoint_eq {L M : realified V →L[ℝ] ℝ}
    (h : ∀ v : V, L (rationalPoint v) = M (rationalPoint v)) : L = M := by
  have h' : L.toLinearMap = M.toLinearMap := linearMap_eq_of_rationalPoint_eq h
  exact ContinuousLinearMap.ext fun x => congrArg (fun f : realified V →ₗ[ℝ] ℝ => f x) h'

omit [Module.Finite ℚ V] in
/-- **The real extension of a `ℚ`-linear form is `ℚ`-homogeneous**: `c • ψ` extends to `c •` the
extension, since both sides agree on the rational points. -/
theorem realifiedForm_rat_smul (c : ℚ) (ψ : V →ₗ[ℚ] ℚ) :
    realifiedForm (c • ψ) = (c : ℝ) • realifiedForm ψ :=
  linearMap_eq_of_rationalPoint_eq fun v => by
    change realifiedForm (c • ψ) (rationalPoint v)
      = (c : ℝ) * realifiedForm ψ (rationalPoint v)
    rw [realifiedForm_rationalPoint, realifiedForm_rationalPoint]
    rw [LinearMap.smul_apply, smul_eq_mul]
    push_cast
    ring

omit [Module.Finite ℚ V] in
/-- The trace form is `ℚ`-homogeneous in the ambient form. -/
theorem fibreFormC_rat_smul (F : ConicalLine BQ Q) (c : ℚ) (ψ : V →ₗ[ℚ] ℚ) :
    fibreFormC F (c • ψ) = (c : ℝ) • fibreFormC F ψ := by
  refine continuousLinearMap_eq_of_rationalPoint_eq fun v => ?_
  change fibreFormC F (c • ψ) (rationalPoint v)
    = (c : ℝ) * fibreFormC F ψ (rationalPoint v)
  simp only [fibreFormC_apply, realifyMap_rationalPoint, realifiedForm_rationalPoint]
  rw [LinearMap.smul_apply, smul_eq_mul]
  push_cast
  ring

omit [Module.Finite ℚ V] in
/-- **The trace form depends only on the restriction of the ambient form to the fibre.** -/
theorem fibreFormC_congr {ψ ψ' : V →ₗ[ℚ] ℚ} (F : ConicalLine BQ Q)
    (h : ψ.comp F.space.subtype = ψ'.comp F.space.subtype) :
    fibreFormC F ψ = fibreFormC F ψ' := by
  refine continuousLinearMap_eq_of_rationalPoint_eq fun v => ?_
  simp only [fibreFormC_apply, realifyMap_rationalPoint, realifiedForm_rationalPoint]
  exact congrArg (fun φ : ↥F.space →ₗ[ℚ] ℚ => (((φ v : ℚ)) : ℝ)) h

omit [Module.Finite ℚ V] in
/-- **Two ambient walls with the same fibre trace have proportional trace forms** — Looijenga's
"scaling their normals": the trace is a hyperplane of the fibre, its form is defined up to a nonzero
scalar, and `exists_smul_of_ker_eq` supplies the scalar. -/
theorem exists_smul_of_fibreTrace_eq {ψ ψ' : V →ₗ[ℚ] ℚ} {F : ConicalLine BQ Q}
    (h : fibreTrace ψ F = fibreTrace ψ' F) :
    ∃ c : ℝ, c ≠ 0 ∧ fibreFormC F ψ' = c • fibreFormC F ψ := by
  obtain ⟨c, hc0, hc⟩ := exists_smul_of_ker_eq h
  refine ⟨(c : ℝ), by exact_mod_cast hc0, ?_⟩
  have hc' : ψ'.comp F.space.subtype = (c • ψ).comp F.space.subtype := by
    rw [hc, LinearMap.smul_comp]
  rw [fibreFormC_congr F hc', fibreFormC_rat_smul]
end Proportional


/-! ## Collapsing a repeated hyperplane does not change the arrangement

Example 4.3 (b), p. 18, counts hyperplanes of the Grassmannian, and Example 6.4, p. 29, runs that
count at the fibre: the walls of `Σ(ℋ)` at the fibre of `I` are the *traces* of the falling
hyperplanes, so an ambient family that repeats a trace with different normals describes the same
arrangement. This section proves it, along a surjection of index sets.

`signDown a` is the set of signs a real number can have under the weak sign condition `a` — with the
weak conditions of `mem_arrangementCone` that set is `{0, a}` — so collapsing a nonempty family of
weak conditions is a finite computation on `SignType`. -/

section SignCollapse

def weakSign (a : SignType) (r : ℝ) : Prop :=
  match a with
  | SignType.zero => r = 0
  | SignType.neg => r ≤ 0
  | SignType.pos => 0 ≤ r

def signDown (a : SignType) : Set SignType :=
  {s : SignType | s = 0 ∨ s = a}

theorem weakSign_of_sign {a : SignType} {r : ℝ} (h : SignType.sign r = a) : weakSign a r := by
  subst h
  rcases s : SignType.sign r with _ | _ | _
  · simpa [weakSign] using sign_eq_zero_iff.1 s
  · simpa [weakSign] using (sign_eq_neg_one_iff.1 s).le
  · simpa [weakSign] using (sign_eq_one_iff.1 s).le

theorem weakSign_iff_sign_mem {a : SignType} {r : ℝ} :
    weakSign a r ↔ SignType.sign r ∈ signDown a := by
  simp only [signDown, Set.mem_ofPred_eq]
  constructor
  · intro h
    rcases a with _ | _ | _
    · exact Or.inl (sign_eq_zero_iff.2 h)
    · rcases lt_or_eq_of_le h with h' | h'
      · exact Or.inr (sign_neg h')
      · exact Or.inl (sign_eq_zero_iff.2 h')
    · rcases lt_or_eq_of_le h with h' | h'
      · exact Or.inr (sign_pos h')
      · exact Or.inl (sign_eq_zero_iff.2 h'.symm)
  · rintro (h | h)
    · rw [sign_eq_zero_iff.1 h]
      rcases a with _ | _ | _ <;> simp [weakSign]
    · exact weakSign_of_sign h

theorem signDown_mul {u v a : SignType} (hu : u ≠ 0) :
    u * v ∈ signDown a ↔ v ∈ signDown (u * a) := by
  simp only [signDown, Set.mem_ofPred_eq]
  have hu0 : u * v = 0 ↔ v = 0 := by
    constructor
    · intro h
      rcases mul_eq_zero.1 h with h' | h'
      · exact absurd h' hu
      · exact h'
    · intro h; rw [h, mul_zero]
  constructor
  · rintro (h | h)
    · exact Or.inl (hu0.1 h)
    · refine Or.inr ?_
      have hu2 : u * u = 1 := by
        rcases u with _ | _ | _ <;> first | exact absurd rfl hu | rfl
      refine mul_left_cancel₀ hu ?_
      rw [h, ← mul_assoc, hu2, one_mul]
  · rintro (h | h)
    · exact Or.inl (hu0.2 h)
    · refine Or.inr ?_
      rw [h, ← mul_assoc]
      rcases u with _ | _ | _ <;> first | exact absurd rfl hu | simp

/-- The form of `signDown_mul` used when rewriting the condition of the *scaled* pattern: since a
nonzero sign is its own inverse, `u * v ∈ signDown (u * a) ↔ v ∈ signDown a`. -/
theorem signDown_mul' {u v a : SignType} (hu : u ≠ 0) :
    u * v ∈ signDown (u * a) ↔ v ∈ signDown a := by
  have hu2 : u * u = 1 := by
    rcases u with _ | _ | _ <;> first | exact absurd rfl hu | rfl
  have h := signDown_mul (u := u) (v := v) (a := u * a) hu
  rwa [← mul_assoc, hu2, one_mul] at h

theorem exists_signDown_forall {T : Set SignType} (hT : T.Nonempty) :
    ∃ b : SignType, ∀ v : SignType, (∀ a ∈ T, v ∈ signDown a) ↔ v ∈ signDown b := by
  simp only [signDown, Set.mem_ofPred_eq]
  by_cases h0 : (0 : SignType) ∈ T
  · exact ⟨0, fun v => ⟨fun h => h 0 h0, fun h _ _ => Or.inl (h.elim id id)⟩⟩
  by_cases hpos : (1 : SignType) ∈ T
  · by_cases hneg : (-1 : SignType) ∈ T
    · refine ⟨0, fun v => ⟨fun h => ?_, fun h _ _ => Or.inl (h.elim id id)⟩⟩
      rcases h 1 hpos with h1 | h1 <;> rcases h (-1) hneg with h2 | h2
      · exact Or.inl h1
      · exact absurd (h1.symm.trans h2) (by decide)
      · exact absurd (h2.symm.trans h1) (by decide)
      · exact absurd (h2.symm.trans h1) (by decide)
    · refine ⟨1, fun v => ⟨fun h => h 1 hpos, fun h a ha => ?_⟩⟩
      rcases h with h | h
      · exact Or.inl h
      · have ha1 : a = 1 := by
          rcases a with _ | _ | _
          · exact absurd ha h0
          · exact absurd ha hneg
          · rfl
        exact Or.inr (by rw [ha1]; exact h)
  · have hone : ∀ a ∈ T, a = -1 := by
      intro a ha
      rcases a with _ | _ | _
      · exact absurd ha h0
      · rfl
      · exact absurd ha hpos
    obtain ⟨a₀, ha₀⟩ := hT
    refine ⟨-1, fun v => ⟨fun h => h (-1) ?_, fun h a ha => ?_⟩⟩
    · rw [← hone a₀ ha₀]; exact ha₀
    · rw [hone a ha]; exact h

end SignCollapse

section ArrangementCollapse

variable {ι ι' : Type*} {φ : ι → (realified V) →L[ℝ] ℝ} {φ' : ι' → (realified V) →L[ℝ] ℝ}
  {j : ι → ι'} {c : ι → ℝ}

omit [Module.Finite ℚ V] in
/-- The weak sign conditions of `mem_arrangementCone`, as a single predicate. -/
theorem mem_arrangementCone_iff_weakSign {s : ι → SignType} {x : realified V} :
    x ∈ arrangementCone φ s ↔ ∀ i, weakSign (s i) (φ i x) := by
  rw [mem_arrangementCone]
  exact forall_congr' fun i => by rcases s i <;> exact Iff.rfl

omit [Module.Finite ℚ V] in
/-- **Collapsing repeated hyperplanes**: if `j : ι → ι'` is surjective and every form of the family
`φ` is a nonzero multiple of the form of `φ'` at its image, then every cell of `φ` is a cell of
`φ'`. The witness `s'` is the sign pattern whose condition at `i'` is the conjunction of the
conditions of the walls over `i'` (`exists_signDown_forall`). -/
theorem arrangementCone_exists_collapse (hj : Function.Surjective j) (hc : ∀ i, c i ≠ 0)
    (hφ : ∀ i, φ i = c i • φ' (j i)) (s : ι → SignType) :
    ∃ s' : ι' → SignType, arrangementCone φ s = arrangementCone φ' s' := by
  classical
  have hne : ∀ i' : ι',
      {a : SignType | ∃ i, j i = i' ∧ a = SignType.sign (c i) * s i}.Nonempty := by
    intro i'
    obtain ⟨i, hi⟩ := hj i'
    exact ⟨_, i, hi, rfl⟩
  choose b hb using fun i' => exists_signDown_forall (hne i')
  refine ⟨b, ?_⟩
  refine SetLike.ext fun x => ?_
  rw [mem_arrangementCone_iff_weakSign, mem_arrangementCone_iff_weakSign]
  have hvalue : ∀ i, φ i x = c i * φ' (j i) x := fun i => by rw [hφ i]; rfl
  constructor
  · intro h i'
    rw [weakSign_iff_sign_mem]
    refine (hb i' (SignType.sign (φ' i' x))).1 ?_
    rintro a ⟨i, hji, rfl⟩
    have hi := h i
    rw [hvalue i, weakSign_iff_sign_mem, sign_mul] at hi
    rw [hji] at hi
    exact (signDown_mul (sign_ne_zero_of_ne (hc i))).1 hi
  · intro h i
    rw [weakSign_iff_sign_mem, hvalue i, sign_mul]
    refine (signDown_mul (sign_ne_zero_of_ne (hc i))).2 ?_
    have hmem : SignType.sign (φ' (j i) x) ∈ signDown (b (j i)) := by
      rw [← weakSign_iff_sign_mem]
      exact h (j i)
    exact (hb (j i) _).2 hmem _ ⟨i, rfl, rfl⟩

omit [Module.Finite ℚ V] in
/-- **Collapsing repeated hyperplanes does not change the cells of the arrangement.** -/
theorem arrangementCells_eq_of_surjective (Cplus : PointedCone ℝ (realified V))
    (hj : Function.Surjective j) (hc : ∀ i, c i ≠ 0) (hφ : ∀ i, φ i = c i • φ' (j i)) :
    arrangementCells φ Cplus = arrangementCells φ' Cplus := by
  refine Set.Subset.antisymm ?_ ?_
  · rintro - ⟨s, rfl⟩
    obtain ⟨s', hs'⟩ := arrangementCone_exists_collapse (φ := φ) (φ' := φ') hj hc hφ s
    exact ⟨s', by rw [hs']⟩
  · rintro - ⟨s', rfl⟩
    refine ⟨fun i => SignType.sign (c i) * s' (j i), ?_⟩
    have hcones : arrangementCone φ (fun i => SignType.sign (c i) * s' (j i)) =
        arrangementCone φ' s' := by
      refine SetLike.ext fun x => ?_
      rw [mem_arrangementCone_iff_weakSign, mem_arrangementCone_iff_weakSign]
      have hvalue : ∀ i, φ i x = c i * φ' (j i) x := fun i => by rw [hφ i]; rfl
      have step : ∀ i, weakSign (SignType.sign (c i) * s' (j i)) (φ i x) ↔
          weakSign (s' (j i)) (φ' (j i) x) := by
        intro i
        rw [hvalue i, weakSign_iff_sign_mem, weakSign_iff_sign_mem, sign_mul]
        exact signDown_mul' (sign_ne_zero_of_ne (hc i))
      refine (forall_congr' step).trans ?_
      exact ⟨fun h i' => by obtain ⟨i, rfl⟩ := hj i'; exact h i, fun h i => h (j i)⟩
    rw [hcones]

omit [Module.Finite ℚ V] in
/-- **Collapsing repeated hyperplanes does not change the arrangement decomposition `Σ`**: the
face-closure of the cells, so `arrangementCells_eq_of_surjective` at once. This is the
`fibreWalls → distinctTraces` form of `arrangementDecomposition_smul` and
`arrangementDecomposition_reindex`. -/
theorem arrangementDecomposition_eq_of_surjective (Cplus : PointedCone ℝ (realified V))
    (hj : Function.Surjective j) (hc : ∀ i, c i ≠ 0) (hφ : ∀ i, φ i = c i • φ' (j i)) :
    arrangementDecomposition φ Cplus = arrangementDecomposition φ' Cplus := by
  rw [arrangementDecomposition, arrangementDecomposition,
    arrangementCells_eq_of_surjective Cplus hj hc hφ]

end ArrangementCollapse

/-! ## `Σ(ℋ)` at a fibre, indexed by the fibre's own traces

Looijenga, Example 6.4, p. 29: the walls of `Σ(ℋ)` in `C_{I,+}` are the traces on `I^⊥/I` of the
hyperplanes of `ℋ` containing `I`, and that is what Example 4.3 (b) decomposes. The ambient family
and the trace family give the same arrangement (`arrangementDecomposition_eq_of_surjective` along
`traceProj`, whose scalars are `exists_smul_of_fibreTrace_eq`), so `Σ(ℋ)` may be read either way;
what cannot be done is to read the *count* on the ambient index set. -/

section TraceArrangement

variable {BQ : LinearMap.BilinForm ℚ V} {Q : QuadraticForm ℝ (realified V)}
variable {ι : Type*} {ψ : ι → V →ₗ[ℚ] ℚ} {F : ConicalLine BQ Q}

/-- A representative ambient wall for a distinct trace. -/
noncomputable def traceRep (ψ : ι → V →ₗ[ℚ] ℚ) (F : ConicalLine BQ Q)
    (T : distinctTraces ψ F) : fibreWalls ψ F :=
  Classical.choose T.2

omit [Module.Finite ℚ V] in
theorem traceRep_spec (ψ : ι → V →ₗ[ℚ] ℚ) (F : ConicalLine BQ Q)
    (T : distinctTraces ψ F) : fibreTrace (ψ ↑(traceRep ψ F T)) F = T.1 :=
  Classical.choose_spec T.2

/-- **The trace form of a distinct trace**: the trace form of a representative wall. Independent of
the representative up to a nonzero scalar (`exists_smul_of_fibreTrace_eq`). -/
noncomputable def traceForm (ψ : ι → V →ₗ[ℚ] ℚ) (F : ConicalLine BQ Q)
    (T : distinctTraces ψ F) : realified ↥F.space →L[ℝ] ℝ :=
  fibreFormC F (ψ ↑(traceRep ψ F T))

/-- **`Σ(ℋ)` at a fibre of `I`, indexed by the fibre's own distinct traces.** -/
noncomputable def semifanArrangementTraces (ψ : ι → V →ₗ[ℚ] ℚ) (F : ConicalLine BQ Q) :
    Set (PointedCone ℝ (realified ↥F.space)) :=
  arrangementDecomposition (traceForm ψ F) F.closure

omit [Module.Finite ℚ V] in
/-- **The trace forms along the surjection are the walls up to a nonzero scalar** — "scaling their
normals". -/
theorem exists_smul_traceForm (ψ : ι → V →ₗ[ℚ] ℚ) (F : ConicalLine BQ Q) (i : fibreWalls ψ F) :
    ∃ c : ℝ, c ≠ 0 ∧ fibreFormC F (ψ ↑i) = c • traceForm ψ F (traceProj ψ F i) := by
  have hker : fibreTrace (ψ ↑(traceRep ψ F (traceProj ψ F i))) F =
      fibreTrace (ψ ↑i) F := by
    rw [traceRep_spec]
    rfl
  obtain ⟨c, hc0, hc⟩ := exists_smul_of_fibreTrace_eq hker
  exact ⟨c, hc0, hc⟩

omit [Module.Finite ℚ V] in
/-- **The arrangement of the distinct traces is the arrangement of the ambient walls**: Example 6.4,
p. 29, at a fibre, with the collapse of repeated traces and the scaling of their normals. -/
theorem semifanArrangementTraces_eq (ψ : ι → V →ₗ[ℚ] ℚ) (F : ConicalLine BQ Q) :
    semifanArrangementTraces ψ F = semifanArrangement ψ F := by
  classical
  refine (arrangementDecomposition_eq_of_surjective (Cplus := F.closure)
    (φ := fun i : fibreWalls ψ F => fibreFormC F (ψ ↑i)) (φ' := traceForm ψ F)
    (j := traceProj ψ F) (c := fun i => Classical.choose (exists_smul_traceForm ψ F i))
    (traceProj_surjective ψ F) (fun i => (Classical.choose_spec
      (exists_smul_traceForm ψ F i)).1) (fun i => (Classical.choose_spec
      (exists_smul_traceForm ψ F i)).2)).symm

end TraceArrangement

/-! ## The duplicate-insensitive counting interface

Example 4.3 (b), p. 18, counts *hyperplanes of the Grassmannian*: the set of traces which cut a
rational cone is finite. `CutsFinitelyOnTraces` is that statement; it is a predicate on a `Set` of
`ℚ`-hyperplanes of the fibre, so it cannot be defeated by an ambient family that repeats a trace.
`cutsFinitelyOnRational_iff_cutsFinitelyOnTraces` reads it as `CutsFinitelyOnRational` for any
family of trace forms indexed by the traces, which is the interface every consumer of the counting
in `SemifanArrangement` takes. -/

section TraceCounting

variable {BQ : LinearMap.BilinForm ℚ V} {Q : QuadraticForm ℝ (realified V)}
variable {F : ConicalLine BQ Q}

/-- **A `ℚ`-linear form on the fibre's carrier, as a continuous real form**: the base change of the
form to `ℝ ⊗_ℚ ↥F.space`, on which every linear form is continuous. This is the trace form of a
`ℚ`-hyperplane of the fibre without reference to an ambient container. -/
noncomputable def fibreTraceCLM (f : ↥F.space →ₗ[ℚ] ℚ) :
    realified ↥F.space →L[ℝ] ℝ :=
  ⟨realifiedForm f, IsModuleTopology.continuous_of_linearMap _⟩

omit [Module.Finite ℚ V] in
@[simp] theorem fibreTraceCLM_apply (f : ↥F.space →ₗ[ℚ] ℚ) (x : realified ↥F.space) :
    fibreTraceCLM f x = realifiedForm f x := rfl

omit [Module.Finite ℚ V] in
/-- **The trace form of an ambient wall is the real form of its restriction**: the identification of
the two descriptions of "the trace of `H` on `I^⊥/I`". -/
theorem fibreFormC_eq_fibreTraceCLM (ψ : V →ₗ[ℚ] ℚ) (F : ConicalLine BQ Q) :
    fibreFormC F ψ = fibreTraceCLM (ψ.comp F.space.subtype) := by
  refine continuousLinearMap_eq_of_rationalPoint_eq fun v => ?_
  rw [fibreFormC_apply, realifyMap_rationalPoint, realifiedForm_rationalPoint,
    fibreTraceCLM_apply, realifiedForm_rationalPoint]
  rfl

omit [Module.Finite ℚ V] in
/-- **A form cuts a cone iff it takes opposite signs at two of its points.** -/
theorem cutsOn_iff_exists_mul_neg {W : Type*} [AddCommGroup W] [Module ℚ W]
    (ψ : realified W →ₗ[ℝ] ℝ) (P : PointedCone ℝ (realified W)) :
    CutsOn ψ P ↔ ∃ x ∈ P, ∃ y ∈ P, ψ x * ψ y < 0 := by
  constructor
  · rintro ⟨⟨x, hx, hx0⟩, ⟨y, hy, hy0⟩⟩
    exact ⟨y, hy, x, hx, by nlinarith⟩
  · rintro ⟨x, hx, y, hy, hxy⟩
    have hx0 : ψ x ≠ 0 := by
      rintro h; rw [h, zero_mul] at hxy; exact absurd hxy (lt_irrefl 0)
    have hy0 : ψ y ≠ 0 := by
      rintro h; rw [h, mul_zero] at hxy; exact absurd hxy (lt_irrefl 0)
    rcases lt_or_gt_of_ne hx0 with hneg | hpos
    · exact ⟨⟨y, hy, by nlinarith⟩, ⟨x, hx, hneg⟩⟩
    · exact ⟨⟨x, hx, hpos⟩, ⟨y, hy, by nlinarith⟩⟩

omit [Module.Finite ℚ V] in
/-- **`CutsOn` is unchanged by a nonzero scalar**: the hyperplane and its two sides are unchanged,
so the trace of a hyperplane cuts independently of the normal representing it. -/
theorem cutsOn_smul {W : Type*} [AddCommGroup W] [Module ℚ W]
    {ψ : realified W →ₗ[ℝ] ℝ} {P : PointedCone ℝ (realified W)} {c : ℝ} (hc : c ≠ 0) :
    CutsOn (c • ψ) P ↔ CutsOn ψ P := by
  have hc2 : 0 < c * c := mul_self_pos.2 hc
  have hsl : ∀ x : realified W, (c • ψ) x = c * ψ x := fun x => by
    rw [LinearMap.smul_apply, smul_eq_mul]
  rw [cutsOn_iff_exists_mul_neg, cutsOn_iff_exists_mul_neg]
  refine ⟨fun ⟨x, hx, y, hy, h⟩ => ⟨x, hx, y, hy, ?_⟩,
    fun ⟨x, hx, y, hy, h⟩ => ⟨x, hx, y, hy, ?_⟩⟩
  · rw [hsl, hsl] at h
    nlinarith
  · rw [hsl, hsl]
    nlinarith

/-- **A trace of the fibre cuts a cone**: some `ℚ`-linear form with that kernel takes both signs on
it. By `cutsOn_smul` and `exists_smul_of_ker_eq` this depends only on the trace, not on the normal
chosen to represent it — which is what makes the count below insensitive to repeated traces. -/
def TraceCutsOn (F : ConicalLine BQ Q) (T : Submodule ℚ ↥F.space)
    (P : PointedCone ℝ (realified ↥F.space)) : Prop :=
  ∃ f : ↥F.space →ₗ[ℚ] ℚ, LinearMap.ker f = T ∧ CutsOn (fibreTraceCLM f).toLinearMap P

omit [Module.Finite ℚ V] in
/-- The cutting predicate at a form with the given kernel. -/
theorem traceCutsOn_iff {T : Submodule ℚ ↥F.space} {f : ↥F.space →ₗ[ℚ] ℚ}
    (hf : LinearMap.ker f = T) {P : PointedCone ℝ (realified ↥F.space)} :
    TraceCutsOn F T P ↔ CutsOn (fibreTraceCLM f).toLinearMap P := by
  constructor
  · rintro ⟨g, hg, hcut⟩
    have hkerg : LinearMap.ker f = LinearMap.ker g := by rw [hf, ← hg]
    obtain ⟨c, hc0, hc⟩ := exists_smul_of_ker_eq hkerg.symm
    have hclm : fibreTraceCLM f = (c : ℝ) • fibreTraceCLM g := by
      ext x
      rw [fibreTraceCLM_apply, hc, realifiedForm_rat_smul]
      rfl
    rw [hclm]
    exact (cutsOn_smul (ψ := (fibreTraceCLM g).toLinearMap) (P := P) (c := (c : ℝ))
      (show ((c : ℝ)) ≠ 0 by exact_mod_cast hc0)).2 hcut
  · exact fun h => ⟨f, hf, h⟩

/-- **The counting input of Example 4.3 (b), p. 18, on a set of traces**: of the traces in `S`, only
finitely many cut any given rational subcone of `C_{I,+}`. This is the source's statement — "the
corresponding subset of the Grassmannian of `L` is a finite union of `Γ`-orbits. Then this
collection is locally finite on `C`" — as a predicate on a `Set` of `ℚ`-hyperplanes of the fibre. -/
def CutsFinitelyOnTraces (F : ConicalLine BQ Q) (S : Set (Submodule ℚ ↥F.space)) : Prop :=
  ∀ P : PointedCone ℝ (realified ↥F.space), IsRationalCone P → P ≤ F.closure →
    {T : S | TraceCutsOn F T.1 P}.Finite

omit [Module.Finite ℚ V] in
/-- **The trace count is the index count of any family of trace forms indexed by the traces.** With
`traceForm` this reads `CutsFinitelyOnTraces` as the `CutsFinitelyOnRational` that every consumer of
the counting hypothesis in `SemifanArrangement` takes — so the consumers hold with the
duplicate-insensitive hypothesis, and note that the *ambient*-indexed count is a strictly stronger
statement, false for an infinite `ℋ` repeating a trace. -/
theorem cutsFinitelyOnRational_iff_cutsFinitelyOnTraces
    {S : Set (Submodule ℚ ↥F.space)} {φ : S → realified ↥F.space →L[ℝ] ℝ}
    (hφ : ∀ T : S, ∃ f : ↥F.space →ₗ[ℚ] ℚ, LinearMap.ker f = T.1 ∧
      φ T = fibreTraceCLM f) :
    CutsFinitelyOnRational F.closure φ ↔ CutsFinitelyOnTraces F S := by
  constructor
  · intro hcut P hP hPle
    have hset : {T : S | TraceCutsOn F T.1 P} = {T : S | CutsOn (φ T).toLinearMap P} := by
      ext T
      obtain ⟨f, hf, hφT⟩ := hφ T
      rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq, traceCutsOn_iff hf, hφT]
    rw [hset]
    exact hcut P hP hPle
  · intro hcut P hP hPle
    have hset : {T : S | CutsOn (φ T).toLinearMap P} = {T : S | TraceCutsOn F T.1 P} := by
      ext T
      obtain ⟨f, hf, hφT⟩ := hφ T
      rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq, traceCutsOn_iff hf, hφT]
    rw [hset]
    exact hcut P hP hPle

omit [Module.Finite ℚ V] in
/-- **The trace count of a subset is the trace count of the set.** -/
theorem CutsFinitelyOnTraces.mono {S S' : Set (Submodule ℚ ↥F.space)}
    (hcut : CutsFinitelyOnTraces F S') (hsub : S ⊆ S') :
    CutsFinitelyOnTraces F S := by
  intro P hP hPle
  refine Set.Finite.of_injOn (f := fun T : S => (⟨T.1, hsub T.2⟩ : S')) ?_ ?_ (hcut P hP hPle)
  · intro T hT
    exact hT
  · intro a _ b _ hab
    exact Subtype.ext (congrArg (fun T : S' => (T.1 : Submodule ℚ ↥F.space)) hab)

omit [Module.Finite ℚ V] in
/-- A finite ambient family has finitely many distinct traces. -/
theorem finite_distinctTraces {ι : Type*} [Finite ι] (ψ : ι → V →ₗ[ℚ] ℚ)
    (F : ConicalLine BQ Q) : (distinctTraces ψ F).Finite :=
  Set.finite_range _

omit [Module.Finite ℚ V] in
/-- **The trace count gives the ambient-indexed count when no trace is repeated infinitely often.**
This is the exact sense in which the duplicate-insensitive count *applies to the existing
`CutsFinitelyOnRational F.closure (fun i : fibreWalls ψ F => fibreFormC F (ψ ↑i))` consumers*: they
hold as soon as each trace has finitely many ambient walls over it. For an infinite `ℋ` that
condition is what fails, and with it the index count — not the source's statement, which counts
traces. -/
theorem cutsFinitelyOnRational_of_cutsFinitelyOnTraces {ι : Type*}
    (ψ : ι → V →ₗ[ℚ] ℚ) (F : ConicalLine BQ Q)
    (hcut : CutsFinitelyOnTraces F (distinctTraces ψ F))
    (hfib : ∀ T : distinctTraces ψ F,
      {i : fibreWalls ψ F | fibreTrace (ψ ↑i) F = T.1}.Finite) :
    CutsFinitelyOnRational F.closure (fun i : fibreWalls ψ F => fibreFormC F (ψ ↑i)) := by
  intro P hP hPle
  have hfinT : {T : distinctTraces ψ F | TraceCutsOn F T.1 P}.Finite := hcut P hP hPle
  have hcover : {i : fibreWalls ψ F | CutsOn (fibreFormC F (ψ ↑i)).toLinearMap P} ⊆
      ⋃ T ∈ {T : distinctTraces ψ F | TraceCutsOn F T.1 P},
        {i : fibreWalls ψ F | fibreTrace (ψ ↑i) F = T.1} := by
    intro i hi
    have hi' : CutsOn (fibreFormC F (ψ ↑i)).toLinearMap P := hi
    refine Set.mem_iUnion₂.2 ⟨traceProj ψ F i, ⟨(ψ ↑i).comp F.space.subtype, rfl, ?_⟩, rfl⟩
    rw [fibreFormC_eq_fibreTraceCLM] at hi'
    exact hi'
  exact Set.Finite.subset (hfinT.biUnion fun T _ => hfib T) hcover

omit [Module.Finite ℚ V] in
/-- **The trace count gives the ambient-indexed count for a finite ambient family**, where every
trace is repeated only finitely often. -/
theorem cutsFinitelyOnRational_of_cutsFinitelyOnTraces_of_finite {ι : Type*} [Finite ι]
    (ψ : ι → V →ₗ[ℚ] ℚ) (F : ConicalLine BQ Q)
    (hcut : CutsFinitelyOnTraces F (distinctTraces ψ F)) :
    CutsFinitelyOnRational F.closure (fun i : fibreWalls ψ F => fibreFormC F (ψ ↑i)) :=
  cutsFinitelyOnRational_of_cutsFinitelyOnTraces ψ F hcut
    fun _ => Set.Finite.subset (Set.toFinite _) (Set.subset_univ _)

end TraceCounting


/-! ## The counting input, derived from the reduced lattice

Looijenga §1B, p. 11, and Example 4.3 (b), p. 18, read at the fibre of `I`: the traces on `I^⊥/I`
of the hyperplanes of `ℋ` in the `Γ_I`-orbits of a finite `H₀` cut each rational subcone of
`C_{I,+}` finitely often, because the reduced lattice `(Λ ⊓ I^⊥)/(Λ ⊓ I)` and the integrality of
the fibre's form make the norms of the primitive generators take finitely many values
(`cutsFinitelyOnRational_reducedLattice`, #161/#162). What is added here is the step from that
*indexed* count to the trace-set count: the traces are the kernels of the normals' forms, so the
traces that cut are indexed injectively by the cutting lines of the orbit family. -/

section ReducedLatticeCount

variable {BQ : LinearMap.BilinForm ℚ V} {Q : QuadraticForm ℝ (realified V)}

/-- **The traces carried by a `Γ_I`-orbit family of normals** of the fibre: for each line `ℓ` of the
orbit family and its generator `g ℓ`, the `ℚ`-hyperplane `{w | g ℓ · w = 0}` of the reduced
lattice. -/
noncomputable def orbitFamilyTraces (BQ : LinearMap.BilinForm ℚ V) (F : ConicalLine BQ Q)
    {H₀ : Finset (Submodule ℚ ↥F.space)} {ΓI : Set (↥F.space ≃ₗ[ℚ] ↥F.space)}
    (gen : ↥(orbitFamily H₀ ΓI) → ↥F.space) : Set (Submodule ℚ ↥F.space) :=
  {T | ∃ ℓ : ↥(orbitFamily H₀ ΓI), T = LinearMap.ker (restrictBilinForm BQ F.space (gen ℓ))}

omit [Module.Finite ℚ V] in
/-- **The real form of the trace of a normal is the normal form**: the trace form of the hyperplane
`g^⊥` of the fibre is `normalForm (fibreForm) g`. -/
theorem fibreTraceCLM_restrictBilinForm
    (hBQ : ∀ u w : V, (associated Q) (rationalPoint u) (rationalPoint w) = (BQ u w : ℝ))
    (F : ConicalLine BQ Q) (w : ↥F.space) :
    fibreTraceCLM (restrictBilinForm BQ F.space w) = normalForm (fibreForm Q F.space) w := by
  refine continuousLinearMap_eq_of_rationalPoint_eq fun v => ?_
  rw [fibreTraceCLM_apply, realifiedForm_rationalPoint, normalForm_apply,
    associated_fibreForm_restrict hBQ F]

omit [Module.Finite ℚ V] in
/-- A trace that cuts a rational cone is a trace of the orbit family whose line cuts it. -/
theorem cutsOn_normalForm_of_traceCutsOn
    (hBQ : ∀ u w : V, (associated Q) (rationalPoint u) (rationalPoint w) = (BQ u w : ℝ))
    {F : ConicalLine BQ Q} {H₀ : Finset (Submodule ℚ ↥F.space)}
    {ΓI : Set (↥F.space ≃ₗ[ℚ] ↥F.space)}
    {gen : ↥(orbitFamily H₀ ΓI) → ↥F.space}
    {ℓ : ↥(orbitFamily H₀ ΓI)} {T : Submodule ℚ ↥F.space}
    (hT : T = LinearMap.ker (restrictBilinForm BQ F.space (gen ℓ)))
    {P : PointedCone ℝ (realified ↥F.space)} (hcut : TraceCutsOn F T P) :
    CutsOn (normalForm (fibreForm Q F.space) (gen ℓ)).toLinearMap P := by
  obtain ⟨f, hf, hcutf⟩ := hcut
  have hker : LinearMap.ker f = LinearMap.ker (restrictBilinForm BQ F.space (gen ℓ)) := by
    rw [hf, hT]
  obtain ⟨c, hc0, hc⟩ := exists_smul_of_ker_eq hker.symm
  have hclm0 : fibreTraceCLM f =
      (c : ℝ) • fibreTraceCLM (restrictBilinForm BQ F.space (gen ℓ)) := by
    ext x
    rw [fibreTraceCLM_apply, hc, realifiedForm_rat_smul]
    rfl
  have hclm : (fibreTraceCLM f).toLinearMap =
      (c : ℝ) • (normalForm (fibreForm Q F.space) (gen ℓ)).toLinearMap := by
    rw [hclm0, fibreTraceCLM_restrictBilinForm hBQ F (gen ℓ)]
    rfl
  rw [hclm] at hcutf
  exact (cutsOn_smul (ψ := (normalForm (fibreForm Q F.space) (gen ℓ)).toLinearMap) (P := P)
    (c := (c : ℝ)) (show ((c : ℝ)) ≠ 0 by exact_mod_cast hc0)).1 hcutf

set_option maxHeartbeats 1000000 in
-- The orbit family's count and the trace-to-line assignment both elaborate at the fibre's basis;
-- the default heartbeat budget is short for the pair.
/-- **Example 4.3 (b) at the fibre, on the set of traces**: the traces of a `Γ_I`-orbit family of
normals cut each rational subcone of `C_{I,+}` finitely often. The count is
`cutsFinitelyOnRational_reducedLattice` (`Λ` full and integral, `Γ_I` acting by isometries),
and the passage from the cutting lines of the orbit family to the cutting traces is
`cutsOn_normalForm_of_traceCutsOn`: two distinct traces have distinct normal lines, so the
trace-to-line assignment is injective on traces. -/
theorem cutsFinitelyOnTraces_orbitFamily
    (hBQsym : BQ.IsSymm)
    (hBQ : ∀ u w : V, (associated Q) (rationalPoint u) (rationalPoint w) = (BQ u w : ℝ))
    (hsig : sigPos Q = 2) (hnd : Q.Nondegenerate) (F : ConicalLine BQ Q)
    {κ₀ : Type} [Finite κ₀] (bs₀ : Module.Basis κ₀ ℚ V)
    (hint₀ : ∀ x ∈ Submodule.span ℤ (Set.range bs₀), ∀ y ∈ Submodule.span ℤ (Set.range bs₀),
      ∃ n : ℤ, BQ x y = (n : ℚ))
    {κ : Type} [Finite κ] (bs : Module.Basis κ ℚ ↥F.space)
    (hbs : Submodule.span ℤ (Set.range bs) =
      reducedLattice hBQsym F (Submodule.span ℤ (Set.range bs₀)))
    (ΓI : Set (↥F.space ≃ₗ[ℚ] ↥F.space))
    (hone : (1 : ↥F.space ≃ₗ[ℚ] ↥F.space) ∈ ΓI)
    (H₀ : Finset (Submodule ℚ ↥F.space))
    (hΓΛ : ∀ e ∈ ΓI, Submodule.map ((e : ↥F.space →ₗ[ℚ] ↥F.space).restrictScalars ℤ)
      (Submodule.span ℤ (Set.range bs)) = Submodule.span ℤ (Set.range bs))
    (hΓiso : ∀ e ∈ ΓI, ∀ x y : ↥F.space,
      restrictBilinForm BQ F.space (e x) (e y) = restrictBilinForm BQ F.space x y)
    (gen : ↥(orbitFamily H₀ ΓI) → ↥F.space)
    (hgen : ∀ ℓ : ↥(orbitFamily H₀ ΓI), gen ℓ ≠ 0 ∧
      Submodule.span ℤ (Set.range bs) ⊓ ℓ.1.restrictScalars ℤ =
        Submodule.span ℤ ({gen ℓ} : Set ↥F.space)) :
    CutsFinitelyOnTraces F (orbitFamilyTraces BQ F gen) := by
  classical
  have hcut := cutsFinitelyOnRational_reducedLattice hBQsym hBQ hsig hnd F bs₀ hint₀ bs hbs ΓI hone
    H₀ hΓΛ hΓiso gen hgen
  intro P hP hPle
  set S := orbitFamilyTraces BQ F gen with hS
  have hex : ∀ T : S, ∃ ℓ : ↥(orbitFamily H₀ ΓI),
      T.1 = LinearMap.ker (restrictBilinForm BQ F.space (gen ℓ)) := fun T => T.2
  choose L hL using hex
  have hfin : {ℓ : ↥(orbitFamily H₀ ΓI) |
      CutsOn (normalForm (fibreForm Q F.space) (gen ℓ)).toLinearMap P}.Finite :=
    hcut P hP hPle
  refine Set.Finite.of_injOn (f := L) ?_ ?_ hfin
  · intro T hT
    exact cutsOn_normalForm_of_traceCutsOn hBQ (hL T) hT
  · intro a _ b _ hab
    refine Subtype.ext ?_
    rw [hL a, hL b, hab]

end ReducedLatticeCount


/-! ## The half-line support chain at an actual isotropic ray of the fibre

`SemifanArrangement`'s support statements of Example 6.4 are stated for the half line `C_{J,+}` of
a `ConicalPlane`; the fibre-level content of them does not need the plane. Here the ray is a `ρ` of
the fibre with `fibreForm Q F.space (rationalPoint ρ) = 0`, `ρ ≠ 0` and nonnegative pairing with the
sheet — Looijenga §1B, p. 11: "the set of positive vectors is the union of a cone and its antipode.
But the choice of `D` now singles out one of these two cones". Every geometric input is then the
fibre's own Lorentzian geometry (`nonneg_associated_of_quadratic_eq_zero_of_mem_closedSheet`,
`associated_pos_of_mem_upper_of_mem_closedSheet`), and the only counting input is
`CutsFinitelyOnTraces`. -/

section RaySupport

variable {BQ : LinearMap.BilinForm ℚ V} {Q : QuadraticForm ℝ (realified V)}
variable {ι : Type*} {ψ : ι → V →ₗ[ℚ] ℚ} {F : ConicalLine BQ Q}

omit [Module.Finite ℚ V] in
/-- The cell of a sign pattern is a member of the trace arrangement. -/
theorem mem_semifanArrangementTraces_cell
    (s : distinctTraces ψ F → SignType) :
    arrangementCone (traceForm ψ F) s ⊓ F.closure ∈ semifanArrangementTraces ψ F :=
  mem_faceClosure.2 ⟨_, ⟨s, rfl⟩, PointedCone.IsFaceOf.rfl⟩

/-- **An isotropic rational point of the closed sheet lies in `C_{I,+}`**: it is a rational point of
the closed sheet, so in the convex hull of them. -/
theorem rationalPoint_mem_closure_of_isotropic
    (hpos : sigPos (fibreForm Q F.space) = 1) {ρ : ↥F.space}
    (hρ : fibreForm Q F.space (rationalPoint ρ) = 0)
    (hρsheet : 0 ≤ (associated (fibreForm Q F.space)) (rationalPoint ρ) F.sheet) :
    rationalPoint ρ ∈ F.closure := by
  rw [ConicalLine.closure_eq_closedSheet F hpos]
  exact mem_rationalClosure.2 (subset_convexHull ℝ _ ⟨⟨ρ, Set.mem_univ _, rfl⟩,
    subset_closure ((mem_closedSheet hpos F.sheet_pos).2 ⟨le_of_eq hρ.symm, hρsheet⟩)⟩)

/-- **The member of `Σ(ℋ)` above an actual isotropic ray meets the open cone `C_I`** — the fibre
form of `exists_mem_semifanArrangement_halfLine_meets`, with the ray a vector of the fibre instead
of a plane's half line. Only finitely many traces cut the rational cone `⟨r, v⟩`, so a point
`u = r + ε v` has the sign of `r` at every trace off `r`, and `r` lies in the cell of `u`'s sign
pattern. -/
theorem semifanArrangementTraces_ray_meets
    (hpos : sigPos (fibreForm Q F.space) = 1)
    (hnd : (fibreForm Q F.space).Nondegenerate)
    (hcut : CutsFinitelyOnRational F.closure (traceForm ψ F))
    {ρ : ↥F.space} (hρ : fibreForm Q F.space (rationalPoint ρ) = 0) (hρ0 : ρ ≠ 0)
    (hρsheet : 0 ≤ (associated (fibreForm Q F.space)) (rationalPoint ρ) F.sheet) :
    ∃ τ ∈ semifanArrangementTraces ψ F,
      PointedCone.hull ℝ ({rationalPoint ρ} : Set (realified ↥F.space)) ≤ τ ∧
      ((τ : Set (realified ↥F.space)) ∩
        positiveCone.upper (fibreForm Q F.space) F.sheet).Nonempty := by
  classical
  set r : realified ↥F.space := rationalPoint ρ with hrdef
  have hr_closed : r ∈ closedSheet (fibreForm Q F.space) hpos F.sheet_pos :=
    (mem_closedSheet hpos F.sheet_pos).2 ⟨le_of_eq hρ.symm, hρsheet⟩
  have hr_ne : r ≠ 0 := rationalPoint_ne_zero hρ0
  have hr_closure : r ∈ F.closure := rationalPoint_mem_closure_of_isotropic hpos hρ hρsheet
  obtain ⟨w, hwrange, hwU⟩ := dense_range_rationalPoint.exists_mem_open
    (isOpen_positiveCone_upper_of_moduleTopology (fibreForm Q F.space) F.sheet)
    ⟨F.sheet, F.sheet_pos, by rw [associated_self_apply]; exact F.sheet_pos⟩
  obtain ⟨v, rfl⟩ := hwrange
  have hv_closure : rationalPoint v ∈ F.closure := ConicalLine.upper_subset_closure F hpos hwU
  have hrv : 0 < (associated (fibreForm Q F.space)) r (rationalPoint v) := by
    rw [associated_comm]
    exact associated_pos_of_mem_upper_of_mem_closedSheet (fibreForm Q F.space) hpos hnd
      F.sheet_pos hwU hr_closed hr_ne
  set P : PointedCone ℝ (realified ↥F.space) :=
    PointedCone.hull ℝ ({r, rationalPoint v} : Set (realified ↥F.space)) with hPdef
  have hP_rat : IsRationalCone P := by
    refine ⟨{ρ, v}, ?_⟩
    rw [hPdef]
    congr 1
    ext x
    simp [hrdef]
  have hP_le : P ≤ F.closure := by
    rw [hPdef]
    refine Submodule.span_le.2 ?_
    rintro x (rfl | rfl)
    · exact hr_closure
    · exact hv_closure
  have hrP : r ∈ P := by
    rw [hPdef]; exact PointedCone.subset_hull (by simp)
  have hvP : rationalPoint v ∈ P := by
    rw [hPdef]; exact PointedCone.subset_hull (by simp)
  have hspos : ∀ᶠ ε : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0), (0 : ℝ) < ε :=
    self_mem_nhdsWithin
  have hUev : ∀ᶠ ε : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      r + ε • rationalPoint v ∈ positiveCone.upper (fibreForm Q F.space) F.sheet :=
    hspos.mono fun ε hε => by
      have hε0 : 0 < ε := hε
      have hvt : 0 < (associated (fibreForm Q F.space)) (rationalPoint v) F.sheet := hwU.2
      have hrt : 0 ≤ (associated (fibreForm Q F.space)) r F.sheet := by
        rw [hrdef]; exact hρsheet
      refine ⟨?_, ?_⟩
      · have hexp : (fibreForm Q F.space) (r + ε • rationalPoint v)
            = (fibreForm Q F.space) r
              + 2 * ε * (associated (fibreForm Q F.space)) r (rationalPoint v)
              + ε ^ 2 * (fibreForm Q F.space) (rationalPoint v) := by
          conv_lhs => rw [show r + ε • rationalPoint v = (1 : ℝ) • r + ε • rationalPoint v by
            rw [one_smul]]
          rw [quadratic_expand]
          ring
        rw [hexp, show (fibreForm Q F.space) r = 0 from hρ, zero_add]
        have h1 : 0 < ε ^ 2 * (fibreForm Q F.space) (rationalPoint v) :=
          mul_pos (pow_pos hε0 2) hwU.1
        have h2 : 0 < 2 * ε * (associated (fibreForm Q F.space)) r (rationalPoint v) :=
          mul_pos (by linarith) hrv
        linarith
      · rw [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
        nlinarith [hrt, hvt, hε0]
  obtain ⟨u, _, huU, hsign⟩ :=
    exists_mem_signPattern_eq_of_cutsFinitely (Cplus := F.closure) (P := P)
      hcut hP_rat hP_le hrP hvP _ hUev
  have hu_closure : u ∈ F.closure := ConicalLine.upper_subset_closure F hpos huU
  have hoff : ∀ T : distinctTraces ψ F, traceForm ψ F T u = 0 → traceForm ψ F T r = 0 := by
    intro T hi
    by_contra hne
    have hs : SignType.sign ((traceForm ψ F T) r) = 0 := by
      rw [← hsign T hne, hi, sign_zero]
    exact sign_ne_zero_of_ne hne hs
  have hrcone : r ∈ arrangementCone (traceForm ψ F) (signPattern (traceForm ψ F) u) :=
    mem_arrangementCone_signPattern_of_sign_eq hoff hsign
  have hucone : u ∈ arrangementCone (traceForm ψ F) (signPattern (traceForm ψ F) u) :=
    mem_arrangementCone_signPattern (traceForm ψ F) u
  refine ⟨arrangementCone (traceForm ψ F) (signPattern (traceForm ψ F) u) ⊓ F.closure,
    mem_semifanArrangementTraces_cell (ψ := ψ) (F := F) _, ?_, ⟨u, ⟨hucone, hu_closure⟩, huU⟩⟩
  refine Submodule.span_le.2 ?_
  rintro x hx
  rw [Set.mem_singleton_iff] at hx
  subst hx
  exact ⟨hrcone, hr_closure⟩

/-- **`J_{Σ(ℋ)} ⊆ ⟨r⟩^⊥` at an actual isotropic ray** — the `⟨ray⟩^⊥` half of Example 6.4, p. 29 at
the fibre: the support space of the ray is contained in the kernel of its own metric dual. The
metric dual of the ray is nonnegative on the fibre's closed sheet and vanishes at the isotropic
ray (`nonneg_associated_of_quadratic_eq_zero_of_mem_closedSheet`). -/
theorem sigmaSupportSpace_ray_le_ker
    (hpos : sigPos (fibreForm Q F.space) = 1)
    (hnd : (fibreForm Q F.space).Nondegenerate)
    (hcut : CutsFinitelyOnRational F.closure (traceForm ψ F))
    {ρ : ↥F.space} (hρ : fibreForm Q F.space (rationalPoint ρ) = 0) (hρ0 : ρ ≠ 0)
    (hρsheet : 0 ≤ (associated (fibreForm Q F.space)) (rationalPoint ρ) F.sheet) :
    sigmaSupportSpace (positiveCone.upper (fibreForm Q F.space) F.sheet)
        (semifanArrangementTraces ψ F)
        (PointedCone.hull ℝ ({rationalPoint ρ} : Set (realified ↥F.space))) ≤
      LinearMap.ker ((associated (fibreForm Q F.space)) (rationalPoint ρ)) := by
  obtain ⟨τ, hτmem, hτle, hτmeet⟩ :=
    semifanArrangementTraces_ray_meets (ψ := ψ) hpos hnd hcut hρ hρ0 hρsheet
  refine (sigmaSupportSpace_le hτmem hτle hτmeet).trans ?_
  obtain ⟨cell, hcell, hface⟩ := mem_faceClosure.1 hτmem
  obtain ⟨s, rfl⟩ := hcell
  have hτclos : τ ≤ F.closure := hface.le.trans inf_le_right
  exact supportSpace_le_ker_associated_of_isotropic (Q := fibreForm Q F.space) hpos F.sheet_pos
    hρ hρsheet rfl (hτclos.trans (closure_le_closedSheet F hpos))

/-- **The traces through the ray cut the member out**: the common kernel of the traces vanishing at
an actual isotropic ray is contained in the span of every member of `Σ(ℋ)` above the ray that meets
the open cone — the primal form of the description of a cell by its walls (Example 4.3 (b), p. 18),
at the trace arrangement. -/
theorem iInf_traceKernel_le_span_of_member
    (hpos : sigPos (fibreForm Q F.space) = 1)
    (hcut : CutsFinitelyOnRational F.closure (traceForm ψ F))
    {ρ : ↥F.space}
    (τ : supportIndex (positiveCone.upper (fibreForm Q F.space) F.sheet)
      (semifanArrangementTraces ψ F)
      (PointedCone.hull ℝ ({rationalPoint ρ} : Set (realified ↥F.space)))) :
    (⨅ T : {T : distinctTraces ψ F // traceForm ψ F T (rationalPoint ρ) = 0},
        LinearMap.ker (traceForm ψ F T.1).toLinearMap) ≤
      Submodule.span ℝ (τ.1 : Set (realified ↥F.space)) := by
  classical
  obtain ⟨σ, ⟨s, rfl⟩, hτσ⟩ := τ.2.1
  have hCsub : (positiveCone.upper (fibreForm Q F.space) F.sheet : Set (realified ↥F.space)) ⊆
      (F.closure : Set (realified ↥F.space)) := by
    rw [ConicalLine.closure_eq_closedSheet F hpos]
    exact upper_subset_rationalClosure_closedSheet hpos F.sheet_pos
  have hgen := le_span_of_isFaceOf_arrangementCone
    (φ := traceForm ψ F)
    (C := (positiveCone.upper (fibreForm Q F.space) F.sheet : Set (realified ↥F.space)))
    (isOpen_positiveCone_upper_of_moduleTopology (fibreForm Q F.space) F.sheet)
    (fun c hc x hx => positiveCone.smul_mem_upper (Q := fibreForm Q F.space) (t := F.sheet) hc hx)
    (zero_notMem_upper (fibreForm Q F.space) F.sheet) hCsub hcut hτσ τ.2.2.2
  refine (le_iInf fun j => ?_).trans hgen
  have hrayτ : rationalPoint ρ ∈ τ.1 :=
    τ.2.2.1 (Submodule.subset_span (Set.mem_singleton _))
  refine iInf_le_of_le ⟨j.1, ?_⟩ le_rfl
  have := j.2 hrayτ
  simpa [LinearMap.mem_ker] using this

section RayTraceKernels

omit [Module.Finite ℚ V]

/-- **The common kernel of the distinct trace forms vanishing at a point of the fibre** — the
`J_ℋ` side of Looijenga, Example 6.4, p. 29: `A = ⨅ {ker (traceForm T) | T ∈ distinctTraces,
T(r) = 0}`. It is written as its own definition because the intersection over the subtype of traces
is expensive to elaborate inside a longer statement. The intersection is over a *set* of traces, so
an ambient family that repeats a wall does not change it. -/
noncomputable def rayTraceKernels (ψ : ι → V →ₗ[ℚ] ℚ) (F : ConicalLine BQ Q) (ρ : ↥F.space) :
    Submodule ℝ (realified ↥F.space) :=
  ⨅ T : {T : distinctTraces ψ F // traceForm ψ F T (rationalPoint ρ) = 0},
    LinearMap.ker (traceForm ψ F T.1).toLinearMap

/-- **`J_{Σ(ℋ)} ⊆ J_ℋ` at an actual isotropic ray, wall by wall**: the support space of the ray
inside one member `τ` of `Σ(ℋ)` is contained in the kernel of the trace form of every distinct
trace vanishing at the ray. This is `supportSpace_halfLine_le_ker` (Looijenga, Example 6.4, p. 29)
with the fibre's own trace index and a vector of the Lorentzian fibre in place of a `ConicalPlane`:
the member is a face of a sign cell, so the trace form is one-signed on it — where the sign is zero
the form vanishes on the whole member, and elsewhere the form or its negative is nonnegative on `τ`
and zero on the ray, so it is a form of `supportForms τ ⟨r⟩`. -/
theorem supportSpace_ray_le_traceKernel
    {ρ : ↥F.space}
    (τ : supportIndex (positiveCone.upper (fibreForm Q F.space) F.sheet)
      (semifanArrangementTraces ψ F)
      (PointedCone.hull ℝ ({rationalPoint ρ} : Set (realified ↥F.space))))
    (T : distinctTraces ψ F) (hT : traceForm ψ F T (rationalPoint ρ) = 0) :
    supportSpace τ.1 (PointedCone.hull ℝ ({rationalPoint ρ} : Set (realified ↥F.space))) ≤
      LinearMap.ker (traceForm ψ F T).toLinearMap := by
  classical
  have hmem : τ.1 ∈ faceClosure (arrangementCells (traceForm ψ F) F.closure) := τ.2.1
  obtain ⟨cell, hcell, hface⟩ := mem_faceClosure.1 hmem
  obtain ⟨s, rfl⟩ := hcell
  have hle : τ.1 ≤ arrangementCone (traceForm ψ F) s ⊓ F.closure := hface.le
  have hvan : ∀ x ∈ PointedCone.hull ℝ ({rationalPoint ρ} : Set (realified ↥F.space)),
      traceForm ψ F T x = 0 := by
    intro x hx
    obtain ⟨c, -, rfl⟩ := PointedCone.mem_hull_singleton.1 hx
    rw [ContinuousLinearMap.map_smul, smul_eq_mul, hT, mul_zero]
  have hsign : ∀ x ∈ τ.1, match s T with
      | SignType.zero => traceForm ψ F T x = 0
      | SignType.neg => traceForm ψ F T x ≤ 0
      | SignType.pos => 0 ≤ traceForm ψ F T x := by
    intro x hx
    exact (mem_arrangementCone (traceForm ψ F)).1 (Submodule.mem_inf.1 (hle hx)).1 T
  rcases hs : s T with _ | _ | _
  · have hΨ : (traceForm ψ F T).toLinearMap ∈
        supportForms τ.1 (PointedCone.hull ℝ ({rationalPoint ρ} : Set (realified ↥F.space))) := by
      refine mem_supportForms.2 ⟨fun x hx => ?_, fun x hx => ?_⟩
      · have hx' := hsign x hx
        simp only [hs] at hx'
        simpa using hx'.ge
      · simpa using hvan x hx
    exact iInf_le (fun φ : supportForms τ.1 (PointedCone.hull ℝ
      ({rationalPoint ρ} : Set (realified ↥F.space))) =>
      LinearMap.ker (φ : (realified ↥F.space) →ₗ[ℝ] ℝ)) ⟨_, hΨ⟩
  · have hΨ : -((traceForm ψ F T).toLinearMap) ∈
        supportForms τ.1 (PointedCone.hull ℝ ({rationalPoint ρ} : Set (realified ↥F.space))) := by
      refine mem_supportForms.2 ⟨fun x hx => ?_, fun x hx => ?_⟩
      · have hx' := hsign x hx
        simp only [hs] at hx'
        change 0 ≤ -(traceForm ψ F T x)
        linarith
      · change -(traceForm ψ F T x) = 0
        rw [hvan x hx, neg_zero]
    refine le_trans (iInf_le (fun φ : supportForms τ.1 (PointedCone.hull ℝ
      ({rationalPoint ρ} : Set (realified ↥F.space))) =>
      LinearMap.ker (φ : (realified ↥F.space) →ₗ[ℝ] ℝ)) ⟨_, hΨ⟩) ?_
    rw [LinearMap.ker_neg]
  · have hΨ : (traceForm ψ F T).toLinearMap ∈
        supportForms τ.1 (PointedCone.hull ℝ ({rationalPoint ρ} : Set (realified ↥F.space))) := by
      refine mem_supportForms.2 ⟨fun x hx => ?_, fun x hx => ?_⟩
      · have hx' := hsign x hx
        simp only [hs] at hx'
        simpa using hx'
      · simpa using hvan x hx
    exact iInf_le (fun φ : supportForms τ.1 (PointedCone.hull ℝ
      ({rationalPoint ρ} : Set (realified ↥F.space))) =>
      LinearMap.ker (φ : (realified ↥F.space) →ₗ[ℝ] ℝ)) ⟨_, hΨ⟩

end RayTraceKernels

/-- **`J_{Σ(ℋ)} ⊆ J_ℋ` at an actual isotropic ray** — the half of Example 6.4, p. 29 that the
traces supply: the support space of the ray is contained in the common kernel of the trace forms of
the distinct traces vanishing at it. The index is a `Set` of traces, so this is the duplicate-free
statement; it holds without any finiteness premise on the ambient walls, and the only counting input
is `CutsFinitelyOnTraces`-derived — the existence of one member above the ray through the open cone
(`semifanArrangementTraces_ray_meets`) — which is what makes the support-space index nonempty. -/
theorem sigmaSupportSpace_ray_le_traceKernels
    (hpos : sigPos (fibreForm Q F.space) = 1)
    (hnd : (fibreForm Q F.space).Nondegenerate)
    (hcut : CutsFinitelyOnRational F.closure (traceForm ψ F))
    {ρ : ↥F.space} (hρ : fibreForm Q F.space (rationalPoint ρ) = 0) (hρ0 : ρ ≠ 0)
    (hρsheet : 0 ≤ (associated (fibreForm Q F.space)) (rationalPoint ρ) F.sheet) :
    sigmaSupportSpace (positiveCone.upper (fibreForm Q F.space) F.sheet)
        (semifanArrangementTraces ψ F)
        (PointedCone.hull ℝ ({rationalPoint ρ} : Set (realified ↥F.space))) ≤
      rayTraceKernels ψ F ρ := by
  obtain ⟨τ, hτmem, hτle, hτmeet⟩ :=
    semifanArrangementTraces_ray_meets (ψ := ψ) hpos hnd hcut hρ hρ0 hρsheet
  rw [rayTraceKernels]
  refine (sigmaSupportSpace_le hτmem hτle hτmeet).trans (le_iInf fun T => ?_)
  exact supportSpace_ray_le_traceKernel ⟨τ, hτmem, hτle, hτmeet⟩ T.1 T.2

/-- **Looijenga, Example 6.4, p. 29, at an actual isotropic ray of the fibre:
`J_{Σ(ℋ)} = J_ℋ`.** For a nonzero isotropic ray `r = ρ` of the Lorentzian fibre, the support space
of `r` in `Σ(ℋ)` is the intersection of the kernel of its own metric dual `B(r, -)` with the common
kernels of the distinct trace forms vanishing at `r`:

  `J_{Σ(ℋ),r} = ker B(r, -) ⊓ ⨅ {ker (traceForm T) | T ∈ distinctTraces, T(r) = 0}`.

Both inclusions are now available: the two upper bounds are `sigmaSupportSpace_ray_le_ker` and
`sigmaSupportSpace_ray_le_traceKernels`, and the reverse inclusion combines the memberwise primal
bound `iInf_traceKernel_le_span_of_member` with the source's reverse inclusion for a locally
rational decomposition, `inf_ker_iInf_span_le_sigmaSupportSpace` (Lemma-Definition 4.5, p. 19),
which needs no minimal-member or local-finiteness witness. The trace count enters only through the
nonemptiness of the support index, so an ambient family that repeats a wall infinitely often costs
nothing. -/
theorem sigmaSupportSpace_ray_eq
    (hpos : sigPos (fibreForm Q F.space) = 1)
    (hnd : (fibreForm Q F.space).Nondegenerate)
    (hcut : CutsFinitelyOnRational F.closure (traceForm ψ F))
    (hS : IsLocallyRationalDecomposition F.closure (semifanArrangementTraces ψ F))
    {ρ : ↥F.space} (hρ : fibreForm Q F.space (rationalPoint ρ) = 0) (hρ0 : ρ ≠ 0)
    (hρsheet : 0 ≤ (associated (fibreForm Q F.space)) (rationalPoint ρ) F.sheet) :
    sigmaSupportSpace (positiveCone.upper (fibreForm Q F.space) F.sheet)
        (semifanArrangementTraces ψ F)
        (PointedCone.hull ℝ ({rationalPoint ρ} : Set (realified ↥F.space))) =
      LinearMap.ker ((associated (fibreForm Q F.space)) (rationalPoint ρ)) ⊓
        rayTraceKernels ψ F ρ := by
  refine le_antisymm
    (le_inf (sigmaSupportSpace_ray_le_ker (ψ := ψ) hpos hnd hcut hρ hρ0 hρsheet)
      (sigmaSupportSpace_ray_le_traceKernels (ψ := ψ) hpos hnd hcut hρ hρ0 hρsheet)) ?_
  have hS' : IsLocallyRationalDecomposition
      (rationalClosure (closedSheet (fibreForm Q F.space) hpos F.sheet_pos))
      (semifanArrangementTraces ψ F) := by
    rw [← ConicalLine.closure_eq_closedSheet F hpos]
    exact hS
  have heC : rationalPoint ρ ∈
      rationalClosure (closedSheet (fibreForm Q F.space) hpos F.sheet_pos) := by
    rw [← ConicalLine.closure_eq_closedSheet F hpos]
    exact rationalPoint_mem_closure_of_isotropic hpos hρ hρsheet
  have hA : rayTraceKernels ψ F ρ ≤
      ⨅ τ : supportIndex (positiveCone.upper (fibreForm Q F.space) F.sheet)
        (semifanArrangementTraces ψ F)
        (PointedCone.hull ℝ ({rationalPoint ρ} : Set (realified ↥F.space))),
        Submodule.span ℝ (τ.1 : Set (realified ↥F.space)) := by
    rw [rayTraceKernels]
    exact le_iInf fun τ => iInf_traceKernel_le_span_of_member (ψ := ψ) hpos hcut τ
  refine (inf_le_inf_left _ hA).trans ?_
  exact inf_ker_iInf_span_le_sigmaSupportSpace (Q := fibreForm Q F.space) (t := F.sheet)
    (e := rationalPoint ρ) (ht := F.sheet_pos) hpos hnd (rationalPoint_ne_zero hρ0) hρ heC hS'

end RaySupport


/-! ## The fibre-level caller: condition (i) and the support chain from arithmetic only

The hypotheses are the source's: the ambient form is defined over `ℚ` and of signature `(2, n)`
(`hBQ`, `hsig`), the fibre is a `ℚ`-isotropic line `I` of `Λ` with the reduced lattice
`(Λ ⊓ I^⊥)/(Λ ⊓ I)` full and integral (`bs`, `hbs`, `hint₀`), `Γ_I` acts on it by lattice
isomorphisms and isometries (`hΓΛ`, `hΓiso`), and the traces of the walls at `I` are the fibres of
a `Γ_I`-orbit family of `ℚ`-hyperplanes with primitive generators (`hsub` against
`orbitFamilyTraces`). Nothing else: no local-finiteness, no trace equivalence, no local-rationality
certificate. -/

section ArithmeticCaller

variable {BQ : LinearMap.BilinForm ℚ V} {Q : QuadraticForm ℝ (realified V)}
variable {ι : Type*}

/-- **Condition (i) of Definition 6.1 for `Σ(ℋ)` at a fibre, from the arithmetic input alone.** The
members of `Σ(ℋ)` in `C_{I,+}` are the cells of the distinct traces of `ℋ` at `I`, and they are a
locally rational decomposition because Example 4.3 (b) at the reduced lattice counts the cutting
traces — `cutsFinitelyOnTraces_orbitFamily` — with no counting hypothesis carried. -/
theorem semifanArrangementTraces_isLocallyRational_of_orbitFamily
    (hBQsym : BQ.IsSymm)
    (hBQ : ∀ u w : V, (associated Q) (rationalPoint u) (rationalPoint w) = (BQ u w : ℝ))
    (hsig : sigPos Q = 2) (hnd : Q.Nondegenerate) (F : ConicalLine BQ Q)
    {κ₀ : Type} [Finite κ₀] (bs₀ : Module.Basis κ₀ ℚ V)
    (hint₀ : ∀ x ∈ Submodule.span ℤ (Set.range bs₀), ∀ y ∈ Submodule.span ℤ (Set.range bs₀),
      ∃ n : ℤ, BQ x y = (n : ℚ))
    {κ : Type} [Finite κ] (bs : Module.Basis κ ℚ ↥F.space)
    (hbs : Submodule.span ℤ (Set.range bs) =
      reducedLattice hBQsym F (Submodule.span ℤ (Set.range bs₀)))
    (ΓI : Set (↥F.space ≃ₗ[ℚ] ↥F.space))
    (hone : (1 : ↥F.space ≃ₗ[ℚ] ↥F.space) ∈ ΓI)
    (H₀ : Finset (Submodule ℚ ↥F.space))
    (hΓΛ : ∀ e ∈ ΓI, Submodule.map ((e : ↥F.space →ₗ[ℚ] ↥F.space).restrictScalars ℤ)
      (Submodule.span ℤ (Set.range bs)) = Submodule.span ℤ (Set.range bs))
    (hΓiso : ∀ e ∈ ΓI, ∀ x y : ↥F.space,
      restrictBilinForm BQ F.space (e x) (e y) = restrictBilinForm BQ F.space x y)
    (gen : ↥(orbitFamily H₀ ΓI) → ↥F.space)
    (hgen : ∀ ℓ : ↥(orbitFamily H₀ ΓI), gen ℓ ≠ 0 ∧
      Submodule.span ℤ (Set.range bs) ⊓ ℓ.1.restrictScalars ℤ =
        Submodule.span ℤ ({gen ℓ} : Set ↥F.space))
    (ψ : ι → V →ₗ[ℚ] ℚ)
    (hsub : distinctTraces ψ F ⊆ orbitFamilyTraces BQ F gen) :
    IsLocallyRationalDecomposition F.closure (semifanArrangementTraces ψ F) := by
  classical
  have hpos : sigPos (fibreForm Q F.space) = 1 :=
    sigPos_fibreForm_eq_one hBQ hBQsym hsig F
  have hndF : (fibreForm Q F.space).Nondegenerate :=
    fibreForm_space_nondegenerate hBQ hBQsym hnd F
  have hsal : (F.closure : ConvexCone ℝ (realified ↥F.space)).Salient := by
    rw [ConicalLine.closure_eq_closedSheet F hpos]
    exact salient_rationalClosure hpos hndF F.sheet_pos
  have hφ : ∀ T : distinctTraces ψ F, IsRationalForm (traceForm ψ F T).toLinearMap :=
    fun T => isRationalForm_fibreFormC F (ψ ↑(traceRep ψ F T))
  have htraces : CutsFinitelyOnTraces F (distinctTraces ψ F) :=
    (cutsFinitelyOnTraces_orbitFamily hBQsym hBQ hsig hnd F bs₀ hint₀ bs hbs ΓI hone H₀ hΓΛ hΓiso
      gen hgen).mono hsub
  have hcut : CutsFinitelyOnRational F.closure (traceForm ψ F) := by
    refine (cutsFinitelyOnRational_iff_cutsFinitelyOnTraces (F := F) ?_).2 htraces
    intro T
    exact ⟨(ψ ↑(traceRep ψ F T)).comp F.space.subtype, traceRep_spec ψ F T,
      fibreFormC_eq_fibreTraceCLM (ψ ↑(traceRep ψ F T)) F⟩
  exact arrangementDecomposition_isLocallyRational hsal hφ hcut

/-- **Condition (i) of Definition 6.1 for `Σ(ℋ)` at a fibre**, in the ambient-indexed form of
`semifanArrangement`: the same statement, transported across `semifanArrangementTraces_eq`. -/
theorem semifanArrangement_isLocallyRational_of_orbitFamily
    (hBQsym : BQ.IsSymm)
    (hBQ : ∀ u w : V, (associated Q) (rationalPoint u) (rationalPoint w) = (BQ u w : ℝ))
    (hsig : sigPos Q = 2) (hnd : Q.Nondegenerate) (F : ConicalLine BQ Q)
    {κ₀ : Type} [Finite κ₀] (bs₀ : Module.Basis κ₀ ℚ V)
    (hint₀ : ∀ x ∈ Submodule.span ℤ (Set.range bs₀), ∀ y ∈ Submodule.span ℤ (Set.range bs₀),
      ∃ n : ℤ, BQ x y = (n : ℚ))
    {κ : Type} [Finite κ] (bs : Module.Basis κ ℚ ↥F.space)
    (hbs : Submodule.span ℤ (Set.range bs) =
      reducedLattice hBQsym F (Submodule.span ℤ (Set.range bs₀)))
    (ΓI : Set (↥F.space ≃ₗ[ℚ] ↥F.space))
    (hone : (1 : ↥F.space ≃ₗ[ℚ] ↥F.space) ∈ ΓI)
    (H₀ : Finset (Submodule ℚ ↥F.space))
    (hΓΛ : ∀ e ∈ ΓI, Submodule.map ((e : ↥F.space →ₗ[ℚ] ↥F.space).restrictScalars ℤ)
      (Submodule.span ℤ (Set.range bs)) = Submodule.span ℤ (Set.range bs))
    (hΓiso : ∀ e ∈ ΓI, ∀ x y : ↥F.space,
      restrictBilinForm BQ F.space (e x) (e y) = restrictBilinForm BQ F.space x y)
    (gen : ↥(orbitFamily H₀ ΓI) → ↥F.space)
    (hgen : ∀ ℓ : ↥(orbitFamily H₀ ΓI), gen ℓ ≠ 0 ∧
      Submodule.span ℤ (Set.range bs) ⊓ ℓ.1.restrictScalars ℤ =
        Submodule.span ℤ ({gen ℓ} : Set ↥F.space))
    (ψ : ι → V →ₗ[ℚ] ℚ)
    (hsub : distinctTraces ψ F ⊆ orbitFamilyTraces BQ F gen) :
    IsLocallyRationalDecomposition F.closure (semifanArrangement ψ F) := by
  rw [← semifanArrangementTraces_eq]
  exact semifanArrangementTraces_isLocallyRational_of_orbitFamily hBQsym hBQ hsig hnd F bs₀ hint₀
    bs hbs ΓI hone H₀ hΓΛ hΓiso gen hgen ψ hsub

/-- **The fibre-level caller of Example 6.4, p. 29.** One arithmetic input (the traces of `ℋ` at `I`
lie in the `Γ_I`-orbit family of the reduced lattice) gives, at the fibre:

* condition (i) of Definition 6.1: the members of `Σ(ℋ)` in `C_{I,+}` are a locally rational
  decomposition;
* `J_{Σ(ℋ),r} ⊆ ⟨r⟩^⊥` for an actual isotropic ray `r = ρ` of the fibre;
* the common kernel of the traces through `r` lies in the span of every member above `r` meeting the
  open cone — the primal form of the description of a member by its walls, which is the half of
  `J_{Σ(ℋ)} = J_ℋ` that needs the counting;
* that equality itself, `J_{Σ(ℋ),r} = ker B(r, -) ∩ rayTraceKernels`.

No local-finiteness, trace-equivalence or local-rationality certificate is supplied, and the ray is
a vector of the Lorentzian fibre rather than a `ConicalPlane`. -/
theorem semifanArrangement_arithmetic_fibre
    (hBQsym : BQ.IsSymm)
    (hBQ : ∀ u w : V, (associated Q) (rationalPoint u) (rationalPoint w) = (BQ u w : ℝ))
    (hsig : sigPos Q = 2) (hnd : Q.Nondegenerate) (F : ConicalLine BQ Q)
    {κ₀ : Type} [Finite κ₀] (bs₀ : Module.Basis κ₀ ℚ V)
    (hint₀ : ∀ x ∈ Submodule.span ℤ (Set.range bs₀), ∀ y ∈ Submodule.span ℤ (Set.range bs₀),
      ∃ n : ℤ, BQ x y = (n : ℚ))
    {κ : Type} [Finite κ] (bs : Module.Basis κ ℚ ↥F.space)
    (hbs : Submodule.span ℤ (Set.range bs) =
      reducedLattice hBQsym F (Submodule.span ℤ (Set.range bs₀)))
    (ΓI : Set (↥F.space ≃ₗ[ℚ] ↥F.space))
    (hone : (1 : ↥F.space ≃ₗ[ℚ] ↥F.space) ∈ ΓI)
    (H₀ : Finset (Submodule ℚ ↥F.space))
    (hΓΛ : ∀ e ∈ ΓI, Submodule.map ((e : ↥F.space →ₗ[ℚ] ↥F.space).restrictScalars ℤ)
      (Submodule.span ℤ (Set.range bs)) = Submodule.span ℤ (Set.range bs))
    (hΓiso : ∀ e ∈ ΓI, ∀ x y : ↥F.space,
      restrictBilinForm BQ F.space (e x) (e y) = restrictBilinForm BQ F.space x y)
    (gen : ↥(orbitFamily H₀ ΓI) → ↥F.space)
    (hgen : ∀ ℓ : ↥(orbitFamily H₀ ΓI), gen ℓ ≠ 0 ∧
      Submodule.span ℤ (Set.range bs) ⊓ ℓ.1.restrictScalars ℤ =
        Submodule.span ℤ ({gen ℓ} : Set ↥F.space))
    (ψ : ι → V →ₗ[ℚ] ℚ)
    (hsub : distinctTraces ψ F ⊆ orbitFamilyTraces BQ F gen)
    {ρ : ↥F.space} (hρ : fibreForm Q F.space (rationalPoint ρ) = 0) (hρ0 : ρ ≠ 0)
    (hρsheet : 0 ≤ (associated (fibreForm Q F.space)) (rationalPoint ρ) F.sheet) :
    IsLocallyRationalDecomposition F.closure (semifanArrangement ψ F) ∧
      sigmaSupportSpace (positiveCone.upper (fibreForm Q F.space) F.sheet)
          (semifanArrangementTraces ψ F)
          (PointedCone.hull ℝ ({rationalPoint ρ} : Set (realified ↥F.space))) ≤
        LinearMap.ker ((associated (fibreForm Q F.space)) (rationalPoint ρ)) ∧
      (∀ τ : supportIndex (positiveCone.upper (fibreForm Q F.space) F.sheet)
          (semifanArrangementTraces ψ F)
          (PointedCone.hull ℝ ({rationalPoint ρ} : Set (realified ↥F.space))),
        (⨅ T : {T : distinctTraces ψ F // traceForm ψ F T (rationalPoint ρ) = 0},
            LinearMap.ker (traceForm ψ F T.1).toLinearMap) ≤
          Submodule.span ℝ (τ.1 : Set (realified ↥F.space))) ∧
      sigmaSupportSpace (positiveCone.upper (fibreForm Q F.space) F.sheet)
          (semifanArrangementTraces ψ F)
          (PointedCone.hull ℝ ({rationalPoint ρ} : Set (realified ↥F.space))) =
        LinearMap.ker ((associated (fibreForm Q F.space)) (rationalPoint ρ)) ⊓
          rayTraceKernels ψ F ρ := by
  classical
  have hpos : sigPos (fibreForm Q F.space) = 1 :=
    sigPos_fibreForm_eq_one hBQ hBQsym hsig F
  have hndF : (fibreForm Q F.space).Nondegenerate :=
    fibreForm_space_nondegenerate hBQ hBQsym hnd F
  have htraces : CutsFinitelyOnTraces F (distinctTraces ψ F) :=
    (cutsFinitelyOnTraces_orbitFamily hBQsym hBQ hsig hnd F bs₀ hint₀ bs hbs ΓI hone H₀ hΓΛ hΓiso
      gen hgen).mono hsub
  have hcut : CutsFinitelyOnRational F.closure (traceForm ψ F) := by
    refine (cutsFinitelyOnRational_iff_cutsFinitelyOnTraces (F := F) ?_).2 htraces
    intro T
    exact ⟨(ψ ↑(traceRep ψ F T)).comp F.space.subtype, traceRep_spec ψ F T,
      fibreFormC_eq_fibreTraceCLM (ψ ↑(traceRep ψ F T)) F⟩
  have hloc : IsLocallyRationalDecomposition F.closure (semifanArrangementTraces ψ F) :=
    semifanArrangementTraces_isLocallyRational_of_orbitFamily hBQsym hBQ hsig hnd F bs₀ hint₀ bs
      hbs ΓI hone H₀ hΓΛ hΓiso gen hgen ψ hsub
  refine ⟨?_, sigmaSupportSpace_ray_le_ker (ψ := ψ) hpos hndF hcut hρ hρ0 hρsheet,
    fun τ => iInf_traceKernel_le_span_of_member (ψ := ψ) hpos hcut τ, ?_⟩
  · rw [← semifanArrangementTraces_eq]
    exact hloc
  · exact sigmaSupportSpace_ray_eq (ψ := ψ) hpos hndF hcut hloc hρ hρ0 hρsheet

end ArithmeticCaller


/-! ## The induced action of the line stabilizer, and the trace normals

Looijenga §1B, p. 11 (text line 265): "The stabilizer `G_I` acts on `I^⊥/I ⊗ I` with image `Ḡ_I`
the group of real orthogonal transformations of `I^⊥/I ⊗ I` that preserve `C_I`. The kernel `N_I`
of this action consists of the transformations in `G_I` that act trivially on `I^⊥/I ⊗ I`", and at
text line 269, for `I` defined over `ℚ`: "`Γ_I` is arithmetic in `G_I`. This implies that `Γ_{N_I}`
defines a lattice in `I^⊥/I ⊗ I` (preserved by `Ḡ_I`, of course)". That is the source's `Γ̄_I` and
`N_I`, and it is what Example 6.4, p. 29 uses at the fibre: the walls containing `I` are moved by
`Γ_I` and their traces by `Γ̄_I`.

The carrier of the fibre is the complement model `planeComplement BQ F.gen F.partner` of
`I^⊥/I` (`ConicalLine.space`). `fibreCarrierProj` is the projection of `V` onto that model along
the hyperbolic plane `⟨gen, partner⟩`; an isometry carrying `gen` to a nonzero multiple of itself
acts on the model by `x ↦ fibreCarrierProj (g x)`, a `ℚ`-linear equivalence of the carrier, and it
fixes the carrier pointwise exactly when it displaces every vector of `I^⊥` by a multiple of the
isotropic generator — the source's `N_I` read on the model. -/

section InducedAction

variable {BQ : LinearMap.BilinForm ℚ V} {Q : QuadraticForm ℝ (realified V)}

/-- **The projection of `V` onto the complement model `I^⊥/I` along the hyperbolic plane
`⟨gen, partner⟩`**: `v - (v · partner) gen - (v · gen) partner`. The two corrections are the ones
that make the result pair trivially with `gen` and with `partner`; for `v ∈ I^⊥` the second
vanishes, and that is the projection of §1B, p. 11 used at the fibre. -/
noncomputable def fibreCarrierProj (hBsym : BQ.IsSymm) (F : ConicalLine BQ Q) :
    V →ₗ[ℚ] ↥F.space where
  toFun v := ⟨v - BQ F.partner v • F.gen - BQ F.gen v • F.partner, by
    have hpp : BQ F.partner F.gen = 1 := by rw [hBsym.eq]; exact F.pairing
    rw [mem_planeComplement_iff]
    refine ⟨?_, ?_⟩
    · simp only [map_sub, map_smul, smul_eq_mul, F.gen_iso, F.pairing, hpp, mul_zero, mul_one]
      ring
    · simp only [map_sub, map_smul, smul_eq_mul, F.pairing, F.partner_iso, hpp, mul_one, mul_zero]
      ring⟩
  map_add' u v := by
    refine Subtype.ext ?_
    simp only [map_add, add_smul, Submodule.coe_add, Submodule.coe_mk]
    abel
  map_smul' c v := by
    refine Subtype.ext ?_
    simp only [map_smul, smul_sub, smul_smul, Submodule.coe_smul, Submodule.coe_mk,
      RingHom.id_apply]
    module

omit [Module.Finite ℚ V] in
@[simp] theorem fibreCarrierProj_apply (hBsym : BQ.IsSymm) (F : ConicalLine BQ Q) (v : V) :
    ((fibreCarrierProj hBsym F v : ↥F.space) : V) =
      v - BQ F.partner v • F.gen - BQ F.gen v • F.partner := rfl

omit [Module.Finite ℚ V] in
/-- The projection kills the isotropic generator: `π gen = 0` in the model. -/
theorem fibreCarrierProj_gen (hBsym : BQ.IsSymm) (F : ConicalLine BQ Q) :
    fibreCarrierProj hBsym F F.gen = 0 := by
  refine Subtype.ext ?_
  have hpp : BQ F.partner F.gen = 1 := by rw [hBsym.eq]; exact F.pairing
  simp [fibreCarrierProj_apply, F.gen_iso, hpp]

omit [Module.Finite ℚ V] in
/-- The projection kills the hyperbolic partner as well: `π partner = 0`. With
`fibreCarrierProj_gen` this says that the whole hyperbolic plane `⟨gen, partner⟩` is the kernel of
the projection. -/
theorem fibreCarrierProj_partner (hBsym : BQ.IsSymm) (F : ConicalLine BQ Q) :
    fibreCarrierProj hBsym F F.partner = 0 := by
  refine Subtype.ext ?_
  have hpp : BQ F.partner F.gen = 1 := by rw [hBsym.eq]; exact F.pairing
  simp [fibreCarrierProj_apply, F.partner_iso, F.pairing]

omit [Module.Finite ℚ V] in
/-- The projection fixes the model pointwise. -/
theorem fibreCarrierProj_eq_self (hBsym : BQ.IsSymm) (F : ConicalLine BQ Q) (x : ↥F.space) :
    fibreCarrierProj hBsym F (x : V) = x := by
  refine Subtype.ext ?_
  rw [fibreCarrierProj_apply]
  have hx := (mem_planeComplement_iff BQ).1 x.2
  rw [hx.1, hx.2]
  simp

omit [Module.Finite ℚ V] in
/-- **Two vectors that differ by a multiple of the isotropic generator have the same projection**:
`π` is the quotient map `I^⊥ → I^⊥/I` in the complement model, so it sees vectors only modulo
`ℚ gen`. -/
theorem fibreCarrierProj_eq_of_sub_mem_span (hBsym : BQ.IsSymm) (F : ConicalLine BQ Q) {v w : V}
    (h : v - w ∈ Submodule.span ℚ ({F.gen} : Set V)) :
    fibreCarrierProj hBsym F v = fibreCarrierProj hBsym F w := by
  have hker : Submodule.span ℚ ({F.gen} : Set V) ≤ LinearMap.ker (fibreCarrierProj hBsym F) := by
    rw [Submodule.span_le]
    rintro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    simpa using fibreCarrierProj_gen hBsym F
  have hzero : fibreCarrierProj hBsym F (v - w) = 0 := LinearMap.mem_ker.1 (hker h)
  rw [map_sub] at hzero
  exact sub_eq_zero.1 hzero

omit [Module.Finite ℚ V] in
/-- **The trace form of a wall is the normal form of the projected normal.** For a wall whose form
is the normal form of `v`, the trace form on the fibre is the normal form of the projection `π v`:
on the model the two forms agree because every point of the carrier pairs with `gen` and with
`partner` trivially. -/
theorem fibreFormC_eq_normalForm_proj
    (hBQ : ∀ u w : V, (associated Q) (rationalPoint u) (rationalPoint w) = (BQ u w : ℝ))
    (hBsym : BQ.IsSymm) (F : ConicalLine BQ Q) (v : V) :
    fibreFormC F (BQ v) = normalForm (fibreForm Q F.space) (fibreCarrierProj hBsym F v) := by
  refine continuousLinearMap_eq_of_rationalPoint_eq fun x => ?_
  rw [fibreFormC_eq_fibreTraceCLM, fibreTraceCLM_apply, realifiedForm_rationalPoint]
  have hproj : BQ ((fibreCarrierProj hBsym F v : ↥F.space) : V) (x : V) = BQ v (x : V) := by
    rw [fibreCarrierProj_apply]
    have hx := (mem_planeComplement_iff BQ).1 x.2
    simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul,
      hx.1, hx.2, mul_zero, sub_zero]
  rw [normalForm_apply, associated_fibreForm_restrict hBQ F, restrictBilinForm_apply, hproj]
  rfl

omit [Module.Finite ℚ V] in
/-- **The trace of a wall is the kernel of the normal form of its projected normal**: the form
statement above, read on kernels. -/
theorem fibreTrace_eq_ker_restrictBilinForm_proj (hBsym : BQ.IsSymm) (F : ConicalLine BQ Q)
    (v : V) :
    LinearMap.ker (restrictBilinForm BQ F.space (fibreCarrierProj hBsym F v) : ↥F.space →ₗ[ℚ] ℚ) =
      LinearMap.ker ((BQ v).comp F.space.subtype) := by
  ext x
  rw [LinearMap.mem_ker, LinearMap.mem_ker, restrictBilinForm_apply]
  have hproj : BQ ((fibreCarrierProj hBsym F v : ↥F.space) : V) (x : V) = BQ v (x : V) := by
    rw [fibreCarrierProj_apply]
    have hx := (mem_planeComplement_iff BQ).1 x.2
    simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul,
      hx.1, hx.2, mul_zero, sub_zero]
  rw [hproj]
  rfl

omit [Module.Finite ℚ V] in
omit [Module.Finite ℚ V] in
/-- **The induced action, composed with its inverse, is the identity**: `π (g (π (g⁻¹ x))) = x`.
Both terms of the projection of `g⁻¹ x` collapse except the `gen` correction — `π` kills `gen`
(`fibreCarrierProj_gen`), and `BQ gen (g⁻¹ x) = BQ (g gen) x = c · BQ gen x = 0` for `x` in the
carrier — so `g (π (g⁻¹ x))` and `x` differ by a multiple of the isotropic generator, which
`fibreCarrierProj_eq_of_sub_mem_span` cannot see. -/
theorem fibreCarrierProj_comp_symm (hBsym : BQ.IsSymm) (F : ConicalLine BQ Q) (g : V ≃ₗ[ℚ] V)
    (c : ℚ) (hgen : g F.gen = c • F.gen)
    (hgiso : ∀ x y : V, BQ (g x) (g y) = BQ x y) (x : ↥F.space) :
    fibreCarrierProj hBsym F
      (g ((fibreCarrierProj hBsym F (g.symm (x : V)) : ↥F.space) : V)) = x := by
  have hx : BQ F.gen (g.symm (x : V)) = 0 := by
    have hiso : BQ (g F.gen) (x : V) = BQ F.gen (g.symm (x : V)) := by
      rw [← hgiso F.gen (g.symm (x : V))]
      simp
    have hx0 : BQ F.gen (x : V) = 0 := ((mem_planeComplement_iff BQ).1 x.2).1
    rw [← hiso, hgen]
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, hx0, mul_zero]
  refine (fibreCarrierProj_eq_of_sub_mem_span hBsym F ?_).trans
    (fibreCarrierProj_eq_self hBsym F x)
  have hval : ((fibreCarrierProj hBsym F (g.symm (x : V)) : ↥F.space) : V) =
      g.symm (x : V) - BQ F.partner (g.symm (x : V)) • F.gen := by
    rw [fibreCarrierProj_apply, hx, zero_smul, sub_zero]
  rw [hval, map_sub, map_smul, LinearEquiv.apply_symm_apply, hgen, smul_smul]
  rw [show (x : V) - (BQ F.partner (g.symm (x : V)) * c) • F.gen - x
      = (-(BQ F.partner (g.symm (x : V)) * c)) • F.gen by module]
  exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton _))

omit [Module.Finite ℚ V] in
/-- **The induced action of a line-preserving isometry on the fibre carrier** — the source's
`Γ_I → Γ̄_I` (§1B, p. 11, text lines 265–269). An isometry `g` with `g gen = c gen` (`c ≠ 0`) acts
on the complement model by `x ↦ π (g x)`; the inverse is `y ↦ π (g⁻¹ y)`, and both inverse laws are
`fibreCarrierProj_comp_symm`, once for `g` and once for `g⁻¹`. Nothing here needs `g` to preserve
the *partner* of the fibre, so this is the action of the line stabilizer `Γ_I` and not of a plane
stabilizer. -/
noncomputable def fibreInducedEquiv (hBsym : BQ.IsSymm) (F : ConicalLine BQ Q)
    (g : V ≃ₗ[ℚ] V) (c : ℚ) (hgen : g F.gen = c • F.gen) (hc : c ≠ 0)
    (hgiso : ∀ x y : V, BQ (g x) (g y) = BQ x y) :
    ↥F.space ≃ₗ[ℚ] ↥F.space where
  toFun x := fibreCarrierProj hBsym F (g x)
  invFun y := fibreCarrierProj hBsym F (g.symm y)
  map_add' x y := by simp only [Submodule.coe_add, map_add]
  map_smul' a x := by simp only [Submodule.coe_smul, map_smul, RingHom.id_apply]
  left_inv x := by
    have hgen' : g.symm F.gen = c⁻¹ • F.gen := by
      refine g.injective ?_
      rw [LinearEquiv.apply_symm_apply, map_smul, hgen, smul_smul, inv_mul_cancel₀ hc, one_smul]
    have hgiso' : ∀ x y : V, BQ (g.symm x) (g.symm y) = BQ x y := by
      intro x y
      rw [← hgiso (g.symm x) (g.symm y)]
      simp
    have h := fibreCarrierProj_comp_symm hBsym F g.symm c⁻¹ hgen' hgiso' x
    simpa [LinearEquiv.symm_symm] using h
  right_inv y := fibreCarrierProj_comp_symm hBsym F g c hgen hgiso y

omit [Module.Finite ℚ V] in
/-- **The generator's inverse image**: an isometry carrying `gen` to `c • gen` with `c ≠ 0`
carries `gen` back to `c⁻¹ • gen`. -/
theorem fibreGen_symm (F : ConicalLine BQ Q) (g : V ≃ₗ[ℚ] V) {c : ℚ}
    (hgen : g F.gen = c • F.gen) (hc : c ≠ 0) :
    g.symm F.gen = c⁻¹ • F.gen := by
  refine g.injective ?_
  rw [LinearEquiv.apply_symm_apply, map_smul, hgen, smul_smul, inv_mul_cancel₀ hc, one_smul]

omit [Module.Finite ℚ V] in
/-- A carrier vector pairs with `gen` trivially, and an isometry carrying `gen` to a multiple of
itself therefore keeps it trivially paired with the image: the `partner` correction of the
projection of `g x` is zero for `x` in the carrier. -/
theorem BQ_gen_generator_eq_zero (F : ConicalLine BQ Q) (g : V ≃ₗ[ℚ] V) {c : ℚ}
    (hgen : g F.gen = c • F.gen) (hc : c ≠ 0)
    (hgiso : ∀ x y : V, BQ (g x) (g y) = BQ x y)
    (x : ↥F.space) : BQ F.gen (g (x : V)) = 0 := by
  have hx : BQ F.gen (x : V) = 0 := ((mem_planeComplement_iff BQ).1 x.2).1
  have h1 : BQ F.gen (g (x : V)) = BQ (g.symm F.gen) (x : V) := by
    rw [← hgiso (g.symm F.gen) (x : V)]
    simp
  rw [h1, fibreGen_symm F g hgen hc]
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, hx, mul_zero]

omit [Module.Finite ℚ V] in
/-- **The induced carrier automorphism is the projection of the image**, with the `partner`
correction vanishing on the carrier (`BQ_gen_generator_eq_zero`). -/
theorem fibreInducedEquiv_apply_val (hBsym : BQ.IsSymm) (F : ConicalLine BQ Q)
    (g : V ≃ₗ[ℚ] V) {c : ℚ} (hgen : g F.gen = c • F.gen) (hc : c ≠ 0)
    (hgiso : ∀ x y : V, BQ (g x) (g y) = BQ x y) (x : ↥F.space) :
    ((fibreInducedEquiv hBsym F g c hgen hc hgiso x : ↥F.space) : V) =
      g (x : V) - BQ F.partner (g (x : V)) • F.gen := by
  show ((fibreCarrierProj hBsym F (g (x : V)) : ↥F.space) : V) = _
  rw [fibreCarrierProj_apply, BQ_gen_generator_eq_zero F g hgen hc hgiso x, zero_smul, sub_zero]

omit [Module.Finite ℚ V] in
/-- **`Stab(I)` transports the traces of the walls through `I`** — the equivariance of the trace
under the *stabilizer* of the line, which is the one form of invariance that is true.

Let `g` be an isometry with `g gen = c gen`, `c ≠ 0`, and let `e : ↥F.space ≃ ↥F.space` be its
induced action on the carrier (`fibreInducedEquiv`). Then for a wall `ψ` through `I`,
`e '' (F.space ⊓ ker ψ) = F.space ⊓ ker (ψ ∘ g⁻¹)`:

a point `x` of the carrier is killed by `ψ` exactly when its image `π (g x)` is killed by
`ψ ∘ g⁻¹`.
The proof uses that `π (g x) - g x` is a multiple of `gen`, on which `ψ` vanishes because
`I ≤ ker ψ`, and that `g⁻¹ gen` is again a multiple of `gen` (`fibreGen_symm`). This is where
an isometry that moves `I` fails: for such a `g` the factor `π (g x) - g x` carries a `partner`
component, `ψ` does not vanish on it, and no comparison at a fixed fibre exists —
`fibreTrace_comp` states that general fact. -/
theorem fibreTrace_map_fibreInducedEquiv (hBsym : BQ.IsSymm) (F : ConicalLine BQ Q)
    (g : V ≃ₗ[ℚ] V) {c : ℚ} (hgen : g F.gen = c • F.gen) (hc : c ≠ 0)
    (hgiso : ∀ x y : V, BQ (g x) (g y) = BQ x y)
    (ψ : V →ₗ[ℚ] ℚ) (hI : F.line ≤ LinearMap.ker ψ) :
    (fibreTrace ψ F).map
        (fibreInducedEquiv hBsym F g c hgen hc hgiso).toLinearMap =
      fibreTrace (ψ.comp (g.symm : V →ₗ[ℚ] V)) F := by
  have hgen0 : ψ F.gen = 0 :=
    hI (by rw [F.line_eq]; exact Submodule.subset_span (Set.mem_singleton _))
  have hgen' : g.symm F.gen = c⁻¹ • F.gen := fibreGen_symm F g hgen hc
  have hsymm0 : ψ (g.symm F.gen) = 0 := by
    rw [hgen', map_smul, smul_eq_mul, hgen0, mul_zero]
  have hzero : ∀ v : ↥F.space, BQ F.gen (g (v : V)) = 0 :=
    fun v => BQ_gen_generator_eq_zero F g hgen hc hgiso v
  have hzero' : ∀ v : ↥F.space, BQ F.gen (g.symm (v : V)) = 0 := by
    intro v
    have h1 : BQ F.gen (g.symm (v : V)) = BQ (g F.gen) (v : V) := by
      rw [← hgiso F.gen (g.symm (v : V))]
      simp
    rw [h1, hgen, map_smul, LinearMap.smul_apply, smul_eq_mul]
    have hv : BQ F.gen (v : V) = 0 := ((mem_planeComplement_iff BQ).1 v.2).1
    rw [hv, mul_zero]
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hx' : ψ (x : V) = 0 := by simpa [fibreTrace, LinearMap.mem_ker] using hx
    have hxval : (((fibreInducedEquiv hBsym F g c hgen hc hgiso x : ↥F.space) : V)) =
        g (x : V) - BQ F.partner (g (x : V)) • F.gen := by
      show ((fibreCarrierProj hBsym F (g (x : V)) : ↥F.space) : V) = _
      rw [fibreCarrierProj_apply, hzero x, zero_smul, sub_zero]
    show ψ (g.symm (((fibreInducedEquiv hBsym F g c hgen hc hgiso x : ↥F.space) : V))) = 0
    rw [hxval]
    simp only [map_sub, map_smul, LinearEquiv.symm_apply_apply, hx', hsymm0, hgen0, smul_eq_mul,
      mul_zero, sub_zero]
  · intro hy
    have hy' : ψ (g.symm (y : V)) = 0 := by simpa [fibreTrace, LinearMap.mem_ker] using hy
    refine ⟨(fibreInducedEquiv hBsym F g c hgen hc hgiso).symm y, ?_, ?_⟩
    · have hval : (((fibreInducedEquiv hBsym F g c hgen hc hgiso).symm y : ↥F.space) : V) =
          g.symm (y : V) - BQ F.partner (g.symm (y : V)) • F.gen := by
        show ((fibreCarrierProj hBsym F (g.symm (y : V)) : ↥F.space) : V) = _
        rw [fibreCarrierProj_apply, hzero' y, zero_smul, sub_zero]
      have hgoal :
          ψ (((fibreInducedEquiv hBsym F g c hgen hc hgiso).symm y : ↥F.space) : V) = 0 := by
        rw [hval]
        simp only [map_sub, map_smul, smul_eq_mul, hsymm0, hgen0, mul_zero, sub_zero]
        exact hy'
      simpa [fibreTrace, LinearMap.mem_ker] using hgoal
    · simp

/-- **(HT′) — the group-theoretic form of the one open hypothesis of the fibre count.**

For one ambient orbit representative `Hⱼ = ker (ψ j)` and the fibre of `I`, the walls `g Hⱼ` that
contain `I` should contribute a *single* `Stab_Γ(I)`-orbit of traces at `I`. Quantified over pairs:
any two isometries of `Γ` carrying `I` into `Hⱼ` — equivalently, whose walls `g Hⱼ` contain `I` —
differ by an element `h ∈ Γ` that preserves the line `I`, its generator up to a nonzero rational
scalar, and the form, and that carries one wall to the other.

This is the hypothesis the transfer consumes, and it is neither of the two statements it is easily
confused with. It is **stronger** than point transitivity of `Γ` on primitive isotropic lines (which
is `CuspWorkedInstance.exists_isometry_apply_eq` for `U ⊕ U`): that says all fibres are equivalent,
and says nothing about the hyperplanes through one of them. It is **strictly weaker** than
`distinctTraces ψ F ⊆ orbitFamilyTraces BQ F gen`: it mentions no lattice, no basis of the reduced
lattice, no primitive generator and no count, and an orbit of it may be infinite. What it buys is
finiteness of the number of orbits — one per ambient orbit representative — and that is all the
transfer needs, because the fibre count `cutsFinitelyOnTraces_orbitFamily` turns one orbit family
into the duplicate-insensitive cutter count. -/
def StabilizerTransitiveOnWallsThroughLine {ι : Type*} (BQ : LinearMap.BilinForm ℚ V)
    (ψ : ι → V →ₗ[ℚ] ℚ) (Γ : Set (V ≃ₗ[ℚ] V)) (F : ConicalLine BQ Q) (j : ι) : Prop :=
  ∀ g₁ ∈ Γ, ∀ g₂ ∈ Γ,
    F.line ≤ LinearMap.ker ((ψ j).comp (g₁ : V →ₗ[ℚ] V)) →
    F.line ≤ LinearMap.ker ((ψ j).comp (g₂ : V →ₗ[ℚ] V)) →
    ∃ (h : V ≃ₗ[ℚ] V) (c : ℚ), h ∈ Γ ∧ c ≠ 0 ∧ h F.gen = c • F.gen ∧
      (∀ x y : V, BQ (h x) (h y) = BQ x y) ∧
      Submodule.map (h : V →ₗ[ℚ] V) (LinearMap.ker ((ψ j).comp (g₁ : V →ₗ[ℚ] V))) =
        LinearMap.ker ((ψ j).comp (g₂ : V →ₗ[ℚ] V))

/-- **The gap, in the form the transfer's conclusion has**: the traces at `I` of the walls of `ℋ`
containing `I` are a finite union of orbits of hyperplanes of `I^⊥/I` under the induced action
`fibreInducedEquiv` of `Stab_Γ(I)`. The orbits may be infinite — this is not a finiteness statement
about `distinctTraces`, which is false — and the group `ΓI` is tied to `Γ` and to the line `I` by
its very statement. -/
def TraceOrbitCover (hBsym : BQ.IsSymm) {ι : Type*} (ψ : ι → V →ₗ[ℚ] ℚ)
    (Γ : Set (V ≃ₗ[ℚ] V)) (F : ConicalLine BQ Q) : Prop :=
  ∃ (H₀ : Finset (Submodule ℚ ↥F.space)) (ΓI : Set (↥F.space ≃ₗ[ℚ] ↥F.space)),
    (∀ e ∈ ΓI, ∃ (h : V ≃ₗ[ℚ] V) (c : ℚ) (hgen : h F.gen = c • F.gen) (hc : c ≠ 0)
      (hgiso : ∀ x y : V, BQ (h x) (h y) = BQ x y),
      h ∈ Γ ∧ e = fibreInducedEquiv hBsym F h c hgen hc hgiso) ∧
    (∀ T ∈ distinctTraces ψ F, ∃ T₀ ∈ H₀, ∃ e ∈ ΓI, T = T₀.map e.toLinearMap)

/-- **The transfer's first half, from the gap**: if the traces are a finite union of
`Stab_Γ(I)`-orbits of hyperplanes of the carrier, then they are an orbit family of a finite set of
hyperplanes — which is the shape `orbitFamilyTraces` and every `hcut` consumer read. The remaining
step from an orbit family of *hyperplanes* to `orbitFamilyTraces BQ F gen` is the primitive
generator `gen` and its property, which the arithmetic callers already take. -/
theorem exists_orbitFamily_of_traceOrbitCover (hBsym : BQ.IsSymm) {ι : Type*}
    {ψ : ι → V →ₗ[ℚ] ℚ} {Γ : Set (V ≃ₗ[ℚ] V)} {F : ConicalLine BQ Q}
    (hcov : TraceOrbitCover hBsym ψ Γ F) :
    ∃ (H₀ : Finset (Submodule ℚ ↥F.space)) (ΓI : Set (↥F.space ≃ₗ[ℚ] ↥F.space)),
      distinctTraces ψ F ⊆ orbitFamily H₀ ΓI := by
  obtain ⟨H₀, ΓI, -, hmem⟩ := hcov
  refine ⟨H₀, ΓI, fun T hT => ?_⟩
  obtain ⟨T₀, hT₀, e, he, hTe⟩ := hmem T hT
  exact mem_orbitFamily.2 ⟨T₀, hT₀, e, he, hTe⟩

end InducedAction

section BasisFreeCaller

variable {BQ : LinearMap.BilinForm ℚ V} {Q : QuadraticForm ℝ (realified V)}
variable {ι : Type*}

/-- **The fibre-level caller with the reduced lattice's basis supplied by the library.** Same as
`semifanArrangement_arithmetic_fibre`, without the fibre basis `bs` and its identification `hbs` as
inputs: `exists_basis_reducedLattice` produces them from the ambient lattice
`Λ = span ℤ (range bs₀)` and the reduced lattice `(Λ ⊓ I^⊥)/(Λ ⊓ I)` of Looijenga §1B, p. 11. -/
theorem semifanArrangement_arithmetic_fibre_of_basis
    (hBQsym : BQ.IsSymm)
    (hBQ : ∀ u w : V, (associated Q) (rationalPoint u) (rationalPoint w) = (BQ u w : ℝ))
    (hsig : sigPos Q = 2) (hnd : Q.Nondegenerate) (F : ConicalLine BQ Q)
    {κ₀ : Type} [Finite κ₀] (bs₀ : Module.Basis κ₀ ℚ V)
    (hint₀ : ∀ x ∈ Submodule.span ℤ (Set.range bs₀), ∀ y ∈ Submodule.span ℤ (Set.range bs₀),
      ∃ n : ℤ, BQ x y = (n : ℚ))
    (ΓI : Set (↥F.space ≃ₗ[ℚ] ↥F.space))
    (hone : (1 : ↥F.space ≃ₗ[ℚ] ↥F.space) ∈ ΓI)
    (H₀ : Finset (Submodule ℚ ↥F.space))
    (hΓΛ : ∀ e ∈ ΓI, Submodule.map ((e : ↥F.space →ₗ[ℚ] ↥F.space).restrictScalars ℤ)
      (reducedLattice hBQsym F (Submodule.span ℤ (Set.range bs₀))) =
        reducedLattice hBQsym F (Submodule.span ℤ (Set.range bs₀)))
    (hΓiso : ∀ e ∈ ΓI, ∀ x y : ↥F.space,
      restrictBilinForm BQ F.space (e x) (e y) = restrictBilinForm BQ F.space x y)
    (gen : ↥(orbitFamily H₀ ΓI) → ↥F.space)
    (hgen : ∀ ℓ : ↥(orbitFamily H₀ ΓI), gen ℓ ≠ 0 ∧
      reducedLattice hBQsym F (Submodule.span ℤ (Set.range bs₀)) ⊓ ℓ.1.restrictScalars ℤ =
        Submodule.span ℤ ({gen ℓ} : Set ↥F.space))
    (ψ : ι → V →ₗ[ℚ] ℚ)
    (hsub : distinctTraces ψ F ⊆ orbitFamilyTraces BQ F gen)
    {ρ : ↥F.space} (hρ : fibreForm Q F.space (rationalPoint ρ) = 0) (hρ0 : ρ ≠ 0)
    (hρsheet : 0 ≤ (associated (fibreForm Q F.space)) (rationalPoint ρ) F.sheet) :
    IsLocallyRationalDecomposition F.closure (semifanArrangement ψ F) ∧
      sigmaSupportSpace (positiveCone.upper (fibreForm Q F.space) F.sheet)
          (semifanArrangementTraces ψ F)
          (PointedCone.hull ℝ ({rationalPoint ρ} : Set (realified ↥F.space))) ≤
        LinearMap.ker ((associated (fibreForm Q F.space)) (rationalPoint ρ)) ∧
      (∀ τ : supportIndex (positiveCone.upper (fibreForm Q F.space) F.sheet)
          (semifanArrangementTraces ψ F)
          (PointedCone.hull ℝ ({rationalPoint ρ} : Set (realified ↥F.space))),
        (⨅ T : {T : distinctTraces ψ F // traceForm ψ F T (rationalPoint ρ) = 0},
            LinearMap.ker (traceForm ψ F T.1).toLinearMap) ≤
          Submodule.span ℝ (τ.1 : Set (realified ↥F.space))) ∧
      sigmaSupportSpace (positiveCone.upper (fibreForm Q F.space) F.sheet)
          (semifanArrangementTraces ψ F)
          (PointedCone.hull ℝ ({rationalPoint ρ} : Set (realified ↥F.space))) =
        LinearMap.ker ((associated (fibreForm Q F.space)) (rationalPoint ρ)) ⊓
          rayTraceKernels ψ F ρ := by
  classical
  obtain ⟨κ, hκ, bs, hbs⟩ := exists_basis_reducedLattice hBQsym F bs₀
  haveI : Fintype κ := hκ
  have hΓΛ' : ∀ e ∈ ΓI, Submodule.map ((e : ↥F.space →ₗ[ℚ] ↥F.space).restrictScalars ℤ)
      (Submodule.span ℤ (Set.range bs)) = Submodule.span ℤ (Set.range bs) := by
    intro e he
    rw [hbs]
    exact hΓΛ e he
  have hgen' : ∀ ℓ : ↥(orbitFamily H₀ ΓI), gen ℓ ≠ 0 ∧
      Submodule.span ℤ (Set.range bs) ⊓ ℓ.1.restrictScalars ℤ =
        Submodule.span ℤ ({gen ℓ} : Set ↥F.space) := by
    intro ℓ
    obtain ⟨h1, h2⟩ := hgen ℓ
    exact ⟨h1, by rw [hbs]; exact h2⟩
  exact semifanArrangement_arithmetic_fibre hBQsym hBQ hsig hnd F bs₀ hint₀ bs hbs ΓI hone H₀
    hΓΛ' hΓiso gen hgen' ψ hsub hρ hρ0 hρsheet

end BasisFreeCaller

end LeanCategories.Lattices.Valued
