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
  `cutsFinitelyOnRational_traceForm_iff` reads it as `CutsFinitelyOnRational` of the trace-indexed
  family, so every consumer of the latter applies to it;
  `cutsFinitelyOnTraces_orbitFamily` derives it from the reduced lattice and the orbit family of
  §1B — no local-finiteness or counting certificate is assumed.
* `semifanArrangementTraces_isLocallyRational_of_arithmetic`: condition (i) of Definition 6.1 for
  `Σ(ℋ)` at a fibre, from that arithmetic input alone.
* the half-line chain at an **actual isotropic ray** of the Lorentzian fibre
  (`semifanArrangement_ray_meets`, `sigmaSupportSpace_ray_le_ker`, `traceKernel_le_span_of_member`):
  the statements of `SemifanArrangement` that quantify over `ConicalPlane` — which is empty in the
  current development — are re-stated at a ray `ρ` of the fibre with `fibreForm Q F.space
  (rationalPoint ρ) = 0`, so that they rest on the fibre's own Lorentzian geometry.
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

end TraceCounting

end LeanCategories.Lattices.Valued
