/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Lattices.Valued.Semifan

/-!
# The arrangement decomposition `Σ(H)` on the conical locus

E. Looijenga, *Compactifications defined by arrangements II: locally symmetric varieties of
  type IV*, arXiv math/0201218v2 (2002), §6, text version
  `.tmp-sources/looijenga-math0201218v2.md`:

* **Example 6.4, p. 29** (text line 791): for a finite union `H` of `Γ`-orbits of `ℚ`-hyperplanes
  of `V` of signature `(2, n-1)`, "the `H ∈ H` containing `I` correspond to `ℚ`-hyperplanes in
  `I^⊥/I ⊗ I` of signature `(1, n-2)` and so according to example 4.3-b these decompose `C_{I,+}`
  into locally rational cones", giving the admissible decomposition `Σ(H)`.

## What is stated

* `semifanArrangement`: **the decomposition `Σ(H)`**, one arrangement decomposition per conical
  fibre — the cells of the traces of the hyperplanes containing `I` (`arrangementDecomposition`,
  the port of Example 4.3 (b), #159), cut out of `C_{I,+}`.
* `semifanArrangement_isLocallyRational`: **condition (i) of Definition 6.1 for `Σ(H)`** — the
  members in `C_{I,+}` are a locally rational decomposition of it. It is
  `arrangementDecomposition_isLocallyRational` at the fibre form, whose hypotheses are the ones the
  source supplies at the fibre and this file does not re-derive: salience of `C_{I,+}`
  (`salient_rationalClosure`, from the fibre's signature `(1, n-1)`), rationality of the trace
  forms (`isRationalForm_fibreFormC`, because `H` is defined over `ℚ`), and the finiteness of the
  cutting traces (`CutsFinitelyOnRational`, carried: for the arithmetic `H` of the source this is
  the counting lemma of #161 at the fibre's lattice, `cutsFinitelyOnRational_orbitFamily`, which is
  not instantiated per fibre here).
* `realifiedForm`/`fibreFormC`: the trace of a `ℚ`-hyperplane on a fibre, as a *continuous real
  linear* form — `LinearMap.baseChange` extended through `ℝ ⊗_ℚ ℚ ≅ ℝ`, and `C_{I,+}`'s module
  topology. The repository had only `IsRationalForm`, a characterization by values on rational
  points, and no construction of the extension.

## What is not here

* **Condition (ii) and `J_{Σ(H)} = J_H`** (the `Σ`-support space of a plane's half line is
  `J^⊥ ⊓ ⋂_{H ∋ J} H`). The inclusion `≤` is available from the support space's definition — every
  member above the half line is one-signed for each wall through it and zero on it, so its support
  space lies in that wall, together with `supportSpace_le_ker_associated_of_isotropic` for the `J^⊥`
  half. The reverse needs the span of an arrangement cell above the half line,
  `⟨arrangementCone φ s ⊓ C₊⟩ = ⋂_{s i = 0} ker (φ i)`, which is where the source's
  "it follows from this and Example 4.3-b" sits; it in turn needs the walls' signature `(1, n-2)`,
  and the repository has no statement about the signature of the restriction of a form to a
  hyperplane (only to the complement of a hyperbolic plane, `sigPos_restrict_planePerp`).
* **The `Γ`-invariance of `Σ(H)`** (Definition 6.1's `gammaInvariant`, which is at the level of the
  members since #162's second commit): the fibre transport is `ConicalLine.map` and the closure
  transport `ConicalLine.map_closure`, but carrying a *cell* of the arrangement in the fibre of `I`
  to a cell of the arrangement in the fibre of `gI` needs the family of forms to be `Γ`-equivariant
  (a permutation `ρ` of the index set with `ψ (ρ i) (g x) = d i * ψ i x`, `d i ≠ 0`), and then the
  sign patterns to be matched across the two realifications —
  `arrangementDecomposition_coneMap_of_equivariant` is stated for a self-equivalence of one `L(ℝ)`,
  not for the two spaces of two fibres, so it has to be transported through
  `fibreCarrierEquivReal`.
-/

@[expose] public section

open PointedCone QuadraticMap

open scoped TensorProduct

namespace LeanCategories.Lattices.Valued

variable {V : Type} [AddCommGroup V] [Module ℚ V] [Module.Finite ℚ V]

/-! ## The real form of a `ℚ`-linear form -/

/-- **The `ℝ`-linear extension of a `ℚ`-linear form**: base change to `ℝ` through the canonical
`ℝ ⊗_ℚ ℚ ≅ ℝ`. -/
noncomputable def realifiedForm (ψ : V →ₗ[ℚ] ℚ) : realified V →ₗ[ℝ] ℝ :=
  (TensorProduct.AlgebraTensorModule.rid ℚ ℝ ℝ).toLinearMap.comp (LinearMap.baseChange ℝ ψ)

omit [Module.Finite ℚ V] in
theorem realifiedForm_rationalPoint (ψ : V →ₗ[ℚ] ℚ) (v : V) :
    realifiedForm ψ (rationalPoint v) = (ψ v : ℝ) := by
  simp only [realifiedForm, LinearMap.comp_apply, LinearEquiv.coe_coe,
    TensorProduct.AlgebraTensorModule.rid_tmul, rationalPoint_apply, LinearMap.baseChange_tmul]
  exact Rat.smul_one_eq_cast ℝ (ψ v)

omit [Module.Finite ℚ V] in
/-- A `ℚ`-linear form's extension is a rational form in the sense of `IsRationalForm`. -/
theorem isRationalForm_realifiedForm (ψ : V →ₗ[ℚ] ℚ) :
    IsRationalForm (realifiedForm ψ) :=
  ⟨ψ, fun v => realifiedForm_rationalPoint ψ v⟩

/-- The extension, as a continuous linear form: on the module topology every linear form is
continuous. -/
noncomputable def realifiedFormC (ψ : V →ₗ[ℚ] ℚ) : realified V →L[ℝ] ℝ :=
  ⟨realifiedForm ψ, IsModuleTopology.continuous_of_linearMap _⟩

omit [Module.Finite ℚ V] in
@[simp] theorem realifiedFormC_apply (ψ : V →ₗ[ℚ] ℚ) (x : realified V) :
    realifiedFormC ψ x = realifiedForm ψ x := rfl

omit [Module.Finite ℚ V] in
@[simp] theorem realifiedFormC_toLinearMap (ψ : V →ₗ[ℚ] ℚ) :
    (realifiedFormC ψ).toLinearMap = realifiedForm ψ := rfl

/-! ## The trace of a `ℚ`-hyperplane on a conical fibre -/

section FibreTrace

variable {BQ : LinearMap.BilinForm ℚ V} {Q : QuadraticForm ℝ (realified V)}

/-- **The trace of the hyperplane `ker ψ` on the fibre of `I`**, as a continuous real linear form:
the extension of `ψ` composed with the identification of the fibre's carrier with a subspace of
`V(ℝ)`. This is the source's "the `H ∈ H` containing `I` correspond to `ℚ`-hyperplanes in
`I^⊥/I ⊗ I`" (Example 6.4, p. 29). -/
noncomputable def fibreFormC (F : ConicalLine BQ Q) (ψ : V →ₗ[ℚ] ℚ) :
    realified ↥F.space →L[ℝ] ℝ :=
  ⟨(realifiedForm ψ).comp (realifyMap F.space),
    IsModuleTopology.continuous_of_linearMap _⟩

omit [Module.Finite ℚ V] in
@[simp] theorem fibreFormC_apply (F : ConicalLine BQ Q) (ψ : V →ₗ[ℚ] ℚ)
    (x : realified ↥F.space) :
    fibreFormC F ψ x = realifiedForm ψ (realifyMap F.space x) := rfl

omit [Module.Finite ℚ V] in
/-- The trace form is rational: it is the extension of `ψ` restricted to the fibre. -/
theorem isRationalForm_fibreFormC (F : ConicalLine BQ Q) (ψ : V →ₗ[ℚ] ℚ) :
    IsRationalForm (fibreFormC F ψ).toLinearMap :=
  ⟨ψ.comp F.space.subtype, fun w => by
    change realifiedForm ψ (realifyMap F.space (rationalPoint w))
      = ((ψ.comp F.space.subtype) w : ℝ)
    rw [realifyMap_rationalPoint, realifiedForm_rationalPoint]
    rfl⟩

omit [Module.Finite ℚ V] in
/-- **The trace of a hyperplane containing the plane `J` vanishes on the fibre ray of `J`**: the
class of `J` in `I^⊥/I` lies in the trace of every `H ⊇ J`. This is the computation behind
condition (ii) of Definition 6.1 for `Σ(H)` and feeds `J_{Σ(H)}`. -/
theorem fibreFormC_fibreRay_eq_zero {BQ : LinearMap.BilinForm ℚ V}
    {Q : QuadraticForm ℝ (realified V)} (hBsym : BQ.IsSymm)
    (F : ConicalLine BQ Q) (G : ConicalPlane BQ) (h : F.line ≤ G.plane)
    (ψ : V →ₗ[ℚ] ℚ) (hψ : G.plane ≤ LinearMap.ker ψ) :
    fibreFormC F ψ (rationalPoint (fibreRay hBsym F G)) = 0 := by
  change realifiedForm ψ (realifyMap F.space (rationalPoint (fibreRay hBsym F G))) = 0
  rw [realifyMap_rationalPoint, realifiedForm_rationalPoint]
  have hmem : ((fibreRay hBsym F G : ↥F.space) : V) ∈ G.plane := by
    rw [fibreRay_val hBsym F G h]
    exact Submodule.sub_mem _ G.ray_mem
      (Submodule.smul_mem _ _ (F.gen_mem_plane G h))
  have hzero : ψ ((fibreRay hBsym F G : ↥F.space) : V) = 0 := by
    simpa using hψ hmem
  rw [hzero]
  norm_num

end FibreTrace

/-! ## `Σ(H)`: one arrangement decomposition per conical fibre -/

section Arrangement

variable {ι : Type*} {BQ : LinearMap.BilinForm ℚ V} {Q : QuadraticForm ℝ (realified V)}

/-- The index set of the hyperplanes of `H` that contain the line `I` of the fibre `F` — the
`H ∈ H` that "contain `I`" in Example 6.4, p. 29. -/
abbrev fibreWalls (ψ : ι → V →ₗ[ℚ] ℚ) (F : ConicalLine BQ Q) : Type _ :=
  {i : ι // F.line ≤ LinearMap.ker (ψ i)}

/-- **Looijenga, Example 6.4, p. 29: the decomposition `Σ(H)` of the conical locus** — in the fibre
of `I`, the arrangement decomposition `Σ(H)` of Example 4.3 (b) cut out of `C_{I,+}` by the traces
of the hyperplanes containing `I`. -/
noncomputable def semifanArrangement (ψ : ι → V →ₗ[ℚ] ℚ) (F : ConicalLine BQ Q) :
    Set (PointedCone ℝ (realified ↥F.space)) :=
  arrangementDecomposition (fun i : fibreWalls ψ F => fibreFormC F (ψ i)) F.closure

omit [Module.Finite ℚ V] in
/-- **Looijenga, Example 6.4, p. 29, condition (i) of Definition 6.1**: the traces of the
hyperplanes containing `I` cut `C_{I,+}` into a locally rational decomposition.

The three hypotheses are the ones the source supplies at the fibre: salience of `C_{I,+}`
(`hsal`, from the fibre's signature `(1, n-1)`), rationality of the traces
(`hφ`, from `isRationalForm_fibreFormC` since `H` is defined over `ℚ`), and finiteness of the
cutting traces (`hcut`: for the arithmetic `H` of the source this is the counting lemma of #161 at
the fibre's lattice, `cutsFinitelyOnRational_orbitFamily`, not instantiated per fibre here). -/
theorem semifanArrangement_isLocallyRational (ψ : ι → V →ₗ[ℚ] ℚ) (F : ConicalLine BQ Q)
    (hsal : (F.closure : ConvexCone ℝ (realified ↥F.space)).Salient)
    (hφ : ∀ i : fibreWalls ψ F, IsRationalForm (fibreFormC F (ψ i)).toLinearMap)
    (hcut : CutsFinitelyOnRational F.closure (fun i : fibreWalls ψ F => fibreFormC F (ψ i))) :
    IsLocallyRationalDecomposition F.closure (semifanArrangement ψ F) :=
  arrangementDecomposition_isLocallyRational hsal hφ hcut

/-- **Condition (i) of Definition 6.1 for `Σ(H)`, from the fibre's signature alone.** The
rationality of the trace forms is discharged (`isRationalForm_fibreFormC`), and salience of
`C_{I,+}` follows from `sigPos` of the fibre form being `1` (§1B, p. 11). What remains is
`CutsFinitelyOnRational` at the fibre, which is the source's arithmetic input. -/
theorem semifanArrangement_isLocallyRational_of_sigPos (ψ : ι → V →ₗ[ℚ] ℚ) (F : ConicalLine BQ Q)
    (hpos : sigPos (fibreForm Q F.space) = 1)
    (hnd : (fibreForm Q F.space).Nondegenerate)
    (hcut : CutsFinitelyOnRational F.closure (fun i : fibreWalls ψ F => fibreFormC F (ψ i))) :
    IsLocallyRationalDecomposition F.closure (semifanArrangement ψ F) :=
  semifanArrangement_isLocallyRational ψ F
    (ConicalLine.closure_eq_closedSheet F hpos ▸ salient_rationalClosure hpos hnd F.sheet_pos)
    (fun i => isRationalForm_fibreFormC F (ψ i)) hcut

end Arrangement

end LeanCategories.Lattices.Valued
