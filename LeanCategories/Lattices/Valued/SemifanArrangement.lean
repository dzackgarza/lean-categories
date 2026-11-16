/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Lattices.Valued.Semifan
public import Mathlib.Algebra.Module.Lattice.Full

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
  topology.
* `semifanArrangement_gammaInvariant`: **the `Γ`-invariance of `Σ(H)`** (Definition 6.1's
  condition on the collection) for a `Γ`-equivariant family of forms — for each `g ∈ Γ` a
  permutation `ρ` of the index set with `ψ (ρ i) (g y) = d i * ψ i y` and `d i ≠ 0`, which is what
  `H` being a finite union of `Γ`-orbits supplies (the source's `H` is `Γ`-invariant, so `Γ`
  permutes its members). `g` carries the fibre of `I` to the fibre of `gI`
  (`Semifan.ConicalLine.map`) and `C_{I,+}` onto the closure of the image fibre
  (`Semifan.ConicalLine.map_closure`); the walls of the two fibres correspond under
  `fibreWallsEquiv`, their traces under `fibreFormC_fibreCarrierEquivReal`, and the members of the
  two arrangements under `map_arrangementDecomposition` — the two-space form of
  `arrangementDecomposition_coneMap_of_equivariant`, since the two fibres are two different
  `ℚ`-vector spaces (`map_arrangementCone`, `map_arrangementCells`, `map_faceClosure`), together
  with `fibreWallsEquiv_coe` and `realifiedForm_equivariant`. The decomposition itself is
  `arrangementDecomposition_reindex`-invariant, so the two index sets — the walls of `H` containing
  `I` and those containing `gI` — may be compared along `ρ`.
* **the reduced lattice `(Λ ⊓ I^⊥)/(Λ ⊓ I)` of Looijenga §1B, p. 11** as a `ℤ`-module:
  `reducedLattice` is the image of `Λ ⊓ I^⊥` under the hyperbolic projection `fibreProjLinear` — the
  projection kills exactly `I` on `I^⊥` (`span_inf_restrictScalars`), so the image is the quotient.
  `isFullLattice_reducedLattice`: it is a `ℤ`-lattice in the fibre's carrier, and
  `exists_basis_reducedLattice`: the fibre has a `ℚ`-basis whose `ℤ`-span *is* it, which is the form
  in which the counting lemma of Example 4.3 (b) takes the lattice of a cone system.
  `pairing_fibreProj` and `integral_reducedLattice`: the fibre's pairing of two projected normals is
  the ambient pairing, so a form integral on `Λ` is integral on the reduced lattice.

## What is not here

* **`CutsFinitelyOnRational` at the fibre**, and hence condition (i) of Definition 6.1 with no
  hypothesis carried. The reduced lattice it runs on is in place (`reducedLattice`, with a `ℚ`-basis
  of the carrier whose `ℤ`-span it is, and the integrality of the form on it), as is the counting
  lemma of Example 4.3 (b) with the group action replaced by a finite set of norms
  (`cutsFinitelyOnRational_of_finiteNormValues`). What is missing is the instantiation of that lemma
  at the fibre, and its `hg` hypothesis — a generator of `ℓ ⊓ Λ_F` for each wall line `ℓ` — is where
  the obvious route fails: the cut of a `ℚ`-line with a lattice is cyclic, but its generator need
  not be the projection of an ambient one, so the ambient finite set of norms
  (`fibreForm_fibreProj`, `finite_form_values_of_orbitFamily`) does not bound the norms of the
  generators the lemma needs.
  For `Λ = ℤ(e + 2w) ⊕ ℤ f ⊕ ℤ(2e)` in `ℚ³ = ⟨e, f⟩ ⊥ ⟨w⟩` (`e·f = 1`, `w·w = 1`, the form
  integral on `Λ`) and `ℓ = ℚ w` one has `ℓ ⊓ Λ = ℤ·4w` while `Λ_F = ℤ·2π(w)` and
  `ℓ ⊓ Λ_F = ℤ·2π(w)` — the projection `π(4w) = 4w` is not primitive in the reduced lattice (a hand
  computation, not a Lean statement). The counting at the fibre therefore needs a norm bound at the
  reduced lattice itself, or the transfer of the ambient counting hypothesis along
  `fibreProjLinear`, which is a statement about rational cones in the fibre and the ambient closed
  sheet and is not in the repository either.

* **Condition (ii) and `J_{Σ(H)} = J_H`** (the `Σ`-support space of a plane's half line is
  `J^⊥ ⊓ ⋂_{H ∋ J} H`). At the half line of `J`, `vSigmaPlane` is `sigmaSupportSpace` over the
  members `τ` of `Σ(H)` with `C_{J,+} ≤ τ` and `τ ∩ C_I ≠ ∅`, and *both* inclusions need such a
  `τ`: with none that intersection is `⊤` and the two sides are different subspaces. The exact
  statement still owed is therefore, at each `F` and `G` with `F.line ≤ G.plane`,
  `∃ τ ∈ semifanArrangement ψ F, PointedCone.hull ℝ {rationalPoint (fibreRay hBsym F G)} ≤ τ ∧
  ((τ : Set (realified ↥F.space)) ∩ positiveCone.upper (fibreForm Q F.space) F.sheet).Nonempty`.
  It does **not** follow from local finiteness on the open cone alone, which is what the counting
  lemma gives (`finite_setOf_apply_eq_zero_of_cutsFinitelyOnRational`): for an arbitrary family of
  forms none need exist — in `ℝ²` with `C₊` the closed upper half plane and the walls `{y = x/n}`
  (`n ≥ 1`) the ray `{(x, 0) | x ≥ 0}` lies in no member of the decomposition, since every sector
  lies in an angular interval bounded away from it — and in the fibre, walls that accumulate at the
  half line without containing it have the same effect. The natural candidate for `τ` is the cell of
  the sign pattern that is `0` exactly on the walls through `J`, which contains the half line by
  construction; the input still needed is that this cell is nonempty, i.e. that the intersection of
  the positive sides of the walls not containing `J` meets `⋂_{H ∋ J} H` in a timelike vector. Given
  `τ`, the `≤` half follows — a trace is one-signed on `τ` and zero on the half line, so it lies in
  `supportForms τ σ` and the support space is inside it, with
  `supportSpace_le_ker_associated_of_isotropic` for the `J^⊥` half — and the `≥` half needs
  `⟨arrangementCone φ s ⊓ C₊⟩ = ⋂_{s i = 0} ker (φ i)`, whose `⊇` half needs the family of walls
  carrying a nonzero sign in `s` to be finite (or locally finite along the cell): `y + ε x` is again
  in the cell only below a bound on `ε` uniform over those walls.
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

/-! ## The transport of an arrangement decomposition between two spaces

Example 6.4's `Σ(H)` is cut fibre by fibre, and the fibres over two `Γ`-related isotropic lines are
two *different* `ℚ`-vector spaces. The transport lemmas of `LocallyRationalDecomposition` are stated
for a self-equivalence `e : L(ℝ) ≃ₗ[ℝ] L(ℝ)` of one space; what follows is the two-space form: a
real linear equivalence `e : L₁(ℝ) ≃ₗ[ℝ] L₂(ℝ)` carries the cells of the arrangement of the forms
`φ` to the cells of the arrangement of the forms `φ'`, provided `φ' i (e y) = c i * φ i y` with
`c i ≠ 0`. The sign pattern is carried along, `s i` becoming `sign (c i) * s i`, exactly as in the
self-equivalence of `arrangementDecomposition_coneMap_of_equivariant`. -/

section TransportBetweenSpaces

variable {V₁ V₂ : Type} [AddCommGroup V₁] [Module ℚ V₁] [AddCommGroup V₂] [Module ℚ V₂]
  {ι : Type*}

/-- A nonzero real number has nonzero sign. -/
theorem sign_ne_zero_of_ne {a : ℝ} (h : a ≠ 0) : SignType.sign a ≠ 0 :=
  fun h0 => h (sign_eq_zero_iff.1 h0)

/-- A nonzero sign has square one. -/
theorem sign_mul_self_of_ne_zero {a : SignType} (h : a ≠ 0) : a * a = 1 := by
  rcases a with _ | _ | _ <;> simp_all

/-- **The image of an intersection of cones under an injective linear map** is the intersection of
the images. Injectivity is what is missing from the general theory of `PointedCone.map`. -/
theorem map_inf_of_injective {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F]
    [Module ℝ F] {f : E →ₗ[ℝ] F} (hf : Function.Injective f)
    (P R : PointedCone ℝ E) :
    (P ⊓ R).map f = P.map f ⊓ R.map f := by
  refine SetLike.ext fun x => ?_
  rw [PointedCone.mem_map, Submodule.mem_inf, PointedCone.mem_map, PointedCone.mem_map]
  constructor
  · rintro ⟨y, ⟨hyP, hyR⟩, rfl⟩
    exact ⟨⟨y, hyP, rfl⟩, ⟨y, hyR, rfl⟩⟩
  · rintro ⟨⟨y, hyP, hyx⟩, ⟨z, hzR, hzx⟩⟩
    have hyz : y = z := hf (hyx.trans hzx.symm)
    exact ⟨y, ⟨hyP, hyz ▸ hzR⟩, hyx⟩

/-- **An equivalence carries an arrangement cone to the arrangement cone of the transported sign
pattern** (the two-space form of `cell_le_coneMap_of_equivariant` and of its reverse). -/
theorem map_arrangementCone {φ : ι → (realified V₁) →L[ℝ] ℝ} {φ' : ι → (realified V₂) →L[ℝ] ℝ}
    {e : realified V₁ ≃ₗ[ℝ] realified V₂} {c : ι → ℝ}
    (hc : ∀ i, c i ≠ 0) (hφ : ∀ i (y : realified V₁), φ' i (e.toLinearMap y) = c i * φ i y)
    (s : ι → SignType) :
    (arrangementCone φ s).map e.toLinearMap =
      arrangementCone φ' (fun i => SignType.sign (c i) * s i) := by
  refine SetLike.ext fun x => ?_
  rw [PointedCone.mem_map, mem_arrangementCone_iff_specializes (φ := φ')]
  constructor
  · rintro ⟨y, hy, rfl⟩ i
    rw [mem_arrangementCone_iff_specializes (φ := φ)] at hy
    have hsign : SignType.sign (φ' i (e.toLinearMap y)) =
        SignType.sign (c i) * SignType.sign (φ i y) := by
      rw [hφ i y, sign_mul]
    rw [hsign]
    rcases hy i with h0 | h0
    · rw [h0, mul_zero]; exact Or.inl rfl
    · rw [h0]; exact Or.inr rfl
  · intro hx
    refine ⟨e.symm.toLinearMap x, ?_, by simp⟩
    rw [mem_arrangementCone_iff_specializes (φ := φ)]
    intro i
    have hφx : φ' i x = c i * φ i (e.symm.toLinearMap x) := by
      have h := hφ i (e.symm.toLinearMap x)
      rwa [show e.toLinearMap (e.symm.toLinearMap x) = x from by simp] at h
    have hsign : SignType.sign (φ i (e.symm.toLinearMap x)) =
        SignType.sign (c i) * SignType.sign (φ' i x) := by
      have h1 : SignType.sign (φ' i x) =
          SignType.sign (c i) * SignType.sign (φ i (e.symm.toLinearMap x)) := by
        rw [hφx, sign_mul]
      rw [h1, ← mul_assoc, sign_mul_self_of_ne_zero (sign_ne_zero_of_ne (hc i)), one_mul]
    rw [hsign]
    rcases hx i with h0 | h0
    · rw [h0, mul_zero]; exact Or.inl rfl
    · rw [h0, ← mul_assoc, sign_mul_self_of_ne_zero (sign_ne_zero_of_ne (hc i)), one_mul]
      exact Or.inr rfl

/-- **The cells of the arrangement are carried onto the cells of the transported arrangement.** -/
theorem map_arrangementCells {φ : ι → (realified V₁) →L[ℝ] ℝ}
    {φ' : ι → (realified V₂) →L[ℝ] ℝ} {e : realified V₁ ≃ₗ[ℝ] realified V₂} {c : ι → ℝ}
    (hc : ∀ i, c i ≠ 0) (hφ : ∀ i (y : realified V₁), φ' i (e.toLinearMap y) = c i * φ i y)
    {Cplus : PointedCone ℝ (realified V₁)} {Cplus' : PointedCone ℝ (realified V₂)}
    (hC : Cplus.map e.toLinearMap = Cplus') :
    (arrangementCells φ Cplus).image (fun σ => σ.map e.toLinearMap) =
      arrangementCells φ' Cplus' := by
  refine Set.Subset.antisymm ?_ ?_
  · rintro - ⟨σ, ⟨s, rfl⟩, rfl⟩
    refine ⟨fun i => SignType.sign (c i) * s i, ?_⟩
    change (arrangementCone φ s ⊓ Cplus).map e.toLinearMap = _
    rw [map_inf_of_injective e.injective, map_arrangementCone hc hφ, hC]
  · rintro - ⟨u, rfl⟩
    have hpat : (fun i => SignType.sign (c i) * (SignType.sign (c i) * u i)) = u := by
      funext i
      rw [← mul_assoc, sign_mul_self_of_ne_zero (sign_ne_zero_of_ne (hc i)), one_mul]
    refine ⟨arrangementCone φ (fun i => SignType.sign (c i) * u i) ⊓ Cplus, ⟨_, rfl⟩, ?_⟩
    change (arrangementCone φ (fun i => SignType.sign (c i) * u i) ⊓ Cplus).map e.toLinearMap = _
    rw [map_inf_of_injective e.injective, map_arrangementCone hc hφ, hpat, hC]

/-- **The face-closure of a family is carried onto the face-closure of its image** (the two-space
form of `faceClosure_coneMap`). -/
theorem map_faceClosure {e : realified V₁ ≃ₗ[ℝ] realified V₂}
    (S : Set (PointedCone ℝ (realified V₁))) :
    (faceClosure S).image (fun σ => σ.map e.toLinearMap) =
      faceClosure (S.image (fun σ => σ.map e.toLinearMap)) := by
  refine Set.Subset.antisymm ?_ ?_
  · rintro - ⟨σ, ⟨τ, hτ, hστ⟩, rfl⟩
    exact mem_faceClosure.2 ⟨τ.map e.toLinearMap, ⟨τ, hτ, rfl⟩, (isFaceOf_map_iff e).2 hστ⟩
  · rintro G ⟨τ, ⟨σ', hσ', rfl⟩, hGτ⟩
    have hcomp : e.toLinearMap.comp e.symm.toLinearMap = LinearMap.id := by
      ext y; simp
    have hcomp' : e.symm.toLinearMap.comp e.toLinearMap = LinearMap.id := by
      ext y; simp
    refine ⟨PointedCone.map e.symm.toLinearMap G, mem_faceClosure.2 ⟨σ', hσ', ?_⟩, ?_⟩
    · have hid : PointedCone.map e.symm.toLinearMap (PointedCone.map e.toLinearMap σ') = σ' := by
        rw [PointedCone.map_map, hcomp', PointedCone.map_id]
      have hmap := (isFaceOf_map_iff (e := e.symm) (σ := G)
        (P := PointedCone.map e.toLinearMap σ')).2 hGτ
      rwa [hid] at hmap
    · change PointedCone.map e.toLinearMap (PointedCone.map e.symm.toLinearMap G) = G
      rw [PointedCone.map_map, hcomp, PointedCone.map_id]

/-- **The arrangement decomposition of `φ` is carried onto that of `φ'`** (the two-space form of
`arrangementDecomposition_coneMap_of_equivariant`). -/
theorem map_arrangementDecomposition {φ : ι → (realified V₁) →L[ℝ] ℝ}
    {φ' : ι → (realified V₂) →L[ℝ] ℝ} {e : realified V₁ ≃ₗ[ℝ] realified V₂} {c : ι → ℝ}
    (hc : ∀ i, c i ≠ 0) (hφ : ∀ i (y : realified V₁), φ' i (e.toLinearMap y) = c i * φ i y)
    {Cplus : PointedCone ℝ (realified V₁)} {Cplus' : PointedCone ℝ (realified V₂)}
    (hC : Cplus.map e.toLinearMap = Cplus') :
    (arrangementDecomposition φ Cplus).image (fun σ => σ.map e.toLinearMap) =
      arrangementDecomposition φ' Cplus' := by
  rw [arrangementDecomposition, arrangementDecomposition,
    map_faceClosure, map_arrangementCells hc hφ hC]

/-- **The arrangement cone does not depend on how the index set is named.** The cells are the sign
cells of the forms, so a bijection of the index set only renames the sign patterns. -/
theorem arrangementCone_reindex {ι' : Type*} {φ : ι' → (realified V₁) →L[ℝ] ℝ} (j : ι ≃ ι')
    (s : ι → SignType) :
    arrangementCone (fun i => φ (j i)) s = arrangementCone φ (fun i' => s (j.symm i')) := by
  refine SetLike.ext fun x => ?_
  rw [mem_arrangementCone_iff_specializes (φ := fun i => φ (j i)),
    mem_arrangementCone_iff_specializes (φ := φ)]
  exact ⟨fun h i' => by simpa using h (j.symm i'), fun h i => by simpa using h (j i)⟩

/-- **The cells do not depend on how the index set is named** (`arrangementCone_reindex`). -/
theorem arrangementCells_reindex {ι' : Type*} {φ : ι' → (realified V₁) →L[ℝ] ℝ}
    (j : ι ≃ ι') (Cplus : PointedCone ℝ (realified V₁)) :
    arrangementCells (fun i => φ (j i)) Cplus = arrangementCells φ Cplus := by
  refine Set.Subset.antisymm ?_ ?_
  · rintro - ⟨s, rfl⟩
    exact ⟨fun i' => s (j.symm i'), by rw [arrangementCone_reindex j s]⟩
  · rintro - ⟨t, rfl⟩
    refine ⟨fun i => t (j i), ?_⟩
    rw [arrangementCone_reindex j (fun i => t (j i))]
    simp

/-- **The arrangement decomposition does not depend on how the index set is named.** This is what
lets the two-space transport above be applied to the walls of two different fibres, whose index sets
— the hyperplanes of `H` containing `I` and those containing `gI` — are different subtypes of one
index set. -/
theorem arrangementDecomposition_reindex {ι' : Type*}
    {φ : ι' → (realified V₁) →L[ℝ] ℝ} (j : ι ≃ ι')
    (Cplus : PointedCone ℝ (realified V₁)) :
    arrangementDecomposition (fun i => φ (j i)) Cplus = arrangementDecomposition φ Cplus := by
  rw [arrangementDecomposition, arrangementDecomposition, arrangementCells_reindex j]

end TransportBetweenSpaces

/-! ## `Γ`-invariance of `Σ(H)` for a `Γ`-equivariant family of forms

Example 6.4 asks the collection `Σ(H)` to be `Γ`-invariant (Definition 6.1), and `H` there is a
finite union of `Γ`-orbits, so `Γ` permutes the hyperplanes of `H`: for each `g ∈ Γ` there is a
permutation `ρ` of the index set with the form of `H (ρ i)` the form of `H i` transported along
`g`, up to a nonzero rational scalar (`ψ (ρ i) (g y) = d i * ψ i y`). Under that hypothesis the
decomposition of one fibre is carried to the decomposition of the image fibre by the carrier
isometry of `Semifan.fibreCarrierEquivReal`, which is what `IsGammaInvariantLocus` asks for at the
level of the members. -/

section GammaInvarianceArrangement

variable {BQ : LinearMap.BilinForm ℚ V} {Q : QuadraticForm ℝ (realified V)}
  {ψ : ι → V →ₗ[ℚ] ℚ} {g : V ≃ₗ[ℚ] V} {ρ : ι ≃ ι} {d : ι → ℚ}

omit [Module.Finite ℚ V] in
/-- **A `Γ`-equivariant family of `ℚ`-linear forms has equivariant realifications.** Both sides are
`ℝ`-linear in `y` and agree on the `ℚ`-rational points, which span `V(ℝ)`. -/
theorem realifiedForm_equivariant (hψ : ∀ i (y : V), ψ (ρ i) (g y) = d i * ψ i y) (i : ι)
    (y : realified V) :
    realifiedForm (ψ (ρ i)) (realifiedEquiv g y) = (d i : ℝ) * realifiedForm (ψ i) y := by
  let L : realified V →ₗ[ℝ] ℝ :=
    (realifiedForm (ψ (ρ i))).comp (realifiedEquiv g).toLinearMap - (d i : ℝ) • realifiedForm (ψ i)
  have hL : ∀ x : V, L (rationalPoint x) = 0 := by
    intro x
    change realifiedForm (ψ (ρ i)) (realifiedEquiv g (rationalPoint x))
      - (d i : ℝ) * realifiedForm (ψ i) (rationalPoint x) = 0
    rw [realifiedEquiv_rationalPoint, realifiedForm_rationalPoint, realifiedForm_rationalPoint,
      hψ i x]
    push_cast
    ring
  have hzero : L = 0 := by
    have hle : Submodule.span ℝ (Set.range (rationalPoint (V := V))) ≤ L.ker := by
      rw [Submodule.span_le]
      rintro - ⟨x, rfl⟩
      simpa using hL x
    rw [span_range_rationalPoint, top_le_iff] at hle
    exact LinearMap.ext fun z => by
      have hz : z ∈ L.ker := by rw [hle]; exact Submodule.mem_top
      simpa using hz
  have h := congrArg (fun f : realified V →ₗ[ℝ] ℝ => f y) hzero
  change realifiedForm (ψ (ρ i)) (realifiedEquiv g y) - (d i : ℝ) * realifiedForm (ψ i) y = 0 at h
  rw [sub_eq_zero] at h
  exact h

omit [Module.Finite ℚ V] in
/-- **The trace of a hyperplane is carried to the trace of the image hyperplane**: on the carriers
of two `Γ`-related fibres, the forms of the family agree under the carrier isometry, up to the
scalars `d`. This is the `hφ` input of `map_arrangementDecomposition` for `Σ(H)`. -/
theorem fibreFormC_fibreCarrierEquivReal (F : ConicalLine BQ Q)
    (hBQ : ∀ u w : V, (associated Q) (rationalPoint u) (rationalPoint w) = (BQ u w : ℝ))
    (hg : ∀ x y : V, BQ (g x) (g y) = BQ x y)
    (hψ : ∀ i (y : V), ψ (ρ i) (g y) = d i * ψ i y) (i : ι)
    (y : realified ↥(planeComplement BQ F.gen F.partner)) :
    fibreFormC (ConicalLine.map F hBQ hg) (ψ (ρ i))
        (fibreCarrierEquivReal (Q := Q) (g := g) F hg y) =
      (d i : ℝ) * fibreFormC F (ψ i) y := by
  rw [fibreFormC_apply, fibreFormC_apply, realifyMap_fibreCarrierEquivReal]
  exact realifiedForm_equivariant hψ i _

/-- **`Γ` permutes the hyperplanes of `H` containing a given isotropic line**: the walls of the
fibre of `I` are carried onto the walls of the fibre of `gI` by the permutation of the index set,
because `ψ i` vanishes on `I` exactly when `ψ (ρ i)` vanishes on `gI`. -/
noncomputable def fibreWallsEquiv (F : ConicalLine BQ Q)
    (hBQ : ∀ u w : V, (associated Q) (rationalPoint u) (rationalPoint w) = (BQ u w : ℝ))
    (hg : ∀ x y : V, BQ (g x) (g y) = BQ x y) (hd : ∀ i, d i ≠ 0)
    (hψ : ∀ i (y : V), ψ (ρ i) (g y) = d i * ψ i y) :
    fibreWalls ψ F ≃ fibreWalls ψ (ConicalLine.map F hBQ hg) :=
  Equiv.subtypeEquiv ρ fun i => by
    constructor
    · rintro h x ⟨y, hy, rfl⟩
      change ψ (ρ i) (g y) = 0
      rw [hψ i y, h hy, mul_zero]
    · intro h x hx
      have hx' : g x ∈ F.line.map (g : V →ₗ[ℚ] V) := Submodule.mem_map_of_mem hx
      have h1 : ψ (ρ i) (g x) = 0 := h hx'
      have h2 := hψ i x
      rw [h1] at h2
      exact (mul_eq_zero.1 h2.symm).resolve_left (hd i)

omit [Module.Finite ℚ V] in
theorem fibreWallsEquiv_coe (F : ConicalLine BQ Q)
    (hBQ : ∀ u w : V, (associated Q) (rationalPoint u) (rationalPoint w) = (BQ u w : ℝ))
    (hg : ∀ x y : V, BQ (g x) (g y) = BQ x y) (hd : ∀ i, d i ≠ 0)
    (hψ : ∀ i (y : V), ψ (ρ i) (g y) = d i * ψ i y) (i : fibreWalls ψ F) :
    ((fibreWallsEquiv (ρ := ρ) (d := d) F hBQ hg hd hψ i :
      fibreWalls ψ (ConicalLine.map F hBQ hg)) : ι) = ρ i := rfl

omit [Module.Finite ℚ V] in
/-- **The traces of two corresponding walls agree under the carrier isometry, indexed by the
permutation of the walls of a fibre** (`fibreWallsEquiv_coe` applied to
`fibreFormC_fibreCarrierEquivReal`): this is the `hφ` input of `map_arrangementDecomposition` for
`Σ(H)`. -/
theorem fibreFormC_fibreWallsEquiv (F : ConicalLine BQ Q)
    (hBQ : ∀ u w : V, (associated Q) (rationalPoint u) (rationalPoint w) = (BQ u w : ℝ))
    (hg : ∀ x y : V, BQ (g x) (g y) = BQ x y) (hd : ∀ i, d i ≠ 0)
    (hψ : ∀ i (y : V), ψ (ρ i) (g y) = d i * ψ i y) (i : fibreWalls ψ F)
    (y : realified ↥(planeComplement BQ F.gen F.partner)) :
    fibreFormC (ConicalLine.map F hBQ hg)
        (ψ ↑(fibreWallsEquiv (ρ := ρ) (d := d) F hBQ hg hd hψ i))
        ((fibreCarrierEquivReal (Q := Q) (g := g) F hg).toLinearMap y) =
      (d ↑i : ℝ) * fibreFormC F (ψ ↑i) y := by
  rw [fibreWallsEquiv_coe (ρ := ρ) (d := d) F hBQ hg hd hψ i]
  simpa using fibreFormC_fibreCarrierEquivReal (ρ := ρ) (d := d) F hBQ hg hψ (↑i) y

/-- **Looijenga, Example 6.4, p. 29: `Σ(H)` is `Γ`-invariant**, for a `Γ`-equivariant family of
forms. `g` carries the fibre of `I` to the fibre of `gI` (`ConicalLine.map`), its rational closure
`C_{I,+}` onto the closure of the image fibre (`ConicalLine.map_closure`), and — because the traces
of the walls correspond under the carrier isometry (`fibreFormC_fibreCarrierEquivReal`) and the
walls themselves correspond under the permutation of the index set (`fibreWallsEquiv`) — the members
of `Σ(H)` in the one fibre onto the members of `Σ(H)` in the other
(`map_arrangementDecomposition`). -/
theorem semifanArrangement_gammaInvariant
    (hBQ : ∀ u w : V, (associated Q) (rationalPoint u) (rationalPoint w) = (BQ u w : ℝ))
    (Γ : Set (V ≃ₗ[ℚ] V)) (ψ : ι → V →ₗ[ℚ] ℚ)
    (hequiv : ∀ g ∈ Γ, ∃ (ρ : ι ≃ ι) (d : ι → ℚ), (∀ i, d i ≠ 0) ∧
      ∀ i (y : V), ψ (ρ i) (g y) = d i * ψ i y)
    (hpos : ∀ F : ConicalLine BQ Q,
      sigPos (fibreForm Q (planeComplement BQ F.gen F.partner)) = 1) :
    IsGammaInvariantLocus BQ Q Γ (semifanArrangement ψ) := by
  intro g hgΓ hg F
  obtain ⟨ρ, d, hd, hψ⟩ := hequiv g hgΓ
  have hclos := ConicalLine.map_closure (Q := Q) (g := g) F hBQ hg (hpos F)
    (hpos (ConicalLine.map F hBQ hg)) (ConicalLine.map F hBQ hg).sheet_pos
  have hcells : (semifanArrangement ψ F).image
      (fun σ => σ.map (fibreCarrierEquivReal (Q := Q) (g := g) F hg).toLinearMap) =
      semifanArrangement ψ (ConicalLine.map F hBQ hg) := by
    change (arrangementDecomposition (fun i : fibreWalls ψ F => fibreFormC F (ψ i)) F.closure).image
        (fun σ => σ.map (fibreCarrierEquivReal (Q := Q) (g := g) F hg).toLinearMap) =
      arrangementDecomposition (fun j : fibreWalls ψ (ConicalLine.map F hBQ hg) =>
        fibreFormC (ConicalLine.map F hBQ hg) (ψ j)) (ConicalLine.map F hBQ hg).closure
    rw [← arrangementDecomposition_reindex
      (φ := fun j : fibreWalls ψ (ConicalLine.map F hBQ hg) =>
        fibreFormC (ConicalLine.map F hBQ hg) (ψ j))
      (fibreWallsEquiv (Q := Q) (g := g) (ψ := ψ) (ρ := ρ) (d := d) F hBQ hg hd hψ)]
    exact map_arrangementDecomposition (ι := fibreWalls ψ F) (c := fun i => (d (↑i) : ℝ))
      (fun i => by exact_mod_cast hd (↑i))
      (fun i y => fibreFormC_fibreWallsEquiv (ρ := ρ) (d := d) F hBQ hg hd hψ i y) hclos
  refine ⟨ConicalLine.map F hBQ hg, rfl, ?_, ?_⟩
  · intro σ hσ
    refine ⟨σ.map (fibreCarrierEquivReal (Q := Q) (g := g) F hg).toLinearMap, ?_,
      memberImage_map_eq F hBQ hg σ⟩
    have hmem : σ.map (fibreCarrierEquivReal (Q := Q) (g := g) F hg).toLinearMap ∈
        (semifanArrangement ψ F).image
          (fun σ => σ.map (fibreCarrierEquivReal (Q := Q) (g := g) F hg).toLinearMap) :=
      Set.mem_image_of_mem _ hσ
    rwa [hcells] at hmem
  · intro σ' hσ'
    have hmem : σ' ∈ (semifanArrangement ψ F).image
        (fun σ => σ.map (fibreCarrierEquivReal (Q := Q) (g := g) F hg).toLinearMap) := by
      rw [hcells]; exact hσ'
    obtain ⟨σ, hσ, hσeq⟩ := hmem
    refine ⟨σ, hσ, ?_⟩
    rw [← hσeq]
    exact memberImage_map_eq F hBQ hg σ

end GammaInvarianceArrangement

/-! ## The walls of `Σ(H)` at a fibre are the normal forms of the projected normals

The counting lemma of #161 is stated for a family of `ℚ`-linear forms `BQ v` (the normal forms of
the normals `v` of the hyperplanes) over a lattice `Λ`. Example 4.3 (b), p. 18
(`.tmp-sources/looijenga-math0201218v2.md:491`), is applied at the fibre in Example 6.4, p. 29
(`.tmp-sources/looijenga-math0201218v2.md:791`: "the `H ∈ H` containing `I` correspond to
`ℚ`-hyperplanes in `I^⊥/I ⊗ I` of signature `(1, n-2)` and so according to example 4.3-b these
decompose `C_{I,+}`"), so the family at the fibre has to be recognised as a family of normal forms
over the reduced lattice `(Λ ⊓ I^⊥)/(Λ ⊓ I)`. What follows is that recognition:

* `fibreFormC_bilinForm`: the trace on the fibre of the wall of `v` is the normal form of the
  projection of `v` to the complement of the hyperbolic plane;
* `fibreForm_fibreProj`: for `v ⊥ I` the *norm* of that projection in the fibre's form is the norm
  of `v` in the ambient form — which is what lets the finite set of norms of the ambient orbit
  family (`finite_form_values_of_orbitFamily`) serve at every fibre, since
  `(v - (v·f) e)·(v - (v·f) e) = v·v` when `v·e = 0`.
-/

section FibreNormals

variable {BQ : LinearMap.BilinForm ℚ V} {Q : QuadraticForm ℝ (realified V)}

omit [Module.Finite ℚ V] in
/-- The projection of a vector to the complement of the hyperbolic plane, written out. -/
theorem fibreProj_val (hBsym : BQ.IsSymm) (F : ConicalLine BQ Q) (v : V) :
    ((fibreProj hBsym F v : ↥F.space) : V)
      = v - BQ v F.partner • F.gen - BQ v F.gen • F.partner := rfl

omit [Module.Finite ℚ V] in
/-- **The trace of the hyperplane of `BQ v` on a fibre is the normal form of the projected
normal.** This is the identification which makes the walls of `Σ(H)` at a fibre the arrangement of
the normals `fibreProj v` over the reduced lattice. -/
theorem fibreFormC_bilinForm (hBsym : BQ.IsSymm)
    (hBQ : ∀ u w : V, (associated Q) (rationalPoint u) (rationalPoint w) = (BQ u w : ℝ))
    (F : ConicalLine BQ Q) (v : V) :
    fibreFormC F (BQ v) =
      normalForm (fibreForm Q F.space) (fibreProj hBsym F v) := by
  refine ContinuousLinearMap.ext fun x => ?_
  let L : realified ↥F.space →ₗ[ℝ] ℝ :=
    (fibreFormC F (BQ v)).toLinearMap -
      (normalForm (fibreForm Q F.space) (fibreProj hBsym F v)).toLinearMap
  have hproj : ∀ w : ↥F.space,
      BQ ((fibreProj hBsym F v : ↥F.space) : V) (w : V) = BQ v (w : V) := by
    intro w
    have hw := (ConicalLine.mem_space_iff (F := F)).1 w.2
    rw [fibreProj_val hBsym F v]
    simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul,
      hw.1, hw.2, mul_zero, sub_zero]
  have hL : ∀ w : ↥F.space, L (rationalPoint w) = 0 := by
    intro w
    have h1 : fibreFormC F (BQ v) (rationalPoint w) = (BQ v (w : V) : ℝ) := by
      rw [fibreFormC_apply, realifyMap_rationalPoint, realifiedForm_rationalPoint]
    have h2 : normalForm (fibreForm Q F.space) (fibreProj hBsym F v) (rationalPoint w)
        = (BQ v (w : V) : ℝ) := by
      rw [normalForm_apply, associated_fibreForm, realifyMap_rationalPoint,
        realifyMap_rationalPoint, hBQ, hproj]
    change fibreFormC F (BQ v) (rationalPoint w)
      - normalForm (fibreForm Q F.space) (fibreProj hBsym F v) (rationalPoint w) = 0
    rw [h1, h2, sub_self]
  have hzero : L = 0 := by
    have hle : Submodule.span ℝ (Set.range (rationalPoint (V := ↥F.space))) ≤ L.ker := by
      rw [Submodule.span_le]
      rintro - ⟨w, rfl⟩
      simpa using hL w
    rw [span_range_rationalPoint, top_le_iff] at hle
    exact LinearMap.ext fun z => by
      have hz : z ∈ L.ker := by rw [hle]; exact Submodule.mem_top
      simpa using hz
  have := congrArg (fun f : realified ↥F.space →ₗ[ℝ] ℝ => f x) hzero
  change fibreFormC F (BQ v) x
    - normalForm (fibreForm Q F.space) (fibreProj hBsym F v) x = 0 at this
  exact sub_eq_zero.1 this

omit [Module.Finite ℚ V] in
/-- **The norm of the projected normal is the ambient norm**, for a normal orthogonal to the
isotropic line `I`: the projection `v - (v·f) e` differs from `v` by a vector in the radical of the
form on `I^⊥`, so the fibre's form at it takes the value the ambient form takes at `v`. This is what
lets the finite set of norms of `finite_form_values_of_orbitFamily` be used at every fibre. -/
theorem fibreForm_fibreProj (hBsym : BQ.IsSymm)
    (hBQ : ∀ u w : V, (associated Q) (rationalPoint u) (rationalPoint w) = (BQ u w : ℝ))
    (F : ConicalLine BQ Q) {v : V} (hv : BQ F.gen v = 0) :
    fibreForm Q F.space (rationalPoint (fibreProj hBsym F v)) = (BQ v v : ℝ) := by
  rw [fibreForm_rationalPoint hBQ]
  have hv' : BQ v F.gen = 0 := by rw [hBsym.eq]; exact hv
  have hval : ((fibreProj hBsym F v : ↥F.space) : V)
      = v - BQ v F.partner • F.gen := by
    rw [fibreProj_val hBsym F v, hv', zero_smul, sub_zero]
  have hcalc : BQ (v - BQ v F.partner • F.gen) (v - BQ v F.partner • F.gen) = BQ v v := by
    have h1 : BQ (v - BQ v F.partner • F.gen) = BQ v - (BQ v F.partner) • BQ F.gen := by
      rw [map_sub, map_smul]
    rw [h1]
    simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul,
      hv', hv, F.gen_iso, mul_zero, sub_zero]
  rw [hval, hcalc]

end FibreNormals

/-! ## The reduced lattice of a conical fibre

Looijenga §1B, p. 11 (text line 251): for a `ℚ`-isotropic line `I` the reduction `I^⊥/I` carries the
lattice `(Λ ⊓ I^⊥)/(Λ ⊓ I)`, and Example 4.3 (b) at the fibre — the input to condition (i) of
Definition 6.1 for `Σ(H)` (Example 6.4, p. 29, text line 791) — runs on that lattice. This section
is it, as a `ℤ`-module in the carrier `⟨e, f⟩^⊥` of `ConicalLine.space`:

* `fibreProjLinear`: the hyperbolic projection `x ↦ x - (x·f) e - (x·e) f` as a `ℚ`-linear map, of
  which `fibreProj` is the underlying function;
* `reducedLattice`: the reduction `(Λ ⊓ I^⊥)/(Λ ⊓ I)` as the image of `Λ ⊓ I^⊥` under it — the
  projection kills exactly `I` on `I^⊥` (`span_inf_restrictScalars`), so the image *is* the
  quotient;
* `isLattice_reducedLattice`: the reduced lattice is a `ℤ`-lattice in the fibre's carrier, hence
  `exists_basis_reducedLattice`: the fibre has a `ℚ`-basis whose `ℤ`-span is the reduced lattice.
  That basis is the one Example 4.3 (b) takes (`cutsFinitelyOnRational_of_finiteNormValues`);
* `pairing_fibreProj` and `integral_reducedLattice`: the fibre's pairing of two projected normals is
  the ambient pairing, so an ambient form integral on `Λ` is integral on the reduced lattice (and
  `fibreForm_fibreProj` is the same statement for norms). -/

section ReducedLattice

variable {BQ : LinearMap.BilinForm ℚ V} {Q : QuadraticForm ℝ (realified V)}

/-- **A lattice in a `ℚ`-vector space is the `ℤ`-span of a `ℚ`-basis.** On a `ℤ`-basis of the
lattice
(`Submodule.IsLattice.free`), `Module.Basis.extendOfIsLattice` is a `ℚ`-basis of the ambient space,
and the `ℤ`-span of its values is the lattice. This is the form in which the counting lemma of
Example 4.3 (b) takes its lattice (`cutsFinitelyOnRational_of_finiteNormValues`). -/
theorem exists_basis_span_eq_of_isFullLattice {W : Type} [AddCommGroup W] [Module ℚ W]
    (M : Submodule ℤ W) [Submodule.IsFullLattice ℚ M] :
    ∃ (κ : Type) (_ : Fintype κ) (b : Module.Basis κ ℚ W),
      Submodule.span ℤ (Set.range b) = M := by
  classical
  obtain ⟨b, hb⟩ := Submodule.IsLattice.exists_basis_linearIndependent (K := ℚ) (M := M)
  have hrange : Set.range (fun i => (b i).val) = M.subtype '' Set.range b := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨b i, ⟨i, rfl⟩, rfl⟩
    · rintro ⟨y, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, rfl⟩
  have hspan : Submodule.span ℤ (Set.range (fun i => (b i).val)) = M := by
    rw [hrange, ← Submodule.map_span, b.span_eq, Submodule.map_subtype_top]
  have hsp : (⊤ : Submodule ℚ W) ≤ Submodule.span ℚ (Set.range (fun i => (b i).val)) := by
    rw [← Submodule.span_span_of_tower (R := ℤ) (S := ℚ)
      (s := Set.range (fun i => (b i).val)), hspan, Submodule.IsFullLattice.span_eq_top]
  refine ⟨Fin (Module.finrank ℤ ↥M), inferInstance,
    Module.Basis.mk (v := fun i => (b i).val) hb hsp, ?_⟩
  simpa using hspan

omit [Module.Finite ℚ V] in
/-- **A lattice meets every `ℚ`-subspace in a submodule whose rational span is the whole
subspace**: an element of the subspace is a rational combination of lattice vectors, and clearing
denominators puts it in the intersection. -/
theorem span_inf_restrictScalars {κ : Type} [Finite κ] (bs : Module.Basis κ ℚ V)
    (K : Submodule ℚ V) :
    Submodule.span ℚ ((Submodule.span ℤ (Set.range bs) ⊓ K.restrictScalars ℤ :
      Submodule ℤ V) : Set V) = K := by
  classical
  have hint : Fintype κ := Fintype.ofFinite κ
  refine le_antisymm (Submodule.span_le.2 ?_) ?_
  · rintro x ⟨-, hx⟩
    exact hx
  · intro x hx
    obtain ⟨D, hDpos, hD⟩ := exists_nat_smul_mem_span bs x
    have hmem : ((D : ℤ) • x : V) ∈
        Submodule.span ℤ (Set.range bs) ⊓ K.restrictScalars ℤ :=
      ⟨hD, Submodule.smul_mem _ _ hx⟩
    have hcast : ((D : ℚ)⁻¹) • ((D : ℤ) • x) = x := by
      rw [← Int.cast_smul_eq_zsmul (R := ℚ) (D : ℤ) x, smul_smul, Int.cast_natCast]
      have hD' : ((D : ℚ)) ≠ 0 := by exact_mod_cast hDpos.ne'
      rw [inv_mul_cancel₀ hD', one_smul]
    rw [← hcast]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hmem)

/-- The hyperbolic projection `x ↦ x - (x·f) e - (x·e) f` to the carrier of a conical fibre, as a
`ℚ`-linear map: the linear structure of `fibreProj`. -/
noncomputable def fibreProjLinear (hBsym : BQ.IsSymm) (F : ConicalLine BQ Q) :
    V →ₗ[ℚ] ↥F.space :=
  LinearMap.codRestrict _
    ((LinearMap.id : V →ₗ[ℚ] V) - (BQ.flip F.partner).smulRight F.gen
      - (BQ.flip F.gen).smulRight F.partner) fun v => by
    have hval : ((LinearMap.id : V →ₗ[ℚ] V) - (BQ.flip F.partner).smulRight F.gen
        - (BQ.flip F.gen).smulRight F.partner) v
        = v - BQ v F.partner • F.gen - BQ v F.gen • F.partner := by
      simp
    rw [hval]
    exact (fibreProj hBsym F v).2

omit [Module.Finite ℚ V] in
theorem fibreProjLinear_apply (hBsym : BQ.IsSymm) (F : ConicalLine BQ Q) (v : V) :
    ((fibreProjLinear hBsym F v : ↥F.space) : V)
      = v - BQ v F.partner • F.gen - BQ v F.gen • F.partner := by
  simp [fibreProjLinear]

omit [Module.Finite ℚ V] in
/-- The linear projection is the function `fibreProj`. -/
theorem fibreProjLinear_eq_fibreProj (hBsym : BQ.IsSymm) (F : ConicalLine BQ Q) (v : V) :
    fibreProjLinear hBsym F v = fibreProj hBsym F v :=
  Subtype.ext (by rw [fibreProjLinear_apply, fibreProj_val])

omit [Module.Finite ℚ V] in
/-- **The hyperbolic projection fixes the fibre's carrier pointwise**: a vector orthogonal to both
`e` and `f` is not moved. -/
theorem fibreProjLinear_self (hBsym : BQ.IsSymm) (F : ConicalLine BQ Q) (w : ↥F.space) :
    fibreProjLinear hBsym F w = w := by
  refine Subtype.ext ?_
  rw [fibreProjLinear_apply]
  have h1 : BQ F.gen (w : V) = 0 := ((ConicalLine.mem_space_iff (F := F)).1 w.2).1
  have h2 : BQ F.partner (w : V) = 0 := ((ConicalLine.mem_space_iff (F := F)).1 w.2).2
  have h3 : BQ (w : V) F.gen = 0 := by rw [hBsym.eq]; exact h1
  have h4 : BQ (w : V) F.partner = 0 := by rw [hBsym.eq]; exact h2
  rw [h3, h4, zero_smul, zero_smul, sub_zero, sub_zero]

/-- **The reduced lattice of a conical fibre** — the reduction `(Λ ⊓ I^⊥)/(Λ ⊓ I)` of Looijenga
§1B, p. 11, as the image of `Λ ⊓ I^⊥` under the hyperbolic projection. The projection kills `I` and
nothing else on `I^⊥`, so the image is the quotient; `span_inf_restrictScalars` records that the
intersection is not smaller than the lattice requires. -/
noncomputable def reducedLattice (hBsym : BQ.IsSymm) (F : ConicalLine BQ Q)
    (Λ : Submodule ℤ V) : Submodule ℤ ↥F.space :=
  Submodule.map ((fibreProjLinear hBsym F).restrictScalars ℤ)
    (Λ ⊓ (LinearMap.ker (BQ F.gen)).restrictScalars ℤ)

omit [Module.Finite ℚ V] in
theorem coe_reducedLattice (hBsym : BQ.IsSymm) (F : ConicalLine BQ Q) (Λ : Submodule ℤ V) :
    (reducedLattice hBsym F Λ : Set ↥F.space) = fibreProjLinear hBsym F ''
      (Λ ⊓ (LinearMap.ker (BQ F.gen)).restrictScalars ℤ : Set V) := rfl

omit [Module.Finite ℚ V] in
/-- **The reduced lattice is a full `ℤ`-lattice in the fibre's carrier** (Looijenga §1B, p. 11):
it is finitely generated — the image of `Λ ⊓ I^⊥`, a submodule of a finitely generated
`ℤ`-module — and it spans the carrier over `ℚ`, because `Λ ⊓ I^⊥` spans `I^⊥`
(`span_inf_restrictScalars`) and the projection maps `I^⊥` onto the carrier. -/
theorem isFullLattice_reducedLattice (hBsym : BQ.IsSymm) (F : ConicalLine BQ Q) {κ : Type}
    [Finite κ] (bs : Module.Basis κ ℚ V) :
    Submodule.IsFullLattice ℚ (reducedLattice hBsym F (Submodule.span ℤ (Set.range bs))) := by
  have hΛ : Submodule.IsLattice ℚ (Submodule.span ℤ (Set.range bs)) :=
    Submodule.IsLattice.of_fg (K := ℚ) (Submodule.fg_span (Set.finite_range bs))
  have hfg : (reducedLattice hBsym F (Submodule.span ℤ (Set.range bs))).FG :=
    Submodule.FG.map ((fibreProjLinear hBsym F).restrictScalars ℤ)
      (Submodule.IsLattice.fg ℚ (Submodule.span ℤ (Set.range bs) ⊓
        (LinearMap.ker (BQ F.gen)).restrictScalars ℤ))
  have hlat := Submodule.IsLattice.of_fg (K := ℚ) hfg
  refine { fg := hlat.fg, linearIndepOn := hlat.linearIndepOn, span_eq_top := ?_ }
  · have hcoe : (reducedLattice hBsym F (Submodule.span ℤ (Set.range bs)) : Set ↥F.space) =
        fibreProjLinear hBsym F ''
          ((Submodule.span ℤ (Set.range bs) ⊓
            (LinearMap.ker (BQ F.gen)).restrictScalars ℤ : Submodule ℤ V) : Set V) := rfl
    have htop : Submodule.map (fibreProjLinear hBsym F)
        (Submodule.span ℚ ((Submodule.span ℤ (Set.range bs) ⊓
          (LinearMap.ker (BQ F.gen)).restrictScalars ℤ : Submodule ℤ V) : Set V)) = ⊤ := by
      rw [span_inf_restrictScalars (V := V) bs (LinearMap.ker (BQ F.gen))]
      refine eq_top_iff.2 fun w _ => ?_
      have hw : (w : V) ∈ LinearMap.ker (BQ F.gen) :=
        LinearMap.mem_ker.mpr (((ConicalLine.mem_space_iff (F := F)).1 w.2).1)
      exact Submodule.mem_map.2 ⟨(w : V), hw, fibreProjLinear_self hBsym F w⟩
    have hmap := Submodule.map_span (fibreProjLinear hBsym F)
      ((Submodule.span ℤ (Set.range bs) ⊓
        (LinearMap.ker (BQ F.gen)).restrictScalars ℤ : Submodule ℤ V) : Set V)
    rw [hcoe]
    exact hmap.symm.trans htop

omit [Module.Finite ℚ V] in
/-- **The fibre has a `ℚ`-basis whose `ℤ`-span is the reduced lattice** — the shape in which the
counting lemma of Example 4.3 (b) takes the fibre's lattice
(`cutsFinitelyOnRational_of_finiteNormValues`). -/
theorem exists_basis_reducedLattice (hBsym : BQ.IsSymm) (F : ConicalLine BQ Q) {κ : Type}
    [Finite κ] (bs : Module.Basis κ ℚ V) :
    ∃ (κ' : Type) (_ : Fintype κ') (bs' : Module.Basis κ' ℚ ↥F.space),
      Submodule.span ℤ (Set.range bs') =
        reducedLattice hBsym F (Submodule.span ℤ (Set.range bs)) := by
  have hfull : Submodule.IsFullLattice ℚ
      (reducedLattice hBsym F (Submodule.span ℤ (Set.range bs))) :=
    isFullLattice_reducedLattice hBsym F bs
  exact exists_basis_span_eq_of_isFullLattice
    (M := reducedLattice hBsym F (Submodule.span ℤ (Set.range bs)))

omit [Module.Finite ℚ V] in
/-- **The fibre's pairing of two projected normals is the ambient pairing**: for `u, w ⊥ I` the
projection changes each by a multiple of the isotropic generator `e`, which pairs to zero with
everything in `I^⊥`. -/
theorem pairing_fibreProj (hBsym : BQ.IsSymm) (F : ConicalLine BQ Q) {u w : V}
    (hu : BQ F.gen u = 0) (hw : BQ F.gen w = 0) :
    BQ (fibreProjLinear hBsym F u : V) (fibreProjLinear hBsym F w : V) = BQ u w := by
  have hu' : BQ u F.gen = 0 := by rw [hBsym.eq]; exact hu
  have hw' : BQ w F.gen = 0 := by rw [hBsym.eq]; exact hw
  have h1 : ((fibreProjLinear hBsym F u : ↥F.space) : V)
      = u - BQ u F.partner • F.gen := by
    rw [fibreProjLinear_apply, hu', zero_smul, sub_zero]
  have h2 : ((fibreProjLinear hBsym F w : ↥F.space) : V)
      = w - BQ w F.partner • F.gen := by
    rw [fibreProjLinear_apply, hw', zero_smul, sub_zero]
  have hexp : BQ (u - BQ u F.partner • F.gen)
      = BQ u - (BQ u F.partner) • BQ F.gen := by
    rw [map_sub, map_smul]
  rw [h1, h2, hexp]
  simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul,
    hu', hw, F.gen_iso, mul_zero, sub_zero]

omit [Module.Finite ℚ V] in
/-- **The fibre's form is integral on the reduced lattice**, when the ambient form is integral on
`Λ`: the pairing of two lattice vectors of the fibre is the ambient pairing of their preimages
(`pairing_fibreProj`). -/
theorem integral_reducedLattice (hBsym : BQ.IsSymm) (F : ConicalLine BQ Q) {κ : Type}
    [Finite κ] (bs : Module.Basis κ ℚ V)
    (hint : ∀ x ∈ Submodule.span ℤ (Set.range bs), ∀ y ∈ Submodule.span ℤ (Set.range bs),
      ∃ n : ℤ, BQ x y = (n : ℚ)) :
    ∀ x ∈ reducedLattice hBsym F (Submodule.span ℤ (Set.range bs)),
      ∀ y ∈ reducedLattice hBsym F (Submodule.span ℤ (Set.range bs)),
        ∃ n : ℤ, BQ (x : V) (y : V) = (n : ℚ) := by
  intro x hx y hy
  rw [reducedLattice, Submodule.mem_map] at hx hy
  obtain ⟨u, hu, rfl⟩ := hx
  obtain ⟨w, hw, rfl⟩ := hy
  obtain ⟨n, hn⟩ := hint u hu.1 w hw.1
  exact ⟨n, by simpa using (pairing_fibreProj hBsym F hu.2 hw.2).trans hn⟩

end ReducedLattice

end LeanCategories.Lattices.Valued
