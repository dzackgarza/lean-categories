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
* **`CutsFinitelyOnRational` at the fibre is carried, not derived**:
  `semifanArrangement_isLocallyRational` takes it as a hypothesis. For the arithmetic `H` of the
  source it is `cutsFinitelyOnRational_orbitFamily` at the fibre's lattice, which is not
  instantiated here.
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

end LeanCategories.Lattices.Valued
