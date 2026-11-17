/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Lattices.Valued.FibreArithmetic

/-!
# Transfer of an ambient orbit of walls to a fibre's traces (#172)

Looijenga, *Compactifications defined by arrangements II*, arXiv math/0201218v2, Example 6.4,
p. 29: the walls of `Σ(ℋ)` in `C_{I,+}` are the traces on `I^⊥/I` of the hyperplanes of `ℋ`
containing `I`. The arrangement hypothesis of the source is ambient — `ℋ` is a finite union of
`Γ`-orbits of rational hyperplanes of `V` (Example 4.3 (b), pp. 17–18) — while the count of
`cutsFinitelyOnTraces_orbitFamily` is a count of hyperplanes *of the fibre*. The hypothesis `hsub`
of `semifanArrangement_arithmetic_fibre` (`FibreArithmetic.lean`) is exactly the missing transfer:
the traces of `ℋ` at `I` must be contained in a `Γ_I`-orbit family of a *finite* family of
`ℚ`-hyperplanes of `I^⊥/I`.

## The proposition

`I = ℚ F.gen` is a `ℚ`-isotropic line, `H = ker (BQ v)` is a rational wall through it
(`BQ v F.gen = 0`, so `v ∈ I^⊥` and `I ≤ H`), and `Γ` is a set of isometries of `V`. Write
`π : V → I^⊥/I` for the projection of §1B (the complement model `F.space` of `FibreArithmetic`).
The trace of the wall `gH` at `I` is the hyperplane `ker (restrictBilinForm BQ F.space (π (g v)))`
of the fibre (`fibreTrace_eq_ker_restrictBilinForm_proj`).

`ambientWallTrace_mem_orbitFamily` states: the traces of the walls of the `Γ`-orbit of `H` that
pass through `I` are a **single** `Γ_I`-orbit of hyperplanes of `I^⊥/I`.

## What makes the proof work, and what does not

The candidate hypothesis of #172 is transitivity of `Γ_I = Stab_Γ(I)` on the walls through `I`
inside one `Γ`-orbit. It is *not* used: it is neither necessary for the transfer nor, for an
infinite `Γ`, true — the record's `x^2 - 2y^2 = 1` observation is that an orbit of walls can meet
one fibre infinitely often. What the proof uses instead is **fibre-internal**:

* `hTrans`: the isometries of the fibre `I^⊥/I` are transitive on the normal vectors of a fixed
  fibre norm; and
* the **fibre norm of a trace normal is the ambient norm of the wall normal**,
  `fibreForm_fibreCarrierProj_of_gen_perp`: `q(π v) = q(v)` for `v ∈ I^⊥`. Since `g` is an
  isometry, `q(π (g v)) = q(g v) = q(v) = q(π v)`: every wall of the orbit has a trace normal of
  *the same* fibre norm, so a single fibre-transitivity statement suffices and no statement about
  the ambient walls through `I` is needed.

`U ⊕ U` (the worked instance of `CuspWorkedInstance.lean`) satisfies `hTrans` for **every** wall
normal, by the explicit diagonal and swap isometries of a hyperbolic plane (`hp_exists_isometry`,
`twoHyperbolicPlanes_ambientWallTrace_mem_orbitFamily`); the argument uses nothing about
arithmeticity and nothing about `exists_isometry_apply_eq`. What it does use is the **rank**: the
trace is a *line* of the two-dimensional fibre, and a line of a hyperbolic plane is determined up
to isometry by its value. In the source's rank the trace is a hyperplane of dimension `≥ 2` of a
`(1, n-1)` fibre, and the same determinant identity pins only its *discriminant*, so `hTrans`
becomes the arithmetic statement that an arithmetic group has finitely many orbits on the norm
level set (a genus/class-number statement, Borel–Harish-Chandra for the double cosets
`Γ_I \ O(I^⊥/I) / Stab`), which the tree does not contain. So `hsub` is derived at `U ⊕ U` and is
a genuine extra hypothesis for `I_{2,9}`; see the report in `results/issue-172-report.md`.

#167's `StabilizerTransitiveOnWallsThroughLine` (`FibreArithmetic.lean`, **(HT′)**) is the candidate
hypothesis in the shape of the ambient family, and it is neither used here nor available in general:
what the transfer needs is the fibre-internal `hTrans`. The statement below is also not literally
#167's `TraceOrbitCover`, whose `ΓI` must be the `fibreInducedEquiv`-image of `Stab_Γ(I)` for the
given `Γ`: `ΓI` here may be the whole isometry group of the fibre, and passing to a subgroup is the
arithmetic step the rank decides.
-/

@[expose] public section

open PointedCone QuadraticMap

open scoped TensorProduct

namespace LeanCategories.Lattices.Valued

variable {V : Type} [AddCommGroup V] [Module ℚ V] [Module.Finite ℚ V]

/-! ## The fibre norm of a wall normal is the ambient norm -/

section AmbientOrbitTransfer

variable {BQ : LinearMap.BilinForm ℚ V} {Q : QuadraticForm ℝ (realified V)}

omit [Module.Finite ℚ V] in
/-- **The fibre norm of a wall normal is the ambient norm.** For a wall through `I`
(`v ∈ I^⊥`, i.e. `BQ v F.gen = 0`) the projected normal `π v` has the same fibre norm as `v` has
ambiently: `π v = v - (v · partner) gen` differs from `v` by a multiple of the isotropic generator,
which has vanishing norm and pairs trivially with `I^⊥`. This is the step that makes the transfer
work: an isometry of `V` moves every wall of the orbit to a wall whose trace normal has the same
fibre norm. -/
theorem fibreForm_fibreCarrierProj_of_gen_perp
    (hBQ : ∀ u w : V, (associated Q) (rationalPoint u) (rationalPoint w) = (BQ u w : ℝ))
    (hBsym : BQ.IsSymm) (F : ConicalLine BQ Q) {v : V} (hv : BQ v F.gen = 0) :
    fibreForm Q F.space (rationalPoint (fibreCarrierProj hBsym F v)) = (BQ v v : ℝ) := by
  rw [fibreForm_rationalPoint hBQ F.space (fibreCarrierProj hBsym F v)]
  congr 1
  have hgen : BQ F.gen v = 0 := by rw [hBsym.eq]; exact hv
  have hval : ((fibreCarrierProj hBsym F v : ↥F.space) : V) = v - BQ F.partner v • F.gen := by
    rw [fibreCarrierProj_apply, hgen, zero_smul, sub_zero]
  rw [hval]
  simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
  rw [hv, hgen, F.gen_iso]
  ring

omit [Module.Finite ℚ V] in
/-- **The fibre value of a rational point is the restricted form's value**: the same statement as
`fibreForm_rationalPoint`, written for the `ℚ`-bilinear form of the fibre, which is the form whose
kernels are the fibre's hyperplanes. -/
theorem fibreForm_rationalPoint_eq_restrict
    (hBQ : ∀ u w : V, (associated Q) (rationalPoint u) (rationalPoint w) = (BQ u w : ℝ))
    {W : Submodule ℚ V} (x : ↥W) :
    fibreForm Q W (rationalPoint x) = ((restrictBilinForm BQ W x x : ℚ) : ℝ) := by
  rw [fibreForm_rationalPoint hBQ W x, restrictBilinForm_apply]

omit [Module.Finite ℚ V] in
/-- **Rescaling a normal does not move its zero set**: a wall is a hyperplane, so its normal is
defined only up to a nonzero scalar. -/
theorem ker_restrictBilinForm_smul {BQ : LinearMap.BilinForm ℚ V} (W : Submodule ℚ V)
    {w : ↥W} {c : ℚ} (hc : c ≠ 0) :
    LinearMap.ker (restrictBilinForm BQ W (c • w)) =
      LinearMap.ker (restrictBilinForm BQ W w) := by
  refine le_antisymm ?_ ?_
  · intro x hx
    simp only [LinearMap.mem_ker, restrictBilinForm_apply, map_smul, LinearMap.smul_apply,
      smul_eq_mul] at hx ⊢
    rcases mul_eq_zero.mp hx with h | h
    · exact absurd h hc
    · exact h
  · intro x hx
    simp only [LinearMap.mem_ker, restrictBilinForm_apply, map_smul, LinearMap.smul_apply,
      smul_eq_mul] at hx ⊢
    rw [hx, mul_zero]

omit [Module.Finite ℚ V] in
/-- **An isometry of the fibre carries the zero set of a normal by its action**: for a `ℚ`-linear
equivalence `e` of the fibre preserving the restricted form, the trace of the wall whose normal is
`e w` is the image under `e` of the trace of the wall whose normal is `w`. This is the
`Γ_I`-equivariance of the trace, at the level of the fibre alone — the statement that the trace of
`gH` at `I` is the image of the trace of `H` at `I` under the induced action of `g ∈ Γ_I`. -/
theorem ker_restrictBilinForm_map {BQ : LinearMap.BilinForm ℚ V} (W : Submodule ℚ V)
    (e : ↥W ≃ₗ[ℚ] ↥W)
    (he : ∀ x y : ↥W, restrictBilinForm BQ W (e x) (e y) = restrictBilinForm BQ W x y)
    (w : ↥W) :
    LinearMap.ker (restrictBilinForm BQ W (e w)) =
      Submodule.map (e : ↥W →ₗ[ℚ] ↥W) (LinearMap.ker (restrictBilinForm BQ W w)) := by
  have hkey : ∀ z : ↥W, restrictBilinForm BQ W (e w) z =
      restrictBilinForm BQ W w (e.symm z) := by
    intro z
    rw [← he w (e.symm z), e.apply_symm_apply]
  refine SetLike.ext ?_
  intro x
  rw [Submodule.mem_map]
  constructor
  · intro hx
    refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
    rw [LinearMap.mem_ker]
    rw [LinearMap.mem_ker, hkey] at hx
    exact hx
  · rintro ⟨y, hy, rfl⟩
    rw [LinearMap.mem_ker] at hy ⊢
    rw [hkey]
    simpa using hy

omit [Module.Finite ℚ V] in
/-- **The transfer of an ambient orbit of walls to the fibre's traces** (#172).

The hypotheses, all named:

* `hBQ`, `hBsym`: the ambient form is that of `Q` and is symmetric;
* `F`: the `ℚ`-isotropic line `I = ℚ F.gen` with its hyperbolic partner and sheet;
* `Γ`: a set of **isometries** of `V` (`hΓiso`) — the ambient group whose orbits the arrangement
  hypothesis of the source is stated on;
* `ΓI`: a set of **isometries of the fibre** `I^⊥/I` (`hΓIiso`) — in the intended reading the
  induced action `Γ_I → Γ̄_I` of the stabilizer of `I` (`fibreInducedEquiv`);
* `v₀`, `hwall₀`: the wall normal of `H₀ = ker (BQ v₀)`, so that `I ≤ H₀`;
* `hπ₀`: `H₀ ≠ I^⊥`, i.e. its trace is a genuine hyperplane of the fibre;
* `hTrans`: **the fibre-transitivity hypothesis** — every nonzero fibre vector whose value is that
  of `π v₀` is a nonzero multiple of a `Γ_I`-image of `π v₀`;
* `hg`, `hwall`, `hπg`: `g ∈ Γ`, the wall `gH₀` passes through `I`, and `gH₀ ≠ I^⊥`.

The conclusion is that the trace of `gH₀` at `I` lies in the `Γ_I`-orbit family of the single fibre
hyperplane `ker (restrictBilinForm BQ F.space (π v₀))` — the `Finset`-indexed `orbitFamily` whose
sets are the `hsub` of `cutsFinitelyOnTraces_orbitFamily`. No count on the ambient index set
appears: the `Finset` has one element. -/
theorem ambientWallTrace_mem_orbitFamily
    (hBQ : ∀ u w : V, (associated Q) (rationalPoint u) (rationalPoint w) = (BQ u w : ℝ))
    (hBsym : BQ.IsSymm) (F : ConicalLine BQ Q)
    (Γ : Set (V ≃ₗ[ℚ] V)) (ΓI : Set (↥F.space ≃ₗ[ℚ] ↥F.space))
    (hΓiso : ∀ g ∈ Γ, ∀ x y : V, BQ (g x) (g y) = BQ x y)
    (hΓIiso : ∀ e ∈ ΓI, ∀ x y : ↥F.space,
      restrictBilinForm BQ F.space (e x) (e y) = restrictBilinForm BQ F.space x y)
    {v₀ : V} (hwall₀ : BQ v₀ F.gen = 0) (_hπ₀ : fibreCarrierProj hBsym F v₀ ≠ 0)
    (hTrans : ∀ h : ↥F.space, h ≠ 0 →
      fibreForm Q F.space (rationalPoint h) =
        fibreForm Q F.space (rationalPoint (fibreCarrierProj hBsym F v₀)) →
      ∃ e ∈ ΓI, ∃ c : ℚ, c ≠ 0 ∧ h = c • e (fibreCarrierProj hBsym F v₀))
    {g : V ≃ₗ[ℚ] V} (hg : g ∈ Γ) (hwall : BQ (g v₀) F.gen = 0)
    (hπg : fibreCarrierProj hBsym F (g v₀) ≠ 0) :
    LinearMap.ker (restrictBilinForm BQ F.space (fibreCarrierProj hBsym F (g v₀))) ∈
      orbitFamily ({LinearMap.ker (restrictBilinForm BQ F.space
        (fibreCarrierProj hBsym F v₀))} : Finset (Submodule ℚ ↥F.space)) ΓI := by
  have hnorm : fibreForm Q F.space (rationalPoint (fibreCarrierProj hBsym F (g v₀))) =
      fibreForm Q F.space (rationalPoint (fibreCarrierProj hBsym F v₀)) := by
    rw [fibreForm_fibreCarrierProj_of_gen_perp hBQ hBsym F hwall,
      fibreForm_fibreCarrierProj_of_gen_perp hBQ hBsym F hwall₀, hΓiso g hg v₀ v₀]
  obtain ⟨e, he, c, hc, hce⟩ := hTrans (fibreCarrierProj hBsym F (g v₀)) hπg hnorm
  rw [mem_orbitFamily]
  refine ⟨LinearMap.ker (restrictBilinForm BQ F.space (fibreCarrierProj hBsym F v₀)),
    Finset.mem_singleton_self _, e, he, ?_⟩
  rw [hce, ker_restrictBilinForm_smul F.space hc,
    ker_restrictBilinForm_map F.space e (hΓIiso e he)]

end AmbientOrbitTransfer


/-! ## The verdict on `U ⊕ U` -/

section TwoHyperbolicPlanes

/-- The bilinear form of `U ⊕ U` on `Fin 4 → ℚ` — the rational form of `twoHyperbolicPlanes`
(`CuspWorkedInstance.lean`) in split coordinates: `x · y = x₀y₁ + x₁y₀ + x₂y₃ + x₃y₂`. -/
noncomputable def uuForm : LinearMap.BilinForm ℚ (Fin 4 → ℚ) :=
  LinearMap.mk₂ ℚ (fun x y => x 0 * y 1 + x 1 * y 0 + x 2 * y 3 + x 3 * y 2)
    (fun x y z => by simp only [Pi.add_apply]; ring)
    (fun a x y => by simp only [Pi.smul_apply, smul_eq_mul]; ring)
    (fun x y z => by simp only [Pi.add_apply]; ring)
    (fun a x y => by simp only [Pi.smul_apply, smul_eq_mul]; ring)

theorem uuForm_apply (x y : Fin 4 → ℚ) :
    uuForm x y = x 0 * y 1 + x 1 * y 0 + x 2 * y 3 + x 3 * y 2 := rfl

theorem uuForm_isSymm : uuForm.IsSymm :=
  ⟨fun x y => by rw [uuForm_apply, uuForm_apply]; ring⟩

/-- The isotropic generator `e₀` of the standard line `I`. -/
def uue0 : Fin 4 → ℚ := ![1, 0, 0, 0]
/-- The hyperbolic partner of `e₀`. -/
def uue1 : Fin 4 → ℚ := ![0, 1, 0, 0]
/-- The first vector of the fibre `I^⊥/I ≅ ⟨e₂, e₃⟩`. -/
def uue2 : Fin 4 → ℚ := ![0, 0, 1, 0]
/-- The second vector of the fibre `I^⊥/I ≅ ⟨e₂, e₃⟩`. -/
def uue3 : Fin 4 → ℚ := ![0, 0, 0, 1]

theorem uuForm_uue0 (x : Fin 4 → ℚ) : uuForm uue0 x = x 1 := by
  rw [uuForm_apply]; simp [uue0]

theorem uuForm_uue1 (x : Fin 4 → ℚ) : uuForm uue1 x = x 0 := by
  rw [uuForm_apply]; simp [uue1]

variable {Q : QuadraticForm ℝ (realified (Fin 4 → ℚ))}

theorem uu_mem_space_coords {F : ConicalLine uuForm Q} (hgen : F.gen = uue0)
    (hpartner : F.partner = uue1) {x : Fin 4 → ℚ} (hx : x ∈ F.space) :
    x 0 = 0 ∧ x 1 = 0 := by
  rw [ConicalLine.mem_space_iff, hgen, hpartner] at hx
  exact ⟨by rw [← hx.2, uuForm_uue1], by rw [← hx.1, uuForm_uue0]⟩

theorem uu_eq_smul_of_mem_space {F : ConicalLine uuForm Q} (hgen : F.gen = uue0)
    (hpartner : F.partner = uue1) {x : Fin 4 → ℚ} (hx : x ∈ F.space) :
    x = x 2 • uue2 + x 3 • uue3 := by
  obtain ⟨h0, h1⟩ := uu_mem_space_coords hgen hpartner hx
  funext i
  fin_cases i <;> simp [h0, h1, uue2, uue3]

/-- **The carrier of the fibre of `I = ℚ e₀` is `ℚ²`**: the complement model
`planeComplement uuForm e₀ e₁` is the span of `e₂, e₃`, and a vector of it is determined by its last
two coordinates. -/
noncomputable def uuFibreEquiv {F : ConicalLine uuForm Q} (hgen : F.gen = uue0)
    (hpartner : F.partner = uue1) : ↥F.space ≃ₗ[ℚ] (Fin 2 → ℚ) where
  toFun x := ![x.1 2, x.1 3]
  invFun u := ⟨u 0 • uue2 + u 1 • uue3, by
    rw [ConicalLine.mem_space_iff, hgen, hpartner, uuForm_uue0, uuForm_uue1]
    simp [uue2, uue3]⟩
  left_inv := by
    intro x
    refine Subtype.ext ?_
    change (x.1 2) • uue2 + (x.1 3) • uue3 = (x : Fin 4 → ℚ)
    exact (uu_eq_smul_of_mem_space hgen hpartner x.2).symm
  right_inv := by
    intro u
    funext i
    fin_cases i <;> simp [uue2, uue3]
  map_add' := by
    intro x y
    funext i
    fin_cases i <;> simp
  map_smul' := by
    intro a x
    funext i
    fin_cases i <;> simp

@[simp] theorem uuFibreEquiv_apply {F : ConicalLine uuForm Q} (hgen : F.gen = uue0)
    (hpartner : F.partner = uue1) (x : ↥F.space) :
    uuFibreEquiv hgen hpartner x = ![x.1 2, x.1 3] := rfl

@[simp] theorem uuFibreEquiv_apply_zero {F : ConicalLine uuForm Q} (hgen : F.gen = uue0)
    (hpartner : F.partner = uue1) (x : ↥F.space) :
    uuFibreEquiv hgen hpartner x 0 = x.1 2 := rfl

@[simp] theorem uuFibreEquiv_apply_one {F : ConicalLine uuForm Q} (hgen : F.gen = uue0)
    (hpartner : F.partner = uue1) (x : ↥F.space) :
    uuFibreEquiv hgen hpartner x 1 = x.1 3 := rfl

/-- The form of the hyperbolic plane `⟨e₂, e₃⟩` in coordinates: `u₀v₁ + u₁v₀`. -/
def hpForm (u v : Fin 2 → ℚ) : ℚ := u 0 * v 1 + u 1 * v 0

theorem restrictBilinForm_uuFibreEquiv {F : ConicalLine uuForm Q} (hgen : F.gen = uue0)
    (hpartner : F.partner = uue1) (x y : ↥F.space) :
    restrictBilinForm uuForm F.space x y =
      hpForm (uuFibreEquiv hgen hpartner x) (uuFibreEquiv hgen hpartner y) := by
  obtain ⟨hx0, hx1⟩ := uu_mem_space_coords hgen hpartner x.2
  obtain ⟨hy0, hy1⟩ := uu_mem_space_coords hgen hpartner y.2
  rw [restrictBilinForm_apply, uuForm_apply]
  simp only [hpForm, uuFibreEquiv_apply_zero, uuFibreEquiv_apply_one, hx0, hx1, hy0, hy1,
    mul_zero, zero_add, add_zero]

/-! ### Transitivity of the isometries of a hyperbolic plane -/

/-- The diagonal isometry `(x, y) ↦ (s x, s⁻¹ y)` of the hyperbolic plane. -/
noncomputable def hpDiag (s : ℚ) (hs : s ≠ 0) : (Fin 2 → ℚ) ≃ₗ[ℚ] (Fin 2 → ℚ) where
  toFun u := ![s * u 0, s⁻¹ * u 1]
  invFun u := ![s⁻¹ * u 0, s * u 1]
  left_inv := by
    intro u
    funext i
    fin_cases i
    · change s⁻¹ * (s * u 0) = u 0
      rw [← mul_assoc, inv_mul_cancel₀ hs, one_mul]
    · change s * (s⁻¹ * u 1) = u 1
      rw [← mul_assoc, mul_inv_cancel₀ hs, one_mul]
  right_inv := by
    intro u
    funext i
    fin_cases i
    · change s * (s⁻¹ * u 0) = u 0
      rw [← mul_assoc, mul_inv_cancel₀ hs, one_mul]
    · change s⁻¹ * (s * u 1) = u 1
      rw [← mul_assoc, inv_mul_cancel₀ hs, one_mul]
  map_add' := by
    intro u v
    funext i
    fin_cases i <;> simp <;> ring
  map_smul' := by
    intro a u
    funext i
    fin_cases i <;> simp <;> ring

/-- The swap `(x, y) ↦ (y, x)` of the hyperbolic plane. -/
noncomputable def hpSwap : (Fin 2 → ℚ) ≃ₗ[ℚ] (Fin 2 → ℚ) where
  toFun u := ![u 1, u 0]
  invFun u := ![u 1, u 0]
  left_inv := by intro u; funext i; fin_cases i <;> rfl
  right_inv := by intro u; funext i; fin_cases i <;> rfl
  map_add' := by intro u v; funext i; fin_cases i <;> simp
  map_smul' := by intro a u; funext i; fin_cases i <;> simp

@[simp] theorem hpDiag_apply (s : ℚ) (hs : s ≠ 0) (u : Fin 2 → ℚ) :
    hpDiag s hs u = ![s * u 0, s⁻¹ * u 1] := rfl

@[simp] theorem hpSwap_apply (u : Fin 2 → ℚ) : hpSwap u = ![u 1, u 0] := rfl

@[simp] theorem hpDiag_apply_zero (s : ℚ) (hs : s ≠ 0) (u : Fin 2 → ℚ) :
    hpDiag s hs u 0 = s * u 0 := rfl

@[simp] theorem hpDiag_apply_one (s : ℚ) (hs : s ≠ 0) (u : Fin 2 → ℚ) :
    hpDiag s hs u 1 = s⁻¹ * u 1 := rfl

@[simp] theorem hpSwap_apply_zero (u : Fin 2 → ℚ) : hpSwap u 0 = u 1 := rfl

@[simp] theorem hpSwap_apply_one (u : Fin 2 → ℚ) : hpSwap u 1 = u 0 := rfl

theorem hpForm_hpDiag (s : ℚ) (hs : s ≠ 0) (u v : Fin 2 → ℚ) :
    hpForm (hpDiag s hs u) (hpDiag s hs v) = hpForm u v := by
  have h1 : s * u 0 * (s⁻¹ * v 1) = u 0 * v 1 := by
    rw [mul_mul_mul_comm, mul_inv_cancel₀ hs, one_mul]
  have h2 : s⁻¹ * u 1 * (s * v 0) = u 1 * v 0 := by
    rw [mul_mul_mul_comm, inv_mul_cancel₀ hs, one_mul]
  simp only [hpForm, hpDiag_apply_zero, hpDiag_apply_one]
  rw [h1, h2]

theorem hpForm_hpSwap (u v : Fin 2 → ℚ) :
    hpForm (hpSwap u) (hpSwap v) = hpForm u v := by
  simp only [hpForm, hpSwap_apply_zero, hpSwap_apply_one]
  ring

theorem hp_eq_zero_iff (u : Fin 2 → ℚ) : u = 0 ↔ u 0 = 0 ∧ u 1 = 0 := by
  constructor
  · rintro rfl
    exact ⟨rfl, rfl⟩
  · rintro ⟨h0, h1⟩
    funext i
    fin_cases i <;> simp [h0, h1]

/-- **Transitivity of the isometries of the hyperbolic plane on a level set.** Two nonzero
vectors of `⟨e₂, e₃⟩` with the same value are related by an isometry and a nonzero scalar — this is
where the rank enters: a vector of a hyperbolic *plane* is determined up to isometry by its
value. -/
theorem hp_exists_isometry (u u₀ : Fin 2 → ℚ) (hu₀ : u₀ ≠ 0) (hu : u ≠ 0)
    (hval : hpForm u u = hpForm u₀ u₀) :
    ∃ e : (Fin 2 → ℚ) ≃ₗ[ℚ] (Fin 2 → ℚ),
      (∀ x y, hpForm (e x) (e y) = hpForm x y) ∧ ∃ c : ℚ, c ≠ 0 ∧ u = c • e u₀ := by
  have h2 : u₀ 0 * u₀ 1 = u 0 * u 1 := by
    have h := hval
    simp only [hpForm] at h
    linarith
  have hzu : u 0 * u 1 = 0 ∨ u 0 * u 1 ≠ 0 := em _
  by_cases ha : u₀ 0 = 0
  · have hb : u₀ 1 ≠ 0 := fun hb0 => hu₀ ((hp_eq_zero_iff u₀).2 ⟨ha, hb0⟩)
    have hz : u 0 * u 1 = 0 := by rw [← h2, ha, zero_mul]
    rcases mul_eq_zero.mp hz with hA | hB
    · have hu1 : u 1 ≠ 0 := fun h1 => hu ((hp_eq_zero_iff u).2 ⟨hA, h1⟩)
      refine ⟨LinearEquiv.refl ℚ (Fin 2 → ℚ), fun _ _ => rfl, u 1 / u₀ 1,
        div_ne_zero hu1 hb, ?_⟩
      funext i
      fin_cases i
      · change u 0 = (u 1 / u₀ 1) * u₀ 0
        rw [hA, ha, mul_zero]
      · change u 1 = (u 1 / u₀ 1) * u₀ 1
        rw [div_mul_cancel₀ _ hb]
    · have hu0 : u 0 ≠ 0 := fun h1 => hu ((hp_eq_zero_iff u).2 ⟨h1, hB⟩)
      refine ⟨hpSwap, hpForm_hpSwap, u 0 / u₀ 1, div_ne_zero hu0 hb, ?_⟩
      funext i
      fin_cases i
      · simp only [Pi.smul_apply, smul_eq_mul]
        change u 0 = u 0 / u₀ 1 * u₀ 1
        rw [div_mul_cancel₀ _ hb]
      · simp only [Pi.smul_apply, smul_eq_mul]
        change u 1 = u 0 / u₀ 1 * u₀ 0
        rw [ha, mul_zero, hB]
  · by_cases hb : u₀ 1 = 0
    · have hz : u 0 * u 1 = 0 := by rw [← h2, hb, mul_zero]
      rcases mul_eq_zero.mp hz with hA | hB
      · have hu1 : u 1 ≠ 0 := fun h1 => hu ((hp_eq_zero_iff u).2 ⟨hA, h1⟩)
        refine ⟨hpSwap, hpForm_hpSwap, u 1 / u₀ 0, div_ne_zero hu1 ha, ?_⟩
        funext i
        fin_cases i
        · simp only [Pi.smul_apply, smul_eq_mul]
          change u 0 = u 1 / u₀ 0 * u₀ 1
          rw [hb, mul_zero, hA]
        · simp only [Pi.smul_apply, smul_eq_mul]
          change u 1 = u 1 / u₀ 0 * u₀ 0
          rw [div_mul_cancel₀ _ ha]
      · have hu0 : u 0 ≠ 0 := fun h1 => hu ((hp_eq_zero_iff u).2 ⟨h1, hB⟩)
        refine ⟨LinearEquiv.refl ℚ (Fin 2 → ℚ), fun _ _ => rfl, u 0 / u₀ 0,
          div_ne_zero hu0 ha, ?_⟩
        funext i
        fin_cases i
        · change u 0 = (u 0 / u₀ 0) * u₀ 0
          rw [div_mul_cancel₀ _ ha]
        · change u 1 = (u 0 / u₀ 0) * u₀ 1
          rw [hb, mul_zero, hB]
    · have hA : u 0 ≠ 0 := by
        intro h1
        have h : u₀ 0 * u₀ 1 = 0 := by rw [h2, h1, zero_mul]
        rcases mul_eq_zero.mp h with h' | h'
        · exact ha h'
        · exact hb h'
      have key : u₀ 0 * u₀ 1 = u 1 * u 0 := by rw [h2, mul_comm]
      refine ⟨hpDiag (u 0 / u₀ 0) (div_ne_zero hA ha), hpForm_hpDiag _ _, 1, one_ne_zero, ?_⟩
      funext i
      fin_cases i
      · simp only [Pi.smul_apply, smul_eq_mul, one_mul]
        change u 0 = u 0 / u₀ 0 * u₀ 0
        rw [div_mul_cancel₀ _ ha]
      · simp only [Pi.smul_apply, smul_eq_mul, one_mul]
        change u 1 = (u 0 / u₀ 0)⁻¹ * u₀ 1
        field_simp
        linarith [key]

/-! ### The transfer at `U ⊕ U` -/

/-- The isometries of the fibre `I^⊥/I` of the worked instance. -/
noncomputable def uuFibreIsometries (F : ConicalLine uuForm Q) :
    Set (↥F.space ≃ₗ[ℚ] ↥F.space) :=
  {e | ∀ x y, restrictBilinForm uuForm F.space (e x) (e y) =
    restrictBilinForm uuForm F.space x y}

/-- **`hTrans` holds on `U ⊕ U` for every wall normal**: the isometries of the fibre
`I^⊥/I ≅ ⟨e₂, e₃⟩` are transitive on the fibre vectors of a fixed value, by
`hp_exists_isometry`. Nothing about `Γ`, arithmeticity or `exists_isometry_apply_eq` is used. -/
theorem twoHyperbolicPlanes_hTrans
    (hBQ : ∀ u w : Fin 4 → ℚ,
      (associated Q) (rationalPoint u) (rationalPoint w) = (uuForm u w : ℝ))
    (F : ConicalLine uuForm Q) (hgen : F.gen = uue0) (hpartner : F.partner = uue1)
    {v₀ : Fin 4 → ℚ} (hπ₀ : fibreCarrierProj uuForm_isSymm F v₀ ≠ 0) :
    ∀ h : ↥F.space, h ≠ 0 →
      fibreForm Q F.space (rationalPoint h) =
        fibreForm Q F.space (rationalPoint (fibreCarrierProj uuForm_isSymm F v₀)) →
      ∃ e ∈ uuFibreIsometries F, ∃ c : ℚ, c ≠ 0 ∧
        h = c • e (fibreCarrierProj uuForm_isSymm F v₀) := by
  intro h hh hval
  set φ := uuFibreEquiv hgen hpartner with hφdef
  have hval' : restrictBilinForm uuForm F.space h h =
      restrictBilinForm uuForm F.space (fibreCarrierProj uuForm_isSymm F v₀)
        (fibreCarrierProj uuForm_isSymm F v₀) := by
    have h1 := fibreForm_rationalPoint_eq_restrict (BQ := uuForm) hBQ h
    have h2 := fibreForm_rationalPoint_eq_restrict (BQ := uuForm) hBQ
      (fibreCarrierProj uuForm_isSymm F v₀)
    rw [h1, h2] at hval
    exact_mod_cast hval
  have hval₂ : hpForm (φ h) (φ h) =
      hpForm (φ (fibreCarrierProj uuForm_isSymm F v₀))
        (φ (fibreCarrierProj uuForm_isSymm F v₀)) := by
    rw [← restrictBilinForm_uuFibreEquiv hgen hpartner h h,
      ← restrictBilinForm_uuFibreEquiv hgen hpartner
        (fibreCarrierProj uuForm_isSymm F v₀) (fibreCarrierProj uuForm_isSymm F v₀)]
    exact hval'
  have hφ₀ : φ (fibreCarrierProj uuForm_isSymm F v₀) ≠ 0 := by
    intro h0
    exact hπ₀ (φ.injective (by simpa using h0))
  have hφ : φ h ≠ 0 := by
    intro h0
    exact hh (φ.injective (by simpa using h0))
  obtain ⟨e₂, he₂, c, hc, hce⟩ :=
    hp_exists_isometry (φ h) (φ (fibreCarrierProj uuForm_isSymm F v₀)) hφ₀ hφ hval₂
  refine ⟨(φ.trans e₂).trans φ.symm, ?_, c, hc, ?_⟩
  · intro x y
    rw [restrictBilinForm_uuFibreEquiv hgen hpartner ((φ.trans e₂).trans φ.symm x)
        ((φ.trans e₂).trans φ.symm y),
      restrictBilinForm_uuFibreEquiv hgen hpartner x y]
    have h1 : ∀ z, φ ((φ.trans e₂).trans φ.symm z) = e₂ (φ z) := fun z => by
      simp only [LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
    rw [h1, h1, he₂]
  · refine φ.injective ?_
    have h1 : φ (c • ((φ.trans e₂).trans φ.symm (fibreCarrierProj uuForm_isSymm F v₀)))
        = c • e₂ (φ (fibreCarrierProj uuForm_isSymm F v₀)) := by
      rw [map_smul]
      congr 1
      simp only [LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
    rw [h1]
    exact hce

/-- **The verdict on `U ⊕ U`** (#172): for the worked instance of `CuspWorkedInstance.lean`, the
traces at a rational isotropic line `I` of the walls of **any** `Γ`-orbit of walls through `I` lie
in a single orbit of the isometries of the fibre `I^⊥/I`. This is
`ambientWallTrace_mem_orbitFamily` with `hTrans` discharged unconditionally by
`twoHyperbolicPlanes_hTrans`, and with no hypothesis on the walls through `I` inside the orbit: the
candidate hypothesis of #172 (transitivity of `Γ_I` on the walls through `I`) is not used. -/
theorem twoHyperbolicPlanes_ambientWallTrace_mem_orbitFamily
    (hBQ : ∀ u w : Fin 4 → ℚ,
      (associated Q) (rationalPoint u) (rationalPoint w) = (uuForm u w : ℝ))
    (F : ConicalLine uuForm Q) (hgen : F.gen = uue0) (hpartner : F.partner = uue1)
    (Γ : Set ((Fin 4 → ℚ) ≃ₗ[ℚ] (Fin 4 → ℚ)))
    (hΓiso : ∀ g ∈ Γ, ∀ x y : Fin 4 → ℚ, uuForm (g x) (g y) = uuForm x y)
    {v₀ : Fin 4 → ℚ} (hwall₀ : uuForm v₀ F.gen = 0)
    (hπ₀ : fibreCarrierProj uuForm_isSymm F v₀ ≠ 0)
    {g : (Fin 4 → ℚ) ≃ₗ[ℚ] (Fin 4 → ℚ)} (hg : g ∈ Γ) (hwall : uuForm (g v₀) F.gen = 0)
    (hπg : fibreCarrierProj uuForm_isSymm F (g v₀) ≠ 0) :
    LinearMap.ker (restrictBilinForm uuForm F.space (fibreCarrierProj uuForm_isSymm F (g v₀))) ∈
      orbitFamily ({LinearMap.ker (restrictBilinForm uuForm F.space
        (fibreCarrierProj uuForm_isSymm F v₀))} : Finset (Submodule ℚ ↥F.space))
        (uuFibreIsometries F) :=
  ambientWallTrace_mem_orbitFamily hBQ uuForm_isSymm F Γ (uuFibreIsometries F) hΓiso
    (fun _ he => he) hwall₀ hπ₀
    (twoHyperbolicPlanes_hTrans hBQ F hgen hpartner hπ₀) hg hwall hπg

end TwoHyperbolicPlanes

end LeanCategories.Lattices.Valued
