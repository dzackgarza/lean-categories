/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Lattices.Valued.CuspPlaneIncidence
public import Mathlib.RingTheory.PrincipalIdealDomain
public import Mathlib.Topology.Compactification.OnePoint.ProjectiveLine

/-! # The primitive lines of a plane and the `ℚ`-points of its dual

For a primitive isotropic plane `P` of an integral lattice, this module supplies step (c) of the
per-plane line count of `sec-descent-flags`: the primitive `ℤ`-lines of `P` are the `ℚ`-points of
the dual plane, and the action of the plane stabilizer's image `planeStabilizerImage P` on those
lines is the Möbius action of its matrix in a chosen basis. Step (d), the count itself, is not here;
the last section says exactly which hypothesis is missing and from which lemma.

## The coordinate model

`CoordLines` is the type of primitive rank-one submodules of `ℤ²`, and `CoordLines.equivPoint` is
the correspondence with `ℙ¹(ℚ)` (`OnePoint ℚ`):

* `exists_span_singleton_of_finrank_eq_one` — a rank-one submodule of `ℤ²` is spanned by one vector
  (`Submodule.basisOfPid`, over the principal ideal domain `ℤ`);
* `isPrimitiveSubmodule_span_iff_coprime` — that line is primitive exactly when the two coordinates
  are coprime. Forward: a common divisor `d` puts `v/d` in the saturation and out of the line.
  Backward: Bézout gives the functional `ψ` with `ψ v = 1`, and `x - ψ x • v` is killed by any `c`
  that carries `x` into the line, so it vanishes;
* `vecSlope_inj` — two primitive vectors of the same slope are equal up to sign, so the slope
  descends to `CoordLines` (`CoordLines.slope`) and is injective;
* `onePointVec` / `vecSlope_onePointVec` — the canonical primitive vector `(num, den)` of a rational
  point (`(1, 0)` at infinity) realizes every point, so the slope is also surjective
  (`CoordLines.ofPoint`). The inverse needs no uniqueness of a reduced fraction: the round trip is
  `vecSlope_inj` applied to the canonical vector of the slope.

The "adapted basis" of the source has no content here: the form restricted to an isotropic plane
vanishes identically, so every `ℤ`-basis of `P` is adapted. But a basis at all is extra data, and
`PrimitiveIsotropic` does not carry one: `L` is only projective, not assumed finite free, so a
rank-two submodule need not be finitely generated. The basis is therefore an explicit argument
`b : Basis (Fin 2) ℤ ↥P.toSubmodule` throughout.

## Step (c): the correspondence and its compatibility

* `planeInnerLine` — the rank-one submodule of `↥P` that an incident line cuts out, with
  `planeInnerLine_map` recovering the line and `planeInnerLine_primitive` transporting primitivity
  across `isPrimitiveSubmodule_comap_subtype_iff`. This is the existing primitivity transport of
  `CuspPlaneIncidence`, read in `P` rather than in `L`; no second notion of primitivity appears.
* `planeLineEquivCoord` — read an incident line through the basis: a bijection between
  `PlaneLines L P` and `CoordLines`, with both round trips (`planeLineCoord_ofCoord`,
  `planeLine_ofCoordCoord`).
* `planeLineEquivPoint` — **the correspondence**: `PlaneLines L P ≃ OnePoint ℚ`, the composite of
the two, i.e. the primitive `ℤ`-lines of `P` are the `ℚ`-points of the dual plane in the dual
basis.
* `planeLineEquivPoint_smul` — **the compatibility**: for `δ` in the image of the plane stabilizer,
  the correspondence carries the transport `δ • q` to the Möbius action of `δ`'s matrix in the basis
  on the corresponding point. The route is `planeInnerLine_smul` (the action on the cut-out lines is
  `Submodule.map` along `δ`, from `comap_planeSubmoduleTransport`), `planeCoord_apply`
  (`b.equivFun (δ x) = matrix δ *ᵥ b.equivFun x`, from `LinearMap.toMatrix_mulVec_repr`), and
  `vecSlope_matrixLinearEquiv`, which computes the Möbius action through
  `OnePoint.equivProjectivization` and `Projectivization.smul_mk`.

## Step (d): the count is open

`planeMatrixImage b` is the image of the plane stabilizer in `GL(2, ℤ)` in the basis `b`; by
`planeLineEquivPoint_smul` its orbits on the `ℚ`-points are the `planeStabilizerImage`-orbits on the
primitive lines of `P`, which is the object `sec-descent-flags` counts. **No count is stated here,
because the hypothesis the corpus lemma needs is not available.** The lemma is
`LeanCategories.ForMathlib.natCard_cuspOrbits_le_index_GL2`, of the form
`Nat.card (CuspOrbits (gl2Image Γ)) ≤ Γ.index` under `[Γ.FiniteIndex]`; it does not ask for a
congruence subgroup, so that is not the obstruction. The obstruction is the finite-index hypothesis
itself. Nothing in `PrimitiveIsotropic L 2` or in `planeStabilizerImage P` bounds the index of the
restriction `Stab_{O(L)}(P) → Aut(P) ≃ GL(2, ℤ)`: its kernel is the unipotent radical, which is not
of finite index in the stabilizer, and the image can be thin — already finite for a plane spanned by
a unimodular summand, where the restriction of the stabilizer to the plane is finite. Without finite
index the orbit set on `ℙ¹(ℚ)` is infinite, and Mathlib's `CuspOrbits` also stops being a set of
`ℙ¹(ℚ)`-orbits, because `IsCusp` is defined by parabolic elements and a thin group has none. The
count for `T_Co` is therefore open: it needs a proof of finite index for `planeMatrixImage b`, or
the discriminant-refined finite statement of the source (transitivity of the integral plane
stabilizer on the primitive lines in a fixed discriminant subgroup, whose finite datum is
`F_{J,C}`), which is not in this file.

## What this module does not do

It does not touch the flanker `Γ \ O(L) / (Stab P ⊓ Stab V)`, the loop identity, or
`FibreArithmetic`; and it states no orbit count, index or finiteness claim, for the reason above.

## Search record (LC-09)

`scripts/formalization_corpus.py search` at the manifest head of this worktree under
`primitive lines plane dual rational points correspondence`, `primitive vector coprime coordinates
primitive submodule span`, `OnePoint projectivization GL action slope` and `cusps rational points
projective line subgroup orbits`. No source has the correspondence: the hits are navigation-only
import files of `LeanBridge` and `OddOrder`, with no declaration. The owners used are Mathlib's
`Submodule.basisOfPid`, `Rat.isCoprime_num_den`, `Int.gcd_eq_zero_iff` and
`OnePoint.equivProjectivization`/`equivProjectivization_smul`/`Projectivization.smul_mk`, and the
repository's `isPrimitiveSubmodule_comap_subtype_iff`, `comap_planeSubmoduleTransport`,
`planeStabilizerImage.coe_smul` and `planeLineTransport_restrict_coe`. Everything else is glue.
-/

@[expose] public section

open LeanCategories.Lattices.Valued Module

namespace LeanCategories.Lattices.Valued

universe u


/-! ## The coordinate model: primitive rank-one submodules of `ℤ²` -/

/-- The slope of an integer vector of length two, read as a point of `ℙ¹(ℚ)`: the point at infinity
when the second coordinate vanishes, the ratio `v 0 / v 1` otherwise. -/
noncomputable def vecSlope (v : Fin 2 → ℤ) : OnePoint ℚ :=
  if v 1 = 0 then OnePoint.infty else ((v 1 : ℚ))⁻¹ * (v 0 : ℚ)

theorem vecSlope_smul (k : ℤ) (hk : k ≠ 0) (v : Fin 2 → ℤ) :
    vecSlope (k • v) = vecSlope v := by
  by_cases h : v 1 = 0
  · have h' : (k • v) 1 = 0 := by rw [Pi.smul_apply, h, smul_eq_mul, mul_zero]
    simp only [vecSlope, h, h', ite_true]
  · have h' : k * v 1 ≠ 0 := mul_ne_zero hk h
    have hcast : ((↑(k * v 1) : ℚ))⁻¹ * ((↑(k * v 0) : ℚ)) =
        ((↑(v 1) : ℚ))⁻¹ * ((↑(v 0) : ℚ)) := by
      have hkq : (k : ℚ) ≠ 0 := by exact_mod_cast hk
      have hvq : ((v 1 : ℤ) : ℚ) ≠ 0 := by exact_mod_cast h
      rw [Int.cast_mul, Int.cast_mul]
      field_simp
    simp only [vecSlope, h, h', Pi.smul_apply, smul_eq_mul]
    rw [hcast]

/-- A primitive vector of `ℤ²`: nonzero, with coprime coordinates. -/
def IsPrimitiveVec (v : Fin 2 → ℤ) : Prop :=
  v ≠ 0 ∧ IsCoprime (v 0) (v 1)

theorem IsPrimitiveVec.ne_zero {v : Fin 2 → ℤ} (h : IsPrimitiveVec v) : v ≠ 0 := h.1

theorem IsPrimitiveVec.coprime {v : Fin 2 → ℤ} (h : IsPrimitiveVec v) :
    IsCoprime (v 0) (v 1) := h.2

/-! ### Primitivity of the line spanned by a vector, and coprimality

Over `ℤ` a nonzero vector spans a primitive submodule of `ℤ²` exactly when its two coordinates are
coprime: primitivity is the saturation condition `saturation (ℤ v) = ℤ v`, and a common divisor is
exactly a nonzero scalar that pulls a multiple of `v` out of the line. -/

theorem isPrimitiveSubmodule_span_iff_coprime {v : Fin 2 → ℤ} (hv : v ≠ 0) :
    IsPrimitiveSubmodule (Submodule.span ℤ {v}) ↔ IsCoprime (v 0) (v 1) := by
  constructor
  · intro hprim
    by_contra hnc
    -- a common divisor of the two coordinates that is not a unit gives a failing saturation
    set d : ℤ := (↑((v 0).gcd (v 1)) : ℤ) with hd
    have hdvd0 : d ∣ v 0 := Int.gcd_dvd_left _ _
    have hdvd1 : d ∣ v 1 := Int.gcd_dvd_right _ _
    have hd0 : d ≠ 0 := by
      intro h0
      have hc0 : ((v 0).gcd (v 1) : ℤ) = 0 := hd.symm.trans h0
      have h00 : (v 0).gcd (v 1) = 0 := by exact_mod_cast hc0
      rw [Int.gcd_eq_zero_iff] at h00
      exact hv (funext fun i => by fin_cases i <;> simp [h00.1, h00.2])
    have hd1 : d ≠ 1 := by
      intro h1
      have hc1 : ((v 0).gcd (v 1) : ℤ) = 1 := hd.symm.trans h1
      exact hnc (Int.isCoprime_iff_gcd_eq_one.mpr (by exact_mod_cast hc1))
    have hd2 : 2 ≤ d := by
      have hpos : 0 ≤ d := Int.natCast_nonneg _
      omega
    -- the vector divided by the common divisor lies in the saturation but not in the line
    set w : Fin 2 → ℤ := fun i => v i / d with hwdef
    have hdv : d • w = v := by
      funext i
      rw [Pi.smul_apply, smul_eq_mul, hwdef]
      exact Int.mul_ediv_cancel' (by fin_cases i <;> assumption)
    have hsat : w ∈ saturation (Submodule.span ℤ {v}) := by
      rw [mem_saturation_iff]
      refine ⟨d, hd0, ?_⟩
      rw [hdv]
      exact Submodule.subset_span (Set.mem_singleton v)
    rw [(isPrimitiveSubmodule_iff_saturation_eq (Submodule.span ℤ {v})).mp hprim] at hsat
    rw [Submodule.mem_span_singleton] at hsat
    obtain ⟨m, hm⟩ := hsat
    -- `m d = 1`, contradicting `2 ≤ d`
    have hstep : (d * m) • v = v := by
      rw [mul_smul, hm, hdv]
    have hzero : (d * m - 1) • v = 0 := by rw [sub_smul, hstep, one_smul, sub_self]
    rcases smul_eq_zero.mp hzero with h | h
    · have hmul : d * m = 1 := by omega
      have hunit : IsUnit d := isUnit_of_dvd_one ⟨m, hmul.symm⟩
      rw [Int.isUnit_iff] at hunit
      omega
    · exact hv h
  · intro hcop
    rw [isPrimitiveSubmodule_iff_saturation_eq]
    refine le_antisymm ?_ (le_saturation _)
    intro x hx
    obtain ⟨c, hc, hcx⟩ := mem_saturation_iff (Submodule.span ℤ {v}) x |>.mp hx
    rw [Submodule.mem_span_singleton] at hcx ⊢
    obtain ⟨k, hk⟩ := hcx
    obtain ⟨p, q, hpq⟩ := hcop
    have hk0 : k * v 0 = c * x 0 := by simpa [Pi.smul_apply, smul_eq_mul] using congrFun hk 0
    have hk1 : k * v 1 = c * x 1 := by simpa [Pi.smul_apply, smul_eq_mul] using congrFun hk 1
    refine ⟨p * x 0 + q * x 1, ?_⟩
    have hcd : c * (p * x 0 + q * x 1) = k := by
      calc c * (p * x 0 + q * x 1) = p * (c * x 0) + q * (c * x 1) := by ring
        _ = p * (k * v 0) + q * (k * v 1) := by rw [← hk0, ← hk1]
        _ = k * (p * v 0 + q * v 1) := by ring
        _ = k := by rw [hpq, mul_one]
    have hsub : c • (x - (p * x 0 + q * x 1) • v) = 0 := by
      rw [smul_sub, smul_smul, hcd, hk, sub_self]
    have hzero : x - (p * x 0 + q * x 1) • v = 0 := by
      rcases smul_eq_zero.mp hsub with h | h
      · exact absurd h hc
      · exact h
    exact (sub_eq_zero.mp hzero).symm


/-! ### A rank-one submodule of `ℤ²` is spanned by one vector -/

theorem exists_span_singleton_of_finrank_eq_one {w : Submodule ℤ (Fin 2 → ℤ)}
    (h : Module.finrank ℤ w = 1) :
    ∃ v : Fin 2 → ℤ, v ≠ 0 ∧ w = Submodule.span ℤ {v} := by
  obtain ⟨n, bn⟩ := Submodule.basisOfPid (Pi.basisFun ℤ (Fin 2)) w
  have hcard : Module.finrank ℤ ↥w = n := by
    rw [Module.finrank_eq_card_basis bn, Fintype.card_fin]
  have hn : n = 1 := by omega
  subst hn
  have hspan : w = Submodule.span ℤ {((bn 0 : ↥w) : Fin 2 → ℤ)} := by
    refine le_antisymm ?_ ?_
    · intro x hx
      rw [Submodule.mem_span_singleton]
      refine ⟨bn.repr (⟨x, hx⟩ : ↥w) 0, ?_⟩
      have hy := congrArg Subtype.val (Module.Basis.sum_repr bn (⟨x, hx⟩ : ↥w))
      rw [Fin.sum_univ_one] at hy
      simpa using hy
    · intro x hx
      rw [Submodule.mem_span_singleton] at hx
      obtain ⟨c, rfl⟩ := hx
      exact w.smul_mem c (bn 0).2
  refine ⟨((bn 0 : ↥w) : Fin 2 → ℤ), ?_, hspan⟩
  intro hv
  have hbot : w = ⊥ := by rw [hspan, hv]; simp
  have hbot0 : Module.finrank ℤ (⊥ : Submodule ℤ (Fin 2 → ℤ)) = 0 := by
    rw [Module.finrank_eq_card_basis
      (Module.Basis.empty (ι := Fin 0) (M := ↥(⊥ : Submodule ℤ (Fin 2 → ℤ))))]
    simp
  rw [hbot, hbot0] at h
  exact absurd h (by norm_num)

/-- Two vectors spanning the same line have the same slope. -/
theorem vecSlope_eq_of_span_eq {u v : Fin 2 → ℤ} (hu : u ≠ 0)
    (h : Submodule.span ℤ {u} = Submodule.span ℤ {v}) : vecSlope u = vecSlope v := by
  have hu_mem : u ∈ Submodule.span ℤ {v} := by
    rw [← h]; exact Submodule.subset_span (Set.mem_singleton u)
  have hv_mem : v ∈ Submodule.span ℤ {u} := by
    rw [h]; exact Submodule.subset_span (Set.mem_singleton v)
  rw [Submodule.mem_span_singleton] at hu_mem hv_mem
  obtain ⟨k, hk⟩ := hu_mem
  obtain ⟨m, hm⟩ := hv_mem
  have hstep : (k * m) • u = u := by
    rw [mul_smul, hm, hk]
  have hzero : (k * m - 1) • u = 0 := by rw [sub_smul, hstep, one_smul, sub_self]
  have hkm : k * m = 1 := by
    rcases smul_eq_zero.mp hzero with hz | hz
    · exact sub_eq_zero.mp hz
    · exact absurd hz hu
  have hk0 : k ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hkm
    exact absurd hkm (by norm_num)
  rw [← hk, vecSlope_smul k hk0]

/-! ### The primitive vector attached to a `ℚ`-point, and the two round trips -/

/-- The canonical primitive integer vector of a point of `ℙ¹(ℚ)`: `(num, den)` at a finite point,
`(1, 0)` at infinity. -/
noncomputable def onePointVec (x : OnePoint ℚ) : Fin 2 → ℤ :=
  x.elim ![1, 0] fun q => ![q.num, (q.den : ℤ)]

@[simp]
theorem onePointVec_infty : onePointVec OnePoint.infty = ![1, 0] := rfl

@[simp]
theorem onePointVec_coe (q : ℚ) : onePointVec (q : OnePoint ℚ) = ![q.num, (q.den : ℤ)] := rfl

theorem onePointVec_ne_zero (x : OnePoint ℚ) : onePointVec x ≠ 0 := by
  cases x with
  | infty => simp [onePointVec]
  | coe q => simp [onePointVec]

theorem onePointVec_coprime (x : OnePoint ℚ) :
    IsCoprime (onePointVec x 0) (onePointVec x 1) := by
  cases x with
  | infty => simpa [onePointVec] using isCoprime_one_left (R := ℤ) (x := 0)
  | coe q => simpa [onePointVec] using Rat.isCoprime_num_den q

theorem isPrimitiveVec_onePointVec (x : OnePoint ℚ) : IsPrimitiveVec (onePointVec x) :=
  ⟨onePointVec_ne_zero x, onePointVec_coprime x⟩

theorem vecSlope_onePointVec (x : OnePoint ℚ) : vecSlope (onePointVec x) = x := by
  cases x with
  | infty => simp [vecSlope]
  | coe q =>
    have hden : (0 : ℚ) < (q.den : ℚ) := by exact_mod_cast q.den_pos
    have hne : (q.den : ℤ) ≠ 0 := by
      have : (q.den : ℚ) ≠ 0 := ne_of_gt hden
      exact_mod_cast this
    have hval : ((q.den : ℤ) : ℚ)⁻¹ * (q.num : ℚ) = q := by
      have h := Rat.num_div_den q
      rw [div_eq_inv_mul] at h
      simpa using h
    have h1 : (![q.num, (q.den : ℤ)] : Fin 2 → ℤ) 1 = (q.den : ℤ) := by simp
    have h0 : (![q.num, (q.den : ℤ)] : Fin 2 → ℤ) 0 = q.num := by simp
    simp only [onePointVec_coe, vecSlope, h1, h0, hne, ite_false]
    exact congrArg OnePoint.some hval

/-! ### Two primitive vectors of the same slope are equal up to sign -/

theorem vecSlope_inj {u v : Fin 2 → ℤ} (hu : IsPrimitiveVec u) (hv : IsPrimitiveVec v)
    (h : vecSlope u = vecSlope v) : u = v ∨ u = -v := by
  have unit_of_coprime_zero : ∀ z : Fin 2 → ℤ, IsPrimitiveVec z → z 1 = 0 → IsUnit (z 0) := by
    intro z hz hz1
    obtain ⟨a', b', h'⟩ := hz.2
    refine isUnit_iff_exists_inv.mpr ⟨a', ?_⟩
    rw [mul_comm]
    simpa [hz1] using h'
  by_cases hu1 : u 1 = 0
  · have hinf : vecSlope u = OnePoint.infty := by simp [vecSlope, hu1]
    have hv1 : v 1 = 0 := by
      by_contra hne
      have hfin : vecSlope v = OnePoint.some (((v 1 : ℚ))⁻¹ * (v 0 : ℚ)) := by
        simp only [vecSlope, hne, ite_false]
      rw [hinf, hfin] at h
      exact absurd h (by simp)
    have hu_unit := unit_of_coprime_zero u hu hu1
    have hv_unit := unit_of_coprime_zero v hv hv1
    rw [Int.isUnit_iff] at hu_unit hv_unit
    rcases hu_unit with h1 | h1 <;> rcases hv_unit with h2 | h2
    · left; funext i; fin_cases i <;> simp [hu1, hv1, h1, h2]
    · right; funext i; fin_cases i <;> simp [hu1, hv1, h1, h2]
    · right; funext i; fin_cases i <;> simp [hu1, hv1, h1, h2]
    · left; funext i; fin_cases i <;> simp [hu1, hv1, h1, h2]
  · have hu1q : ((u 1 : ℤ) : ℚ) ≠ 0 := by exact_mod_cast hu1
    have hv1 : v 1 ≠ 0 := by
      intro h0
      have hfin : vecSlope u = OnePoint.some (((u 1 : ℚ))⁻¹ * (u 0 : ℚ)) := by
        simp only [vecSlope, hu1, ite_false]
      have hinf : vecSlope v = OnePoint.infty := by simp [vecSlope, h0]
      rw [hfin, hinf] at h
      exact absurd h (by simp)
    have hv1q : ((v 1 : ℤ) : ℚ) ≠ 0 := by exact_mod_cast hv1
    have hq : ((u 1 : ℚ))⁻¹ * (u 0 : ℚ) = ((v 1 : ℚ))⁻¹ * (v 0 : ℚ) := by
      have h' := h
      simp only [vecSlope, hu1, hv1, ite_false] at h'
      exact OnePoint.coe_injective h'
    have hdiv : (u 0 : ℚ) / (u 1 : ℚ) = (v 0 : ℚ) / (v 1 : ℚ) := by
      rw [div_eq_inv_mul, div_eq_inv_mul]; exact hq
    have hcross_q : (u 0 : ℚ) * (v 1 : ℚ) = (v 0 : ℚ) * (u 1 : ℚ) :=
      (div_eq_div_iff hu1q hv1q).mp hdiv
    have hcross : u 0 * v 1 = v 0 * u 1 := by
      have h' : ((u 0 * v 1 : ℤ) : ℚ) = ((v 0 * u 1 : ℤ) : ℚ) := by
        push_cast
        exact hcross_q
      exact Int.cast_injective h'
    have hdvd : u 1 ∣ v 1 :=
      hu.2.symm.dvd_of_dvd_mul_left ⟨v 0, by rw [hcross, mul_comm]⟩
    have hdvd' : v 1 ∣ u 1 :=
      hv.2.symm.dvd_of_dvd_mul_left ⟨u 0, by rw [← hcross, mul_comm]⟩
    obtain ⟨c, hc⟩ := hdvd
    obtain ⟨e, he⟩ := hdvd'
    have h1 : u 1 = u 1 * (c * e) := by
      calc u 1 = v 1 * e := he
        _ = (u 1 * c) * e := by rw [hc]
        _ = u 1 * (c * e) := by ring
    have hce : c * e = 1 := by
      have h2 : u 1 * (c * e) = u 1 * 1 := by rw [← h1, mul_one]
      exact mul_left_cancel₀ hu1 h2
    have hc_unit : c = 1 ∨ c = -1 := by
      have hunit : IsUnit c := isUnit_of_dvd_one ⟨e, hce.symm⟩
      rwa [Int.isUnit_iff] at hunit
    rcases hc_unit with rfl | rfl
    · left
      have hv1' : v 1 = u 1 := by rw [hc, mul_one]
      have hv0' : v 0 = u 0 := by
        have hh := hcross
        rw [hv1'] at hh
        exact (mul_right_cancel₀ hu1 hh).symm
      funext i; fin_cases i <;> simp [hv0', hv1']
    · right
      have hv1' : v 1 = -u 1 := by rw [hc, mul_neg, mul_one]
      have hv0' : v 0 = -u 0 := by
        have hh := hcross
        rw [hv1'] at hh
        have h2 : u 0 * u 1 = (-v 0) * u 1 := by
          rw [neg_mul]
          have hstep := hh
          rw [mul_neg] at hstep
          linarith
        have h3 := mul_right_cancel₀ hu1 h2
        rw [h3]; ring
      funext i; fin_cases i <;> simp [hv0', hv1']

/-! ### The coordinate model of the primitive lines of the plane -/

/-- A primitive rank-one submodule of `ℤ²`: the coordinate model of a primitive line of a plane
equipped with a `ℤ`-basis. -/
def CoordLines : Type :=
  {w : Submodule ℤ (Fin 2 → ℤ) // Module.finrank ℤ w = 1 ∧ IsPrimitiveSubmodule w}

namespace CoordLines

/-- A generator of the coordinate line, from the basis of a rank-one submodule over `ℤ`. -/
noncomputable def gen (w : CoordLines) : Fin 2 → ℤ :=
  Classical.choose (exists_span_singleton_of_finrank_eq_one w.2.1)

theorem gen_ne_zero (w : CoordLines) : w.gen ≠ 0 :=
  (Classical.choose_spec (exists_span_singleton_of_finrank_eq_one w.2.1)).1

theorem coe_eq_span_gen (w : CoordLines) :
    w.1 = Submodule.span ℤ {w.gen} :=
  (Classical.choose_spec (exists_span_singleton_of_finrank_eq_one w.2.1)).2

theorem isPrimitiveVec_gen (w : CoordLines) : IsPrimitiveVec w.gen :=
  ⟨w.gen_ne_zero,
    (isPrimitiveSubmodule_span_iff_coprime w.gen_ne_zero).mp (by
      rw [← w.coe_eq_span_gen]; exact w.2.2)⟩

/-- **The slope of a primitive line of `ℤ²`**, read in the coordinate basis. -/
noncomputable def slope (w : CoordLines) : OnePoint ℚ := vecSlope w.gen

/-- The slope depends only on the underlying line, and not on the chosen generator. -/
theorem slope_eq_vecSlope {w : CoordLines} {u : Fin 2 → ℤ}
    (h : w.1 = Submodule.span ℤ {u}) : w.slope = vecSlope u :=
  vecSlope_eq_of_span_eq w.gen_ne_zero (w.coe_eq_span_gen.symm.trans h)

/-- The primitive coordinate line spanned by one vector. -/
noncomputable def ofVec (v : Fin 2 → ℤ) (hv : IsPrimitiveVec v) : CoordLines where
  val := Submodule.span ℤ {v}
  property := ⟨finrank_span_singleton_eq_one (R := ℤ) (M := Fin 2 → ℤ) hv.1,
    (isPrimitiveSubmodule_span_iff_coprime hv.1).mpr hv.2⟩

/-- The coordinate line of a `ℚ`-point: the line spanned by its canonical primitive vector. -/
noncomputable def ofPoint (x : OnePoint ℚ) : CoordLines :=
  ofVec (onePointVec x) (isPrimitiveVec_onePointVec x)

theorem ofPoint_coe (x : OnePoint ℚ) :
    (ofPoint x).1 = Submodule.span ℤ {onePointVec x} := rfl

theorem slope_ofPoint (x : OnePoint ℚ) : (ofPoint x).slope = x :=
  (slope_eq_vecSlope (w := ofPoint x) (u := onePointVec x)
    (ofPoint_coe x)).trans (vecSlope_onePointVec x)

theorem span_neg (v : Fin 2 → ℤ) :
    Submodule.span ℤ {-v} = Submodule.span ℤ {v} := by
  ext x
  rw [Submodule.mem_span_singleton, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨-a, by rw [neg_smul, ← smul_neg, ← ha]⟩
  · rintro ⟨a, ha⟩
    exact ⟨-a, by rw [neg_smul, smul_neg, ha, neg_neg]⟩

theorem ofPoint_slope (w : CoordLines) : ofPoint w.slope = w := by
  have hu : IsPrimitiveVec (onePointVec (vecSlope w.gen)) := isPrimitiveVec_onePointVec _
  have hsl : vecSlope (onePointVec (vecSlope w.gen)) = vecSlope w.gen := vecSlope_onePointVec _
  have hcases := vecSlope_inj hu w.isPrimitiveVec_gen hsl
  have hcoe : (ofPoint w.slope).1 = Submodule.span ℤ {onePointVec (vecSlope w.gen)} := rfl
  refine Subtype.ext ?_
  rw [hcoe, w.coe_eq_span_gen]
  rcases hcases with h | h
  · rw [h]
  · rw [h, span_neg]

/-- **The correspondence between the primitive lines of `ℤ²` and the `ℚ`-points of the dual.** -/
noncomputable def equivPoint : CoordLines ≃ OnePoint ℚ where
  toFun := slope
  invFun := ofPoint
  left_inv := ofPoint_slope
  right_inv := slope_ofPoint

end CoordLines


/-! ## The plane: primitive lines of `P` as the `ℚ`-points of the dual in a chosen basis -/

/-- The rank of a submodule is unchanged by an injective linear map. -/
theorem finrank_map_of_injective {R : Type*} [CommRing R] {M N : Type*} [AddCommGroup M]
    [Module R M] [AddCommGroup N] [Module R N] (f : M →ₗ[R] N) (hf : Function.Injective f)
    (p : Submodule R M) : Module.finrank R ↥(p.map f) = Module.finrank R ↥p := by
  exact (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective f hf p)).symm

section Plane

variable {R : Type u} [CommRing R] {L : IntegralLatticeCat R} {P : PrimitiveIsotropic L 2}

/-- The rank-one submodule of `↥P` cut out by an incident primitive line `q` of the plane. -/
def planeInnerLine (q : PlaneLines L P) : Submodule R ↥P.toSubmodule :=
  q.1.toSubmodule.comap P.toSubmodule.subtype

theorem planeInnerLine_map (q : PlaneLines L P) :
    (planeInnerLine q).map P.toSubmodule.subtype = q.1.toSubmodule := by
  ext x
  simp only [Submodule.mem_map, planeInnerLine, Submodule.mem_comap]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hy
  · intro hx
    exact ⟨⟨x, q.2 hx⟩, hx, rfl⟩

theorem planeInnerLine_finrank (q : PlaneLines L P) :
    Module.finrank R (planeInnerLine q) = 1 := by
  rw [← finrank_map_of_injective (p := planeInnerLine q) P.toSubmodule.subtype
    Subtype.val_injective, planeInnerLine_map q]
  exact q.1.finrank_eq

theorem planeInnerLine_primitive [IsDomain R] (q : PlaneLines L P) :
    IsPrimitiveSubmodule (planeInnerLine q) := by
  rw [planeInnerLine]
  exact (isPrimitiveSubmodule_comap_subtype_iff q.2 P.primitive).mpr q.1.primitive

theorem planeInnerLine_injective {q q' : PlaneLines L P}
    (h : planeInnerLine q = planeInnerLine q') : q.1.toSubmodule = q'.1.toSubmodule := by
  rw [← planeInnerLine_map q, ← planeInnerLine_map q', h]

end Plane

section PlaneCoord

attribute [local instance 10000] Submodule.module

variable {L : IntegralLatticeCat ℤ} {P : PrimitiveIsotropic L 2}

/-- The coordinate line of an incident line of the plane, in a chosen `ℤ`-basis of `P`. -/
noncomputable def planeLineCoord (b : Module.Basis (Fin 2) ℤ ↥P.toSubmodule)
    (q : PlaneLines L P) : CoordLines where
  val := (planeInnerLine q).map b.equivFun.toLinearMap
  property :=
    ⟨by rw [finrank_map_of_injective _ b.equivFun.injective, planeInnerLine_finrank q],
      (IsPrimitiveSubmodule.map_equiv_iff b.equivFun (planeInnerLine q)).mpr
        (planeInnerLine_primitive q)⟩

/-- The primitive isotropic line of `L` obtained from a primitive line of the coordinate plane:
read the line in `P` through the basis, then push it into `L`. -/
noncomputable def planeLineOfCoord (b : Module.Basis (Fin 2) ℤ ↥P.toSubmodule)
    (w : CoordLines) : PlaneLines L P :=
  let Wp : Submodule ℤ ↥P.toSubmodule := w.1.map (b.equivFun.symm).toLinearMap
  have hWp : Module.finrank ℤ Wp = 1 := by
    rw [finrank_map_of_injective _ (b.equivFun.symm).injective, w.2.1]
  have hWp_prim : IsPrimitiveSubmodule Wp :=
    (IsPrimitiveSubmodule.map_equiv_iff (b.equivFun.symm) w.1).mpr w.2.2
  let Wl : Submodule ℤ L.obj.carrier := Wp.map P.toSubmodule.subtype
  have hWl : Module.finrank ℤ Wl = 1 := by
    rw [finrank_map_of_injective _ Subtype.val_injective Wp]
    exact hWp
  have hWl_prim : IsPrimitiveSubmodule Wl := by
    have hcomap : Wl.comap P.toSubmodule.subtype = Wp := by
      rw [show Wl = Wp.map P.toSubmodule.subtype from rfl, Submodule.comap_map_eq_self]
      simp [Submodule.ker_subtype]
    refine (isPrimitiveSubmodule_comap_subtype_iff (Submodule.map_subtype_le P.toSubmodule Wp)
      P.primitive).mp ?_
    rw [hcomap]
    exact hWp_prim
  have hWl_iso : IsIsotropicSubmodule L Wl := by
    intro x hx y hy
    obtain ⟨a, ha, rfl⟩ := Submodule.mem_map.mp hx
    obtain ⟨b, hb, rfl⟩ := Submodule.mem_map.mp hy
    exact P.isotropic a a.2 b b.2
  ⟨⟨Wl, hWl_iso, hWl, hWl_prim⟩, Submodule.map_subtype_le P.toSubmodule Wp⟩

theorem planeLineCoord_ofCoord (b : Module.Basis (Fin 2) ℤ ↥P.toSubmodule)
    (w : CoordLines) : planeLineCoord b (planeLineOfCoord b w) = w := by
  refine Subtype.ext ?_
  change ((planeInnerLine (planeLineOfCoord b w)).map b.equivFun.toLinearMap) = w.1
  rw [planeInnerLine,
    show (planeLineOfCoord b w).1.toSubmodule =
      (w.1.map (b.equivFun.symm).toLinearMap).map P.toSubmodule.subtype from rfl,
    Submodule.comap_map_eq_self]
  · rw [← Submodule.map_comp]
    have hcomp : b.equivFun.toLinearMap.comp (b.equivFun.symm).toLinearMap = LinearMap.id := by
      ext x
      simp
    rw [hcomp, Submodule.map_id]
  · simp [Submodule.ker_subtype]

theorem planeLine_ofCoordCoord (b : Module.Basis (Fin 2) ℤ ↥P.toSubmodule)
    (q : PlaneLines L P) : planeLineOfCoord b (planeLineCoord b q) = q := by
  refine Subtype.ext (PrimitiveIsotropic.ext ?_)
  have h1 : ((planeInnerLine q).map b.equivFun.toLinearMap).map
      (b.equivFun.symm).toLinearMap = planeInnerLine q := by
    rw [← Submodule.map_comp]
    have hcomp : (b.equivFun.symm).toLinearMap.comp b.equivFun.toLinearMap = LinearMap.id := by
      ext x
      simp
    rw [hcomp, Submodule.map_id]
  change (((planeInnerLine q).map b.equivFun.toLinearMap).map
    (b.equivFun.symm).toLinearMap).map P.toSubmodule.subtype = q.1.toSubmodule
  rw [h1, planeInnerLine_map]

/-- **The correspondence between the primitive isotropic lines inside a plane and the primitive
lines of the coordinate plane**: read an incident line through the basis. -/
noncomputable def planeLineEquivCoord (b : Module.Basis (Fin 2) ℤ ↥P.toSubmodule) :
    PlaneLines L P ≃ CoordLines where
  toFun := planeLineCoord b
  invFun := planeLineOfCoord b
  left_inv := planeLine_ofCoordCoord b
  right_inv := planeLineCoord_ofCoord b

/-- **Step (c) of the plane count: the correspondence between the primitive isotropic lines inside
the plane `P` and the `ℚ`-points of the dual plane, in a chosen `ℤ`-basis of `P`.** -/
noncomputable def planeLineEquivPoint (b : Module.Basis (Fin 2) ℤ ↥P.toSubmodule) :
    PlaneLines L P ≃ OnePoint ℚ :=
  (planeLineEquivCoord b).trans CoordLines.equivPoint

/-- The forward map of `planeLineEquivPoint`, on an incident line. -/
theorem planeLineEquivPoint_apply (b : Module.Basis (Fin 2) ℤ ↥P.toSubmodule)
    (q : PlaneLines L P) : planeLineEquivPoint b q = (planeLineCoord b q).slope := rfl

/-- The inverse map of `planeLineEquivPoint`, on a `ℚ`-point. -/
theorem planeLineEquivPoint_symm_apply (b : Module.Basis (Fin 2) ℤ ↥P.toSubmodule)
    (x : OnePoint ℚ) :
    (planeLineEquivPoint b).symm x = planeLineOfCoord b (CoordLines.ofPoint x) := rfl

end PlaneCoord


/-! ## The action compatibility

The plane stabilizer acts on the incident lines through `planeStabilizerImage`; in a chosen basis
that image is a subgroup of `GL(2, ℤ)`, and the theorem below says that the correspondence of
`planeLineEquivPoint` carries the action of that image on the lines to the Möbius action of its
matrix on the `ℚ`-points. This is what turns the orbit count into a count of a subgroup of
`GL(2, ℤ)` on `ℙ¹(ℚ)`. -/

section Action

open scoped Matrix

attribute [local instance 10000] Submodule.module

variable {L : IntegralLatticeCat ℤ} {P : PrimitiveIsotropic L 2}

/-- The linear equivalence of `ℤ²` given by an invertible integer matrix. -/
noncomputable def matrixLinearEquiv (g : GL (Fin 2) ℤ) : (Fin 2 → ℤ) ≃ₗ[ℤ] (Fin 2 → ℤ) where
  toFun v := (g : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ v
  invFun v := ((g⁻¹ : GL (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ v
  left_inv v := by
    have hmul : ((g⁻¹ : GL (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) *
        (g : Matrix (Fin 2) (Fin 2) ℤ) = 1 := by
      have h : ((g⁻¹ * g : GL (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) = 1 := by
        rw [inv_mul_cancel, Units.val_one]
      exact h
    change ((g⁻¹ : GL (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ
      ((g : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ v) = v
    rw [Matrix.mulVec_mulVec, hmul, Matrix.one_mulVec]
  right_inv v := by
    have hmul : (g : Matrix (Fin 2) (Fin 2) ℤ) *
        ((g⁻¹ : GL (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) = 1 := by
      have h : ((g * g⁻¹ : GL (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) = 1 := by
        rw [mul_inv_cancel, Units.val_one]
      exact h
    change (g : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ
      (((g⁻¹ : GL (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ v) = v
    rw [Matrix.mulVec_mulVec, hmul, Matrix.one_mulVec]
  map_add' x y := Matrix.mulVec_add _ _ _
  map_smul' c x := Matrix.mulVec_smul _ _ _

theorem matrixLinearEquiv_apply (g : GL (Fin 2) ℤ) (v : Fin 2 → ℤ) :
    matrixLinearEquiv g v = (g : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ v := rfl

/-- The matrix action on `ℤ²`, read over `ℚ`. -/
theorem map_mulVec_cast (g : GL (Fin 2) ℤ) (v : Fin 2 → ℤ) :
    (fun i => ((matrixLinearEquiv g v) i : ℚ)) =
      ((Matrix.GeneralLinearGroup.map (algebraMap ℤ ℚ) g) : Matrix (Fin 2) (Fin 2) ℚ) *ᵥ
        (fun i => (v i : ℚ)) := by
  rw [matrixLinearEquiv_apply]
  ext i
  fin_cases i <;> simp [Matrix.mulVec_fin_two]

/-- The slope of a nonzero vector, as a point of the projectivization. -/
theorem vecSlope_eq_proj (v : Fin 2 → ℤ) (hv : v ≠ 0) :
    vecSlope v = (OnePoint.equivProjectivization ℚ).symm
      (Projectivization.mk ℚ (fun i => (v i : ℚ))
        (by rintro h; exact hv (funext fun i => by
          have := congrFun h i
          simpa using this))) := by
  rw [OnePoint.equivProjectivization_symm_apply_mk]
  by_cases h : v 1 = 0
  · simp [vecSlope, h]
  · have hq : ¬ ((v 1 : ℤ) : ℚ) = 0 := by exact_mod_cast h
    simp only [vecSlope, h, hq, ite_false]

/-- **The Möbius action of an invertible integer matrix on the slope of a vector.** -/
theorem vecSlope_matrixLinearEquiv (g : GL (Fin 2) ℤ) (v : Fin 2 → ℤ) (hv : v ≠ 0) :
    vecSlope (matrixLinearEquiv g v) =
      (Matrix.GeneralLinearGroup.map (algebraMap ℤ ℚ) g) • vecSlope v := by
  have hgv : matrixLinearEquiv g v ≠ 0 := fun h =>
    hv ((matrixLinearEquiv g).injective (by rw [h, map_zero]))
  have hvq : (fun i => (v i : ℚ)) ≠ 0 := by
    intro h
    exact hv (funext fun i => by
      have := congrFun h i
      simpa using this)
  set G : GL (Fin 2) ℚ := Matrix.GeneralLinearGroup.map (algebraMap ℤ ℚ) g with hG
  have hvq : (fun i => (v i : ℚ)) ≠ 0 := fun h => hv (funext fun i => by
    have := congrFun h i
    simpa using this)
  rw [vecSlope_eq_proj _ hgv, vecSlope_eq_proj v hv, hG]
  rw [Equiv.symm_apply_eq, OnePoint.equivProjectivization_smul, Equiv.apply_symm_apply]
  rw [Projectivization.smul_mk]
  congr 1
  exact map_mulVec_cast g v

/-- The matrix of a plane automorphism in the basis `b`. -/
noncomputable def planeMatrixEquiv (b : Module.Basis (Fin 2) ℤ ↥P.toSubmodule) :
    (↥P.toSubmodule ≃ₗ[ℤ] ↥P.toSubmodule) ≃* GL (Fin 2) ℤ :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv ℤ ↥P.toSubmodule).symm.trans
    (Units.mapEquiv (LinearMap.toMatrixAlgEquiv b).toMulEquiv)

theorem planeMatrixEquiv_apply_coe (b : Module.Basis (Fin 2) ℤ ↥P.toSubmodule)
    (δ : ↥P.toSubmodule ≃ₗ[ℤ] ↥P.toSubmodule) :
    ((planeMatrixEquiv b δ : GL (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) =
      LinearMap.toMatrix b b δ.toLinearMap := rfl

/-- The primitive coordinate line obtained by acting with an invertible integer matrix. -/
noncomputable def coordLineMap (w : CoordLines) (g : GL (Fin 2) ℤ) : CoordLines where
  val := w.1.map (matrixLinearEquiv g).toLinearMap
  property :=
    ⟨by rw [finrank_map_of_injective _ (matrixLinearEquiv g).injective, w.2.1],
      (IsPrimitiveSubmodule.map_equiv_iff (matrixLinearEquiv g) w.1).mpr w.2.2⟩

/-- **The slope of the image of a primitive coordinate line under an invertible integer matrix.** -/
theorem slope_coordLineMap (g : GL (Fin 2) ℤ) (w : CoordLines) :
    (coordLineMap w g).slope =
      (Matrix.GeneralLinearGroup.map (algebraMap ℤ ℚ) g) • w.slope := by
  have hmap : (coordLineMap w g).1 = Submodule.span ℤ {matrixLinearEquiv g w.gen} := by
    change w.1.map (matrixLinearEquiv g).toLinearMap = _
    rw [w.coe_eq_span_gen, Submodule.map_span]
    congr 1
    ext x
    simp
  rw [(coordLineMap w g).slope_eq_vecSlope (u := matrixLinearEquiv g w.gen) hmap,
    vecSlope_matrixLinearEquiv g w.gen w.gen_ne_zero, w.slope_eq_vecSlope w.coe_eq_span_gen]

/-- The coordinate vector of the image of `x` under an automorphism of the plane, in the basis. -/
theorem planeCoord_apply (b : Module.Basis (Fin 2) ℤ ↥P.toSubmodule)
    (δ : ↥P.toSubmodule ≃ₗ[ℤ] ↥P.toSubmodule) (x : ↥P.toSubmodule) :
    b.equivFun (δ x) = matrixLinearEquiv (planeMatrixEquiv b δ) (b.equivFun x) := by
  rw [matrixLinearEquiv_apply, planeMatrixEquiv_apply_coe, Module.Basis.equivFun_apply,
    Module.Basis.equivFun_apply, LinearMap.toMatrix_mulVec_repr]
  rfl

/-- **The plane stabilizer acts on the incident lines through the matrix action in the basis.** -/
theorem planeInnerLine_smul (δ : ↥(planeStabilizerImage P)) (q : PlaneLines L P) :
    planeInnerLine (δ • q) =
      (planeInnerLine q).map ((δ : ↥P.toSubmodule ≃ₗ[ℤ] ↥P.toSubmodule) :
        ↥P.toSubmodule →ₗ[ℤ] ↥P.toSubmodule) := by
  rw [planeInnerLine, planeStabilizerImage.coe_smul, comap_planeSubmoduleTransport]
  rfl

/-- The coordinate matrix action of an element of the plane stabilizer's image. -/
noncomputable def planeCoordMatrix (b : Module.Basis (Fin 2) ℤ ↥P.toSubmodule)
    (δ : ↥(planeStabilizerImage P)) : (Fin 2 → ℤ) ≃ₗ[ℤ] (Fin 2 → ℤ) :=
  matrixLinearEquiv (planeMatrixEquiv b (δ : ↥P.toSubmodule ≃ₗ[ℤ] ↥P.toSubmodule))

/-- The coordinate line of a translate of an incident line is the matrix image of the coordinate
line of the line. -/
theorem planeLineCoord_smul_val (b : Module.Basis (Fin 2) ℤ ↥P.toSubmodule)
    (δ : ↥(planeStabilizerImage P)) (q : PlaneLines L P) :
    (planeLineCoord b (δ • q)).1 =
      ((planeLineCoord b q).1).map (planeCoordMatrix b δ).toLinearMap := by
  change (planeInnerLine (δ • q)).map b.equivFun.toLinearMap
    = ((planeInnerLine q).map b.equivFun.toLinearMap).map (planeCoordMatrix b δ).toLinearMap
  have hcomp : b.equivFun.toLinearMap.comp ((δ : ↥P.toSubmodule ≃ₗ[ℤ] ↥P.toSubmodule) :
        ↥P.toSubmodule →ₗ[ℤ] ↥P.toSubmodule)
      = (planeCoordMatrix b δ).toLinearMap.comp b.equivFun.toLinearMap := by
    refine LinearMap.ext (fun x => ?_)
    exact planeCoord_apply b (δ : ↥P.toSubmodule ≃ₗ[ℤ] ↥P.toSubmodule) x
  rw [planeInnerLine_smul, ← Submodule.map_comp, ← Submodule.map_comp, hcomp]

/-- **The compatibility of the correspondence with the action of the image of the plane
stabilizer**: `planeLineEquivPoint` carries the action of `planeStabilizerImage P` on the incident
lines to the Möbius action of its matrix in the basis `b` on the `ℚ`-points of the dual plane. -/
theorem planeLineEquivPoint_smul (b : Module.Basis (Fin 2) ℤ ↥P.toSubmodule)
    (δ : ↥(planeStabilizerImage P)) (q : PlaneLines L P) :
    planeLineEquivPoint b (δ • q) =
      (Matrix.GeneralLinearGroup.map (algebraMap ℤ ℚ)
        (planeMatrixEquiv b (δ : ↥P.toSubmodule ≃ₗ[ℤ] ↥P.toSubmodule))) •
        planeLineEquivPoint b q := by
  have hcoord : planeLineCoord b (δ • q) =
      coordLineMap (planeLineCoord b q)
        (planeMatrixEquiv b (δ : ↥P.toSubmodule ≃ₗ[ℤ] ↥P.toSubmodule)) :=
    Subtype.ext (planeLineCoord_smul_val b δ q)
  rw [planeLineEquivPoint_apply, planeLineEquivPoint_apply, hcoord, slope_coordLineMap]

/-- **The image of the plane stabilizer in `GL(2, ℤ)` in the basis `b`**: the subgroup whose orbits
on `ℙ¹(ℚ)` are the orbits of `planeStabilizerImage P` on the primitive lines of `P`
(`planeLineEquivPoint_smul`). This is the object the per-plane count is an orbit count for; no
finiteness or index statement is made about it. -/
noncomputable def planeMatrixImage (b : Module.Basis (Fin 2) ℤ ↥P.toSubmodule) :
    Subgroup (GL (Fin 2) ℤ) :=
  (planeStabilizerImage P).map (planeMatrixEquiv b).toMonoidHom

theorem mem_planeMatrixImage {b : Module.Basis (Fin 2) ℤ ↥P.toSubmodule} {g : GL (Fin 2) ℤ} :
    g ∈ planeMatrixImage b ↔
      ∃ δ : ↥P.toSubmodule ≃ₗ[ℤ] ↥P.toSubmodule,
        δ ∈ planeStabilizerImage P ∧ planeMatrixEquiv b δ = g :=
  Iff.rfl

/-- **The matrix action of the plane stabilizer on `ℙ¹(ℚ)`**: the restriction, the matrix in the
basis, and the coefficient extension `ℤ → ℚ`. By `planeLineEquivPoint_smul` this is the action on
the `ℚ`-points to which `planeLineEquivPoint` transfers the line action. -/
noncomputable def planeMatrixAction (b : Module.Basis (Fin 2) ℤ ↥P.toSubmodule) :
    ↥(planeStabilizerImage P) →* GL (Fin 2) ℚ :=
  (Matrix.GeneralLinearGroup.map (algebraMap ℤ ℚ)).comp
    ((planeMatrixEquiv b).toMonoidHom.comp (Subgroup.subtype (planeStabilizerImage P)))

theorem planeMatrixAction_apply (b : Module.Basis (Fin 2) ℤ ↥P.toSubmodule)
    (δ : ↥(planeStabilizerImage P)) :
    planeMatrixAction b δ =
      Matrix.GeneralLinearGroup.map (algebraMap ℤ ℚ)
        (planeMatrixEquiv b (δ : ↥P.toSubmodule ≃ₗ[ℤ] ↥P.toSubmodule)) := rfl

end Action

end LeanCategories.Lattices.Valued
