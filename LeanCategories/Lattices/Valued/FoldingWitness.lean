/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Lattices.Valued.FoldingInvariantChamber
public import LeanCategories.Lattices.Valued.Standard

/-!
# A fully witnessed instance of the invariant-chamber theorem (`#116`)

`isChamberWithWalls_invariant_of_chamber` (`FoldingInvariantChamber.lean`) produces
`IsChamberWithWalls` for the invariant lattice from an ambient chamber, an involution, the
preservation of the chamber cone and two arithmetic inputs. This file discharges **every one of
those hypotheses on a concrete lattice**, so the theorem is not vacuous:

* the lattice is the integral hyperbolic plane `U = ⟨e, f⟩` with `e² = f² = 0`, `e · f = 1`
  (`Standard.hyperbolicPlaneFiniteLattice`), of signature `(1,1)`;
* the chamber is the one cut out by the single wall `e - f`, with interior point `e + 2f`
  (`hyperbolicPlane_isChamberWithWalls`): all three fields of `IsChamberWithWalls` are proved, the
  third from the classification of the negative reflective vectors of `U`, which are exactly
  `±(e - f)` (`u_reflective_neg_classification`);
* the involution is the identity (`uIdentity`), the only chamber-preserving involution of `U`: the
  reflection that swaps `e` and `f` carries the wall to its negative and exchanges the two sides of
  the chamber, so it does not preserve the cone.

Everything the joining theorem asks for is then a theorem of this file, not a hypothesis
(`u_witnessed`). A *non-trivial* involution instance needs a Lorentzian lattice with more than one
chamber wall; the repository has exactly one such chamber (`E₁₀(2)`,
`VinbergE10Chamber.e10_isChamberWithWalls`) and the diagram reversal `αᵢ ↦ α_{9-i}` as the
candidate, whose isometry and fixed-lattice root classification are a separate unit.

## LC-09 record

Searched the repository for a worked chamber of the hyperbolic plane and a classification of its
reflective vectors before writing any declaration: `rg "hyperbolicPlane"` gives
`Standard.hyperbolicPlane`/`hyperbolicPlaneFiniteLattice`/`hyperbolicPlane_pairing_single` and the
uses in `FoldingEnriques.lean`'s block matrices, with no chamber and no root classification;
`rg "IsChamberWithWalls"` gives the E₁₀ chamber (`VinbergE10Chamber.lean`) and the folding cone
lemmas only. Mathlib at the pinned head has no chamber of a hyperbolic lattice and no classification
of reflective vectors of `U` (`LinearAlgebra/RootSystem/*` is the finite-type root-system API). The
Formalization Corpus, on "hyperbolic plane lattice roots classification minus two vectors", returns
no files. Nothing to port; the classification below is a two-line `ℤ`-argument.

## References

* V. Alexeev, P. Engel, D. Z. Garza, L. Schaffler, arXiv:2312.03638v2, §3.7–3.8 (printed
  pp. 11–13): Definition 3.3, Lemma 3.4, Definition 3.7, Lemma 3.8.
* N. Bourbaki, *Lie Groups and Lie Algebras*, Ch. V §1: chambers and their walls.
* J. H. Conway, N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, 3rd ed., Ch. 27: the
  hyperbolic plane and its two isotropic rays.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open QuadraticMap
open LeanCategories.Modules.Bilinear.Valued

namespace LeanCategories.Lattices.Valued

/-! ## The hyperbolic plane `U` -/

/-- The first isotropic basis vector `e` of `U`. -/
def uE : Fin 2 → ℤ := Pi.single 0 1

/-- The second isotropic basis vector `f` of `U`. -/
def uF : Fin 2 → ℤ := Pi.single 1 1

/-- The root `e - f` of `U`. -/
def uRoot : Fin 2 → ℤ := uE - uF

/-- The interior vector `e + 2f` of the chamber cut out by `e - f`. -/
def uInterior : Fin 2 → ℤ := uE + 2 • uF

/-- The pairing of `U` in coordinates: `x · y = x₀ y₁ + x₁ y₀`. -/
theorem u_pairing_eq (x y : Fin 2 → ℤ) :
    hyperbolicPlaneFiniteLattice.obj.obj.pairing x y = x 0 * y 1 + x 1 * y 0 := by
  change Matrix.toBilin' hyperbolicPlaneGramMatrix x y = x 0 * y 1 + x 1 * y 0
  rw [Matrix.toBilin'_apply, Fin.sum_univ_two, Fin.sum_univ_two]
  simp [hyperbolicPlaneGramMatrix]

/-- The pairing of `U` in coordinates, on the lattice carrier. -/
theorem u_pairing_eq' (x y : hyperbolicPlaneFiniteLattice.obj.obj.carrier) :
    hyperbolicPlaneFiniteLattice.obj.obj.pairing x y = x 0 * y 1 + x 1 * y 0 := by
  change Matrix.toBilin' hyperbolicPlaneGramMatrix x y = x 0 * y 1 + x 1 * y 0
  rw [Matrix.toBilin'_apply, Fin.sum_univ_two, Fin.sum_univ_two]
  simp [hyperbolicPlaneGramMatrix]

@[simp] theorem uE_apply_zero : uE 0 = 1 := rfl
@[simp] theorem uE_apply_one : uE 1 = 0 := rfl
@[simp] theorem uF_apply_zero : uF 0 = 0 := rfl
@[simp] theorem uF_apply_one : uF 1 = 1 := rfl
@[simp] theorem uRoot_apply_zero : uRoot 0 = 1 := rfl
@[simp] theorem uRoot_apply_one : uRoot 1 = -1 := rfl
@[simp] theorem uInterior_apply_zero : uInterior 0 = 1 := rfl
@[simp] theorem uInterior_apply_one : uInterior 1 = 2 := rfl

theorem uRoot_square : hyperbolicPlaneFiniteLattice.obj.obj.pairing uRoot uRoot = -2 := by
  rw [u_pairing_eq]; norm_num

theorem uInterior_square :
    hyperbolicPlaneFiniteLattice.obj.obj.pairing uInterior uInterior = 4 := by
  rw [u_pairing_eq]; norm_num

theorem uInterior_pairing_root :
    hyperbolicPlaneFiniteLattice.obj.obj.pairing uInterior uRoot = 1 := by
  rw [u_pairing_eq]; norm_num

/-- `e - f` is a reflective root of `U`. -/
theorem uRoot_reflective : IsReflectiveRoot hyperbolicPlaneFiniteLattice.obj uRoot := by
  constructor
  · change IsRegular (hyperbolicPlaneFiniteLattice.obj.obj.pairing uRoot uRoot)
    rw [uRoot_square]
    exact IsRegular.of_ne_zero (by norm_num)
  · intro y
    change hyperbolicPlaneFiniteLattice.obj.obj.pairing uRoot uRoot ∣
      2 * hyperbolicPlaneFiniteLattice.obj.obj.pairing uRoot y
    rw [uRoot_square, u_pairing_eq']
    refine ⟨y 0 - y 1, by simp [uRoot]; ring⟩

/-- **The negative reflective vectors of `U` are exactly `±(e - f)`.** This is the classification
that the chamber's `interior_regular` field needs, proved here rather than assumed: the reflection
is integral only for vectors whose two isotropic coordinates are `±1`, and negative square forces
them to have opposite signs. -/
theorem u_reflective_neg_classification (v : Fin 2 → ℤ)
    (hrefl : IsReflectiveRoot hyperbolicPlaneFiniteLattice.obj v)
    (hneg : hyperbolicPlaneFiniteLattice.obj.obj.pairing v v < 0) :
    v = uRoot ∨ v = -uRoot := by
  obtain ⟨hreg, hdvd⟩ := hrefl
  have hsq : hyperbolicPlaneFiniteLattice.obj.obj.pairing v v = 2 * (v 0 * v 1) := by
    rw [u_pairing_eq']; ring
  have hprod : v 0 * v 1 < 0 := by rw [hsq] at hneg; linarith
  have hb : v 1 ≠ 0 := by
    rintro h; rw [h, mul_zero] at hprod; exact absurd hprod (lt_irrefl 0)
  have ha : v 0 ≠ 0 := by
    rintro h; rw [h, zero_mul] at hprod; exact absurd hprod (lt_irrefl 0)
  -- `e`-coordinate: the divisibility at `e` gives `v₀ v₁ ∣ v₁`
  have hdvd_e : hyperbolicPlaneFiniteLattice.obj.obj.pairing v v ∣
      2 * hyperbolicPlaneFiniteLattice.obj.obj.pairing v uE := hdvd uE
  rw [hsq, u_pairing_eq'] at hdvd_e
  simp only [uE_apply_zero, uE_apply_one, mul_one, mul_zero] at hdvd_e
  have hdvd_e' : v 0 * v 1 ∣ v 1 := by
    obtain ⟨k, hk⟩ := hdvd_e
    exact ⟨k, by linarith⟩
  -- `f`-coordinate: the divisibility at `f` gives `v₀ v₁ ∣ v₀`
  have hdvd_f : hyperbolicPlaneFiniteLattice.obj.obj.pairing v v ∣
      2 * hyperbolicPlaneFiniteLattice.obj.obj.pairing v uF := hdvd uF
  rw [hsq, u_pairing_eq'] at hdvd_f
  simp only [uF_apply_zero, uF_apply_one, mul_one, mul_zero] at hdvd_f
  have hdvd_f' : v 0 * v 1 ∣ v 0 := by
    obtain ⟨k, hk⟩ := hdvd_f
    exact ⟨k, by linarith⟩
  obtain ⟨k, hk⟩ := hdvd_e'
  have hk1 : v 0 * k = 1 := by
    have h4 : v 1 * (v 0 * k) = v 1 := by
      have h5 : v 1 * (v 0 * k) = v 0 * v 1 * k := by ring
      rw [h5, ← hk]
    exact mul_left_cancel₀ hb (by rw [h4, mul_one])
  obtain ⟨l, hl⟩ := hdvd_f'
  have hl1 : v 1 * l = 1 := by
    have h4 : v 0 * (v 1 * l) = v 0 := by
      have h5 : v 0 * (v 1 * l) = v 0 * v 1 * l := by ring
      rw [h5, ← hl]
    exact mul_left_cancel₀ ha (by rw [h4, mul_one])
  have h0 : v 0 = 1 ∨ v 0 = -1 := Int.eq_one_or_neg_one_of_mul_eq_one hk1
  have h1 : v 1 = 1 ∨ v 1 = -1 := Int.eq_one_or_neg_one_of_mul_eq_one hl1
  rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1
  · rw [h0, h1] at hprod; norm_num at hprod
  · left
    funext i; fin_cases i <;> simp [h0, h1]
  · right
    funext i; fin_cases i <;> simp [h0, h1]
  · rw [h0, h1] at hprod; norm_num at hprod

/-- **`U` is a chamber with the single wall `e - f`.** -/
theorem hyperbolicPlane_isChamberWithWalls :
    IsChamberWithWalls hyperbolicPlaneFiniteLattice
      (toRealForm hyperbolicPlaneFiniteLattice uInterior) {uRoot} := by
  have hQ : 0 < realFormQuadratic hyperbolicPlaneFiniteLattice
      (toRealForm hyperbolicPlaneFiniteLattice uInterior) := by
    rw [realFormQuadratic_apply, realFormPairing_toRealForm, uInterior_square]; norm_num
  refine ⟨?_, ⟨toRealForm _ uInterior, ⟨⟨hQ, ?_⟩, ?_⟩⟩, ?_⟩
  · intro r hr
    rw [Set.mem_singleton_iff] at hr
    subst hr
    exact ⟨uRoot_reflective, by rw [uRoot_square]; norm_num⟩
  · rw [associated_self_apply]; exact hQ
  · intro r hr
    rw [Set.mem_singleton_iff] at hr
    subst hr
    rw [realFormPairing_toRealForm, uInterior_pairing_root]; norm_num
  · intro z hz
    have hz' : z ∈ positiveCone.upper (realFormQuadratic hyperbolicPlaneFiniteLattice)
        (toRealForm hyperbolicPlaneFiniteLattice uInterior) ∧
        ∀ r ∈ ({uRoot} : Set (Fin 2 → ℤ)),
          0 < (realForm hyperbolicPlaneFiniteLattice).obj.pairing z
            (toRealForm hyperbolicPlaneFiniteLattice r) := hz
    refine (mem_weylRegularLocus_iff (L := hyperbolicPlaneFiniteLattice)
      (t := toRealForm hyperbolicPlaneFiniteLattice uInterior) (x := z)).mpr ⟨hz'.1, ?_⟩
    intro r hr
    have hclass : r = uRoot ∨ r = -uRoot :=
      u_reflective_neg_classification r hr.1 hr.2
    have hpos := hz'.2 uRoot (Set.mem_singleton uRoot)
    rcases hclass with h | h
    · rw [h]
      exact ne_of_gt hpos
    · rw [h]
      have hsmul : toRealForm hyperbolicPlaneFiniteLattice (-uRoot)
          = (↑(-1) : ℝ) • toRealForm hyperbolicPlaneFiniteLattice uRoot := by
        rw [show (-uRoot : Fin 2 → ℤ) = (-1 : ℤ) • uRoot from by rw [neg_one_zsmul],
          toRealForm_zsmul]
        norm_num
      have hneg : (realForm hyperbolicPlaneFiniteLattice).obj.pairing z
          (toRealForm hyperbolicPlaneFiniteLattice (-uRoot))
          = -(realForm hyperbolicPlaneFiniteLattice).obj.pairing z
              (toRealForm hyperbolicPlaneFiniteLattice uRoot) := by
        rw [hsmul]
        calc (realForm hyperbolicPlaneFiniteLattice).obj.bilinMap z
              ((↑(-1) : ℝ) • toRealForm hyperbolicPlaneFiniteLattice uRoot)
            = (↑(-1) : ℝ) • ((realForm hyperbolicPlaneFiniteLattice).obj.bilinMap z
                (toRealForm hyperbolicPlaneFiniteLattice uRoot)) := map_smul _ _ _
          _ = -((realForm hyperbolicPlaneFiniteLattice).obj.bilinMap z
                (toRealForm hyperbolicPlaneFiniteLattice uRoot)) := by
              rw [smul_eq_mul]; norm_num
      rw [hneg]
      exact ne_of_lt (by linarith)

end LeanCategories.Lattices.Valued
