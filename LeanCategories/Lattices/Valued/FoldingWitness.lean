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

Everything the joining theorem asks for is then a theorem of this file, not a hypothesis:
`u_witnessed` instantiates `isChamberWithWalls_invariant_of_chamber` at `g = 1` and discharges

* the ambient chamber — `hyperbolicPlane_isChamberWithWalls`,
* the involution law and the preservation of the chamber cone (the identity fixes every point),
* the interior lattice vector `w = e + 2f` of the invariant lattice (`hw`, `hwv`), and
* the completeness of the wall set (`hcomplete`) — from `u_root_classification_fixed`, the
  classification read in the invariant lattice,

and concludes both the maximal-dimension statement and `IsChamberWithWalls (M^σ)` with the folded
wall set. The involution is the identity, which is the only chamber-preserving involution of `U` (the
swap of `e` and `f` sends the wall to its negative and exchanges the two sides of the chamber). A
*non-trivial* involution instance needs a Lorentzian lattice with more than one chamber wall, and
the one such chamber in this repository cannot supply it: the `E₁₀` diagram is a tree with a unique
branch point (node `4`, degree `3`) whose three branches have lengths `1`, `2` and `6`, so its
automorphism group is trivial (`FoldingE10Rigidity.lean`). A non-trivial instance therefore has to
come from `T_dP` with `I = -I_En` — the source's setting — whose folded diagrams rest on the
untabulated 19- and 22-vertex diagrams of AEGS Figure 5.

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

/-! ## The invariant lattice of the identity involution -/

/-- The fixed sublattice of the identity involution is the whole lattice. -/
theorem involutionFixedSubmodule_one :
    involutionFixedSubmodule (L := hyperbolicPlaneFiniteLattice)
      (1 : OrthogonalGroup hyperbolicPlaneFiniteLattice.obj) = ⊤ := by
  rw [involutionFixedSubmodule]
  have h : isometryLinearMap (L := hyperbolicPlaneFiniteLattice)
      (1 : OrthogonalGroup hyperbolicPlaneFiniteLattice.obj) = 1 := rfl
  rw [h, sub_self, LinearMap.ker_zero]

/-- The root `e - f` as a vector of the invariant lattice of the identity involution. -/
def uRootFixed : involutionFixedSubmodule (L := hyperbolicPlaneFiniteLattice)
    (1 : OrthogonalGroup hyperbolicPlaneFiniteLattice.obj) :=
  ⟨uRoot, by rw [involutionFixedSubmodule_one]; trivial⟩

/-- The interior vector `e + 2f` as a vector of the invariant lattice of the identity involution. -/
def uInteriorFixed : involutionFixedSubmodule (L := hyperbolicPlaneFiniteLattice)
    (1 : OrthogonalGroup hyperbolicPlaneFiniteLattice.obj) :=
  ⟨uInterior, by rw [involutionFixedSubmodule_one]; trivial⟩

/-- The folded root set of the identity involution with the single wall `e - f` is the single
vector `e - f` of the invariant lattice. -/
theorem u_foldedRootSet_one :
    foldedRootSet (L := hyperbolicPlaneFiniteLattice)
      (1 : OrthogonalGroup hyperbolicPlaneFiniteLattice.obj) {uRoot} = {uRootFixed} := by
  ext v
  rw [mem_foldedRootSet_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨⟨r, hr, hfold⟩, -, -⟩
    rw [Set.mem_singleton_iff] at hr
    subst hr
    rw [show foldedVector (1 : OrthogonalGroup hyperbolicPlaneFiniteLattice.obj) uRoot
        = uRoot from foldedVector_of_fixed _ rfl] at hfold
    exact Subtype.ext hfold.symm
  · rintro rfl
    refine ⟨⟨uRoot, rfl, ?_⟩, ?_, ?_⟩
    · rw [show foldedVector (1 : OrthogonalGroup hyperbolicPlaneFiniteLattice.obj) uRoot
        = uRoot from foldedVector_of_fixed _ rfl]
      rfl
    · change hyperbolicPlaneFiniteLattice.obj.obj.pairing uRoot uRoot < 0
      rw [uRoot_square]; norm_num
    · intro x
      change hyperbolicPlaneFiniteLattice.obj.obj.pairing uRoot uRoot ∣
        2 * hyperbolicPlaneFiniteLattice.obj.obj.pairing uRoot x.1
      rw [uRoot_square, u_pairing_eq']
      refine ⟨x.1 0 - x.1 1, ?_⟩
      simp [uRoot]
      ring

/-- The classification, read in the invariant lattice of the identity involution. -/
theorem u_root_classification_fixed (ρ : involutionFixedSubmodule
      (L := hyperbolicPlaneFiniteLattice) (1 : OrthogonalGroup hyperbolicPlaneFiniteLattice.obj))
    (hρ : ρ ∈ negativeReflectiveRoots
      (invariantFixedLattice (L := hyperbolicPlaneFiniteLattice)
        (1 : OrthogonalGroup hyperbolicPlaneFiniteLattice.obj))) :
    ρ = uRootFixed ∨ ρ = -uRootFixed := by
  obtain ⟨hrefl, hneg⟩ := hρ
  have hreflU : IsReflectiveRoot hyperbolicPlaneFiniteLattice.obj (ρ.1 : Fin 2 → ℤ) := by
    refine ⟨?_, ?_⟩
    · change IsRegular (hyperbolicPlaneFiniteLattice.obj.obj.pairing ρ.1 ρ.1)
      rw [← invariantFixedLattice_pairing (L := hyperbolicPlaneFiniteLattice) (g :=
        (1 : OrthogonalGroup hyperbolicPlaneFiniteLattice.obj)) ρ ρ]
      exact hrefl.regular
    · intro y
      change hyperbolicPlaneFiniteLattice.obj.obj.pairing ρ.1 ρ.1 ∣
        2 * hyperbolicPlaneFiniteLattice.obj.obj.pairing ρ.1 y
      have h := hrefl.dvd_two_mul
        (⟨y, by rw [involutionFixedSubmodule_one]; trivial⟩ : involutionFixedSubmodule
          (L := hyperbolicPlaneFiniteLattice)
            (1 : OrthogonalGroup hyperbolicPlaneFiniteLattice.obj))
      exact h
  have hnegU : hyperbolicPlaneFiniteLattice.obj.obj.pairing ρ.1 ρ.1 < 0 := by
    rw [← invariantFixedLattice_pairing (L := hyperbolicPlaneFiniteLattice) (g :=
      (1 : OrthogonalGroup hyperbolicPlaneFiniteLattice.obj)) ρ ρ]
    exact hneg
  rcases u_reflective_neg_classification ρ.1 hreflU hnegU with h | h
  · left; exact Subtype.ext h
  · right; exact Subtype.ext h

/-- **The joining theorem, fully instantiated.** On the hyperbolic plane with the identity
involution — the only chamber-preserving involution of `U` — every hypothesis of
`isChamberWithWalls_invariant_of_chamber` is a theorem of this file: the ambient chamber
(`hyperbolicPlane_isChamberWithWalls`), the involution law, the preservation of the cone, the
interior lattice vector `e + 2f`, and the completeness of the wall set (from the classification
`u_root_classification_fixed`). The conclusion is the maximal-dimension statement together with
`IsChamberWithWalls` for the invariant lattice with the folded wall set. -/
theorem u_witnessed :
    (∃ v ∈ realFormFixedPart (1 : OrthogonalGroup hyperbolicPlaneFiniteLattice.obj),
        v ∈ rootInteriorCone hyperbolicPlaneFiniteLattice
          (toRealForm hyperbolicPlaneFiniteLattice uInterior)
          (foldedRootImage (1 : OrthogonalGroup hyperbolicPlaneFiniteLattice.obj) {uRoot})) ∧
      IsChamberWithWalls
        (invariantFixedLattice (L := hyperbolicPlaneFiniteLattice)
          (1 : OrthogonalGroup hyperbolicPlaneFiniteLattice.obj))
        (toRealForm _ uInteriorFixed) {uRootFixed} := by
  have hw : 0 < (invariantFixedLattice (L := hyperbolicPlaneFiniteLattice)
      (1 : OrthogonalGroup hyperbolicPlaneFiniteLattice.obj)).obj.obj.pairing
        uInteriorFixed uInteriorFixed := by
    rw [invariantFixedLattice_pairing]
    change 0 < hyperbolicPlaneFiniteLattice.obj.obj.pairing uInterior uInterior
    rw [uInterior_square]; norm_num
  have hwv : ∀ v ∈ foldedRootSet (L := hyperbolicPlaneFiniteLattice)
      (1 : OrthogonalGroup hyperbolicPlaneFiniteLattice.obj) {uRoot},
      0 < (invariantFixedLattice (L := hyperbolicPlaneFiniteLattice)
        (1 : OrthogonalGroup hyperbolicPlaneFiniteLattice.obj)).obj.obj.pairing
          uInteriorFixed v := by
    intro v hv
    rw [u_foldedRootSet_one, Set.mem_singleton_iff] at hv
    subst hv
    rw [invariantFixedLattice_pairing]
    change 0 < hyperbolicPlaneFiniteLattice.obj.obj.pairing uInterior uRoot
    rw [uInterior_pairing_root]; norm_num
  have hcomplete : ∀ ρ ∈ negativeReflectiveRoots (invariantFixedLattice
      (L := hyperbolicPlaneFiniteLattice) (1 : OrthogonalGroup hyperbolicPlaneFiniteLattice.obj)),
      ∃ v ∈ foldedRootSet (L := hyperbolicPlaneFiniteLattice)
        (1 : OrthogonalGroup hyperbolicPlaneFiniteLattice.obj) {uRoot},
        ∃ k : ℤ, k ≠ 0 ∧ ρ = k • v := by
    intro ρ hρ
    rcases u_root_classification_fixed ρ hρ with h | h
    · refine ⟨uRootFixed, by rw [u_foldedRootSet_one]; rfl, 1, one_ne_zero, ?_⟩
      rw [h, one_zsmul]
    · refine ⟨uRootFixed, by rw [u_foldedRootSet_one]; rfl, -1, by norm_num, ?_⟩
      rw [h, neg_one_zsmul]
  obtain ⟨hmax, hch⟩ := isChamberWithWalls_invariant_of_chamber
    (g := (1 : OrthogonalGroup hyperbolicPlaneFiniteLattice.obj))
    (L := hyperbolicPlaneFiniteLattice)
    (one_mul 1) (toRealForm hyperbolicPlaneFiniteLattice uInterior)
    (by rw [hyperbolicPlane_integralSignature])
    (by rw [realFormQuadratic_apply, realFormPairing_toRealForm, uInterior_square]; norm_num)
    {uRoot} hyperbolicPlane_isChamberWithWalls (by
      intro z hz
      have h1 : realFormOrthogonalHom hyperbolicPlaneFiniteLattice
          (1 : OrthogonalGroup hyperbolicPlaneFiniteLattice.obj) z = z := by
        rw [map_one]; rfl
      rwa [h1])
    uInteriorFixed hw hwv hcomplete
  exact ⟨hmax, by rwa [u_foldedRootSet_one] at hch⟩

end LeanCategories.Lattices.Valued
