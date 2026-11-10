/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Convex.Basic
public import Mathlib.GroupTheory.CosetCover
public import Mathlib.LinearAlgebra.QuadraticForm.IsometryEquiv
public import Mathlib.LinearAlgebra.QuadraticForm.Signature
public import LeanCategories.Topology.LorentzCone

/-!
# The positive cone of a real quadratic form of signature `(1, n)`

For a real quadratic form `Q` on a finite-dimensional real vector space `V` of signature
`(1, n)` — `sigPos Q = 1` — the positivity set `{x | 0 < Q x}` is the *positive cone*, with two
sheets: it is the disjoint union of the two convex sets on which a fixed positive vector `t` pairs
positively (`positiveCone.upper`) and negatively (`positiveCone.lower`). Isometries of `Q`
permute the two sheets, so the stabilizer of a sheet (`positiveConeStabilizer`) has index at most
two in the orthogonal group: this is `O⁺(V, Q)`.

The objects are Mathlib's: the pairing is `QuadraticMap.associated` (`associated_apply`, with
`QuadraticForm.associated_isSymm` for symmetry and `QuadraticMap.polarBilin` as its double), the
signature is `QuadraticForm.sigPos`, and the orthogonal group is the group of Mathlib's isometry
equivalences `Q.IsometryEquiv Q`. Mathlib gives `QuadraticMap.IsometryEquiv` with `refl`, `trans`
and `symm` but no `Group` instance on `Q.IsometryEquiv Q`, so the orthogonal group could not be
written as the whole isometry group; `instGroupIsometryEquiv` below supplies that instance.

## The mathematics

Let `Q` have signature `(1, n)`, i.e. `sigPos Q = 1`, and let `Q t > 0`. Then no two-dimensional
subspace is positive definite, which gives the *key inequality* `Q x * Q t ≤ b(x, t)²`
(`mul_self_le_associated_sq`): if it failed, the Gram matrix of `(t, x)` would be positive definite
(its determinant is positive and `Q t > 0`), and `le_sigPos_of_posDef` would put a two-dimensional
positive definite subspace inside a form of `sigPos` one. Projecting a vector off `t` along
`b(·, t)` turns it into a negative value of `Q`, and the key inequality is exactly the reverse
Cauchy–Schwarz inequality on `t^⊥` (`associated_spatialPart_sq_le`). Two points of the cone pair
positively exactly when they lie on the same side of `t^⊥` (`associated_pos_of_mem_upper`), which
makes the two sides convex and makes an isometry either fix both or exchange them.

## References

* J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, 3rd ed., Ch. 27: the
  positive cone of a Lorentzian lattice, its two sheets, and `O⁺` as the stabilizer of one.
* V. V. Nikulin, *Integral symmetric bilinear forms and some of their applications*, Izv. Akad.
  Nauk SSSR Ser. Mat. 43 (1979), §1: `O(M)` and its index-two subgroup for K3 period lattices.
* J. G. Ratcliffe, *Foundations of Hyperbolic Manifolds*, 2nd ed., §3.1: the two-sheeted
  hyperboloid of a Lorentzian form and the reverse Cauchy–Schwarz inequality.
-/

@[expose] public section

open QuadraticMap

namespace LeanCategories.Lattices.Valued

universe u

/-- `2` is invertible in `ℝ`. Mathlib writes the associated pairing of a quadratic form as `⅟2`
times the polar form and registers no such instance, so the pairing cannot be written without
this. -/
noncomputable instance instInvertibleTwoReal : Invertible (2 : ℝ) :=
  invertibleOfNonzero (by norm_num)

section Core

variable {V : Type u} [AddCommGroup V] [Module ℝ V]

/-- The **orthogonal group** of a quadratic form, as the group of Mathlib's isometry equivalences.

Searched Mathlib (pinned `v4.33.1`) for an existing group structure on these, and found none:
`QuadraticMap.IsometryEquiv` (`LinearAlgebra/QuadraticForm/IsometryEquiv.lean`) and
`LinearMap.BilinForm.IsometryEquiv` (`LinearAlgebra/BilinearForm/IsometryEquiv.lean`) each supply
`refl`, `symm` and `trans`, `EquivLike`/`LinearEquivClass` instances and a coercion to
`LinearEquiv`, but no `Group` instance on the endomorphism type and no `Subgroup` of them; the only
`orthogonalGroup` in Mathlib is the matrix one, `Matrix.orthogonalGroup n R = unitaryGroup n R`
(`LinearAlgebra/UnitaryGroup.lean`), which is not a group of form-preserving maps of an abstract
module. Supplying the instance here is what lets `O(Q)` be Mathlib's isometry group itself
(`⊤ : Subgroup (Q.IsometryEquiv Q)`) instead of a separately defined group of form-preserving
linear equivalences; nothing below redefines the object. -/
noncomputable instance instGroupIsometryEquiv (Q : QuadraticForm ℝ V) :
    Group (Q.IsometryEquiv Q) where
  mul f g := f.trans g
  one := QuadraticMap.IsometryEquiv.refl Q
  inv f := f.symm
  mul_assoc f g h := rfl
  one_mul f := rfl
  mul_one f := rfl
  inv_mul_cancel f := DFunLike.ext _ _ (fun x =>
    QuadraticMap.IsometryEquiv.apply_symm_apply f x)

/-- The self-pairing of the associated form is the form itself. Mathlib states this for
`associatedHom S`; `associated` is that map (`QuadraticMap.coe_associatedHom`). -/
theorem associated_self_apply (Q : QuadraticForm ℝ V) (x : V) : (associated Q) x x = Q x := by
  simpa [QuadraticMap.coe_associatedHom] using
    QuadraticMap.associated_eq_self_apply (S := ℝ) (Q := Q) x

/-- The associated pairing is symmetric. Mathlib states symmetry for `associatedHom S`; this is the
form of it used below. -/
theorem associated_comm (Q : QuadraticForm ℝ V) (x y : V) :
    (associated Q) x y = (associated Q) y x :=
  LinearMap.IsSymm.eq (QuadraticForm.associated_isSymm (S := ℝ) Q) x y

/-- The form evaluated on a linear combination, in terms of the associated pairing: the quadratic
expansion that every completed-square argument below uses. -/
theorem quadratic_expand (Q : QuadraticForm ℝ V) (a b : ℝ) (x y : V) :
    Q (a • x + b • y) = a ^ 2 * Q x + 2 * a * b * (associated Q) x y + b ^ 2 * Q y := by
  conv_lhs => rw [← associated_self_apply Q (a • x + b • y)]
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
    associated_self_apply]
  rw [associated_comm Q y x]
  ring

end Core

section Lorentzian

variable {V : Type u} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
variable {Q : QuadraticForm ℝ V}

/-- **The key inequality of a form of signature `(1, n)`.** For a positive vector `t`, no vector
`x` has `Q x * Q t > b(x, t)²`: that inequality would make `(t, x)` a positive definite plane,
which a form with `sigPos = 1` does not have. -/
theorem mul_self_le_associated_sq (hpos : sigPos Q = 1) {t : V} (ht : 0 < Q t) (x : V) :
    Q x * Q t ≤ (associated Q) x t ^ 2 := by
  by_contra hcon
  have hdet : (associated Q) x t ^ 2 < Q x * Q t := not_le.mp hcon
  have hPD : (Q.restrict (Submodule.span ℝ {t, x})).PosDef := by
    intro v hv
    obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.mp v.2
    rw [QuadraticMap.restrict_apply, ← hab, quadratic_expand, associated_comm Q t x]
    have hv' : a • t + b • x ≠ 0 := by
      intro hzero
      exact hv (Subtype.ext (by rw [← hab]; exact hzero))
    rcases eq_or_ne b 0 with hb0 | hb
    · subst hb0
      have ha : a ≠ 0 := by
        intro ha
        exact hv' (by rw [ha]; simp)
      nlinarith [sq_pos_of_ne_zero ha, ht]
    · nlinarith [sq_nonneg (a * Q t + b * (associated Q) x t), sq_pos_of_ne_zero hb, ht,
        mul_pos ht (sub_pos.mpr hdet)]
  have hdim : Module.finrank ℝ (Submodule.span ℝ {t, x}) ≤ 1 :=
    (le_sigPos_of_posDef (Q := Q) hPD).trans hpos.le
  have htne : t ≠ 0 := by
    intro h
    rw [h] at ht
    simp at ht
  have hsingle : Module.finrank ℝ (Submodule.span ℝ {t}) = 1 := by
    rw [finrank_span_singleton]
    simpa using htne
  have hspan : Submodule.span ℝ {t} = Submodule.span ℝ {t, x} := by
    refine Submodule.eq_of_le_of_finrank_le ?_ ?_
    · exact Submodule.span_mono
        (Set.singleton_subset_iff.mpr (Set.mem_insert_iff.mpr (Or.inl rfl)))
    · rw [hsingle]
      exact hdim
  have hx : x ∈ Submodule.span ℝ {t} := by
    rw [hspan]
    exact Submodule.subset_span (Set.mem_insert_iff.mpr (Or.inr rfl))
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hx
  have hQx : Q x = c ^ 2 * Q t := by
    rw [← hc, QuadraticMap.map_smul, smul_eq_mul]
    ring
  have hB : (associated Q) x t = c * Q t := by
    rw [← hc, map_smul, LinearMap.smul_apply, smul_eq_mul, associated_self_apply]
  rw [hQx, hB] at hdet
  nlinarith [hdet, ht]

end Lorentzian

section Cone

variable {V : Type u} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
variable {Q : QuadraticForm ℝ V}

/-- The **positive cone** of a real quadratic form: the vectors of positive value. -/
def positiveCone (Q : QuadraticForm ℝ V) : Set V := {x | 0 < Q x}

/-- The sheet of the positive cone on which a positive vector `t` pairs positively. -/
def positiveCone.upper (Q : QuadraticForm ℝ V) (t : V) : Set V :=
  {x | 0 < Q x ∧ 0 < (associated Q) x t}

/-- The other sheet: the one on which a positive vector `t` pairs negatively. -/
def positiveCone.lower (Q : QuadraticForm ℝ V) (t : V) : Set V :=
  {x | 0 < Q x ∧ (associated Q) x t < 0}

/-- The projection of `x` off the line `ℝ t` along the pairing with `t`. -/
noncomputable def spatialPart (Q : QuadraticForm ℝ V) (t x : V) : V :=
  x - ((associated Q) x t / Q t) • t

omit [FiniteDimensional ℝ V] in
/-- The projection is orthogonal to `t`. -/
theorem associated_spatialPart_right (Q : QuadraticForm ℝ V) {t : V} (ht : Q t ≠ 0) (x : V) :
    (associated Q) (spatialPart Q t x) t = 0 := by
  rw [spatialPart, map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul,
    associated_self_apply]
  field_simp
  ring

omit [FiniteDimensional ℝ V] in
/-- The value of `Q` on the projection, in terms of the pairing with `t`. -/
theorem quadratic_spatialPart (Q : QuadraticForm ℝ V) {t : V} (ht : Q t ≠ 0) (x : V) :
    Q (spatialPart Q t x) = Q x - (associated Q) x t ^ 2 / Q t := by
  have h := quadratic_expand Q (1 : ℝ) (-((associated Q) x t / Q t)) x t
  simp only [one_smul, one_pow, one_mul] at h
  rw [spatialPart, sub_eq_add_neg, ← neg_smul, h]
  field_simp
  ring

/-- **The projection has nonpositive value**: this is the key inequality, divided by `Q t`. -/
theorem quadratic_spatialPart_nonpos (Q : QuadraticForm ℝ V) (hpos : sigPos Q = 1) {t : V}
    (ht : 0 < Q t) (x : V) : Q (spatialPart Q t x) ≤ 0 := by
  have hQt : Q t ≠ 0 := ht.ne'
  rw [quadratic_spatialPart Q hQt x]
  have h := mul_self_le_associated_sq (Q := Q) hpos ht x
  have hdiv : Q x ≤ (associated Q) x t ^ 2 / Q t := by
    rw [le_div_iff₀ ht]
    linarith
  linarith

/-- **The reverse Cauchy–Schwarz inequality on the orthogonal complement of `t`.** The pairing of
two projections is bounded by the square root of the product of their (negated) values. -/
theorem associated_spatialPart_sq_le (Q : QuadraticForm ℝ V) (hpos : sigPos Q = 1) {t : V}
    (ht : 0 < Q t) (x y : V) :
    (associated Q) (spatialPart Q t x) (spatialPart Q t y) ^ 2 ≤
      (-(Q (spatialPart Q t x))) * (-(Q (spatialPart Q t y))) := by
  have hQt : Q t ≠ 0 := ht.ne'
  set u := spatialPart Q t x with hu
  set v := spatialPart Q t y with hv
  have hut : (associated Q) u t = 0 := associated_spatialPart_right Q hQt x
  have hvt : (associated Q) v t = 0 := associated_spatialPart_right Q hQt y
  have hQu : Q u ≤ 0 := quadratic_spatialPart_nonpos Q hpos ht x
  have hQv : Q v ≤ 0 := quadratic_spatialPart_nonpos Q hpos ht y
  have hexp : ∀ lam : ℝ,
      Q (u + lam • v) = Q u + 2 * lam * (associated Q) u v + lam ^ 2 * Q v := by
    intro lam
    rw [show u + lam • v = (1 : ℝ) • u + lam • v by simp, quadratic_expand]
    ring
  have hkey : ∀ lam : ℝ, Q (u + lam • v) ≤ 0 := by
    intro lam
    have h0 : (associated Q) (u + lam • v) t = 0 := by
      rw [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, hut, hvt]
      simp
    by_contra hcon
    have hpos' : 0 < Q (u + lam • v) := not_le.mp hcon
    have h := mul_self_le_associated_sq (Q := Q) hpos ht (u + lam • v)
    rw [h0] at h
    nlinarith [h, hpos']
  rcases eq_or_ne (Q v) 0 with hv0 | hvne
  · have hB0 : (associated Q) u v = 0 := by
      by_contra hB
      have hlam := hkey ((1 - Q u) / (2 * (associated Q) u v))
      rw [hexp, hv0] at hlam
      have h2 : 2 * ((1 - Q u) / (2 * (associated Q) u v)) * (associated Q) u v = 1 - Q u := by
        field_simp
      nlinarith [hlam, h2]
    simp [hB0, hv0]
  · have hQvneg : Q v < 0 := lt_of_le_of_ne hQv hvne
    have hlam := hkey (-((associated Q) u v) / Q v)
    rw [hexp] at hlam
    have hmul := mul_nonneg_of_nonpos_of_nonpos hlam hQvneg.le
    have hsimp : ∀ a b c : ℝ, c ≠ 0 →
        (a + 2 * (-b / c) * b + (-b / c) ^ 2 * c) * c = a * c - b ^ 2 := by
      intro a b c hc
      field_simp
      ring
    rw [hsimp (Q u) ((associated Q) u v) (Q v) hvne] at hmul
    nlinarith [hmul]

end Cone

section Sheets

variable {V : Type u} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
variable {Q : QuadraticForm ℝ V}

/-- On the cone the pairing with a positive vector never vanishes. -/
theorem associated_ne_zero_of_mem_positiveCone (Q : QuadraticForm ℝ V) (hpos : sigPos Q = 1)
    {t : V} (ht : 0 < Q t) {x : V} (hx : x ∈ positiveCone Q) : (associated Q) x t ≠ 0 := by
  have h := mul_self_le_associated_sq (Q := Q) hpos ht x
  have hpos' : 0 < Q x * Q t := mul_pos hx ht
  intro h0
  rw [h0] at h
  nlinarith [h, hpos']

/-- Every point of the cone lies on one of the two sheets cut out by a positive vector. -/
theorem mem_upper_or_mem_lower (Q : QuadraticForm ℝ V) (hpos : sigPos Q = 1) {t : V}
    (ht : 0 < Q t) {x : V} (hx : x ∈ positiveCone Q) :
    x ∈ positiveCone.upper Q t ∨ x ∈ positiveCone.lower Q t := by
  have hne := associated_ne_zero_of_mem_positiveCone Q hpos ht hx
  rcases lt_or_gt_of_ne hne with h | h
  · exact Or.inr ⟨hx, h⟩
  · exact Or.inl ⟨hx, h⟩

/-- The cone is the union of its two sheets. -/
theorem positiveCone_eq_upper_union_lower (Q : QuadraticForm ℝ V) (hpos : sigPos Q = 1)
    {t : V} (ht : 0 < Q t) :
    positiveCone Q = positiveCone.upper Q t ∪ positiveCone.lower Q t := by
  ext x
  constructor
  · intro hx
    exact mem_upper_or_mem_lower Q hpos ht hx
  · rintro (⟨hx, -⟩ | ⟨hx, -⟩)
    · exact hx
    · exact hx

omit [FiniteDimensional ℝ V] in
/-- The two sheets are disjoint. -/
theorem upper_disjoint_lower (Q : QuadraticForm ℝ V) (t : V) :
    Disjoint (positiveCone.upper Q t) (positiveCone.lower Q t) := by
  rw [Set.disjoint_left]
  rintro x ⟨-, hpos⟩ ⟨-, hneg⟩
  exact absurd hpos (not_lt.mpr hneg.le)

omit [FiniteDimensional ℝ V] in
/-- Negation exchanges the two sheets. -/
theorem neg_mem_upper_iff (Q : QuadraticForm ℝ V) (t x : V) :
    -x ∈ positiveCone.upper Q t ↔ x ∈ positiveCone.lower Q t := by
  have hx : Q (-x) = Q x := by
    rw [show -x = (-1 : ℝ) • x by simp, QuadraticMap.map_smul]
    simp
  have hB : (associated Q) (-x) t = -(associated Q) x t := by
    rw [show -x = (-1 : ℝ) • x by simp, map_smul, LinearMap.smul_apply, smul_eq_mul]
    ring
  rw [positiveCone.upper, positiveCone.lower]
  simp only [Set.mem_ofPred_eq]
  rw [hx, hB, neg_pos]

omit [FiniteDimensional ℝ V] in
/-- The two sheets are distinct, since one of them is nonempty. -/
theorem upper_ne_lower (Q : QuadraticForm ℝ V) (t : V) (ht : 0 < Q t) :
    positiveCone.upper Q t ≠ positiveCone.lower Q t := by
  intro h
  have h1 : 0 < (associated Q) t t := by rw [associated_self_apply]; exact ht
  have h2 : t ∈ positiveCone.lower Q t := h ▸ (⟨ht, h1⟩ : t ∈ positiveCone.upper Q t)
  exact absurd h2.2 (not_lt.mpr h1.le)

omit [FiniteDimensional ℝ V] in
/-- The image of the lower sheet is the negation of the image of the upper one. -/
theorem image_lower_eq_neg_image_upper (Q : QuadraticForm ℝ V) {t : V}
    (f : Q.IsometryEquiv Q) :
    f '' positiveCone.lower Q t = Neg.neg '' (f '' positiveCone.upper Q t) := by
  ext z
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨f (-y), ⟨-y, (neg_mem_upper_iff Q t y).mpr hy, by simp⟩, by simp⟩
  · rintro ⟨w, ⟨v, hv, rfl⟩, hz⟩
    exact ⟨-v, (neg_mem_upper_iff Q t (-v)).mp (by simpa using hv), by
      rw [map_neg]
      exact hz⟩

omit [FiniteDimensional ℝ V] in
theorem neg_image_upper (Q : QuadraticForm ℝ V) (t : V) :
    Neg.neg '' (positiveCone.upper Q t) = positiveCone.lower Q t := by
  ext z
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (neg_mem_upper_iff Q t (-y)).mp (by simpa using hy)
  · intro hz
    exact ⟨-z, (neg_mem_upper_iff Q t z).mpr hz, by simp⟩

omit [FiniteDimensional ℝ V] in
theorem neg_image_lower (Q : QuadraticForm ℝ V) (t : V) :
    Neg.neg '' (positiveCone.lower Q t) = positiveCone.upper Q t := by
  ext z
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (neg_mem_upper_iff Q t y).mpr hy
  · intro hz
    exact ⟨-z, (neg_mem_upper_iff Q t (-z)).mp (by simpa using hz), by simp⟩

/-- **Two points of the same sheet pair positively.** This is the reverse Cauchy–Schwarz
inequality read through the projection off `t`. -/
theorem associated_pos_of_mem_upper (Q : QuadraticForm ℝ V) (hpos : sigPos Q = 1) {t : V}
    (ht : 0 < Q t) {x y : V} (hx : x ∈ positiveCone.upper Q t)
    (hy : y ∈ positiveCone.upper Q t) : 0 < (associated Q) x y := by
  obtain ⟨hQx, hBx⟩ := hx
  obtain ⟨hQy, hBy⟩ := hy
  have hQt : Q t ≠ 0 := ht.ne'
  set u := spatialPart Q t x with hu
  set v := spatialPart Q t y with hv
  set alpha : ℝ := (associated Q) x t / Q t with halpha
  set beta : ℝ := (associated Q) y t / Q t with hbeta
  have hxrep : x = alpha • t + u := by
    rw [halpha, hu, spatialPart]
    abel
  have hyrep : y = beta • t + v := by
    rw [hbeta, hv, spatialPart]
    abel
  have hut : (associated Q) u t = 0 := associated_spatialPart_right Q hQt x
  have hvt : (associated Q) v t = 0 := associated_spatialPart_right Q hQt y
  have hQu : Q u ≤ 0 := quadratic_spatialPart_nonpos Q hpos ht x
  have hQv : Q v ≤ 0 := quadratic_spatialPart_nonpos Q hpos ht y
  have hcs := associated_spatialPart_sq_le Q hpos ht x y
  have hQxeq : Q x = alpha ^ 2 * Q t + Q u := by
    conv_lhs => rw [hxrep, ← one_smul ℝ u]
    rw [quadratic_expand, associated_comm Q t u, hut]
    ring
  have hQyeq : Q y = beta ^ 2 * Q t + Q v := by
    conv_lhs => rw [hyrep, ← one_smul ℝ v]
    rw [quadratic_expand, associated_comm Q t v, hvt]
    ring
  have hsplit : (associated Q) x y = alpha * beta * Q t + (associated Q) u v := by
    calc (associated Q) x y = (associated Q) (alpha • t + u) (beta • t + v) := by
          rw [hxrep, hyrep]
      _ = alpha * beta * Q t + (associated Q) u v := by
          simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
            hut, associated_comm Q t v, hvt, associated_self_apply]
          ring
  have halphaPos : 0 < alpha * Q t := by
    rw [halpha, div_mul_cancel₀ _ hQt]
    exact hBx
  have hbetaPos : 0 < beta * Q t := by
    rw [hbeta, div_mul_cancel₀ _ hQt]
    exact hBy
  have hleft : -Q u < alpha ^ 2 * Q t := by linarith
  have hright : -Q v < beta ^ 2 * Q t := by linarith
  have huNonneg : 0 ≤ -Q u := by linarith
  have hvNonneg : 0 ≤ -Q v := by linarith
  have hprod : (alpha ^ 2 * Q t) * (beta ^ 2 * Q t) = (alpha * beta * Q t) ^ 2 := by ring
  have hbetaSqPos : 0 < beta ^ 2 * Q t := by linarith
  have hbig : (-Q u) * (-Q v) < (alpha * beta * Q t) ^ 2 := by
    calc (-Q u) * (-Q v) ≤ (-Q u) * (beta ^ 2 * Q t) :=
          mul_le_mul_of_nonneg_left hright.le huNonneg
      _ < (alpha ^ 2 * Q t) * (beta ^ 2 * Q t) :=
          mul_lt_mul_of_pos_right hleft hbetaSqPos
      _ = (alpha * beta * Q t) ^ 2 := hprod
  have hAB : 0 < alpha * beta * Q t := by nlinarith [halphaPos, hbetaPos, ht]
  nlinarith [hcs, hbig, hAB, sq_abs ((associated Q) u v), hsplit]

/-- **Two points on opposite sheets pair negatively.** -/
theorem associated_neg_of_mem_upper_lower (Q : QuadraticForm ℝ V) (hpos : sigPos Q = 1)
    {t : V} (ht : 0 < Q t) {x y : V} (hx : x ∈ positiveCone.upper Q t)
    (hy : y ∈ positiveCone.lower Q t) : (associated Q) x y < 0 := by
  have hneg : -y ∈ positiveCone.upper Q t := (neg_mem_upper_iff Q t y).mpr hy
  have h := associated_pos_of_mem_upper Q hpos ht hx hneg
  have h1 : (associated Q) x (-y) = -(associated Q) x y := map_neg ((associated Q) x) y
  rw [h1] at h
  linarith

/-- **Two points of the lower sheet pair positively.** -/
theorem associated_pos_of_mem_lower (Q : QuadraticForm ℝ V) (hpos : sigPos Q = 1) {t : V}
    (ht : 0 < Q t) {x y : V} (hx : x ∈ positiveCone.lower Q t)
    (hy : y ∈ positiveCone.lower Q t) : 0 < (associated Q) x y := by
  rw [← neg_mem_upper_iff Q t x, ← neg_mem_upper_iff Q t y] at *
  have h := associated_pos_of_mem_upper Q hpos ht hx hy
  have h1 : (associated Q) (-x) (-y) = (associated Q) x y := by
    rw [map_neg ((associated Q) (-x)) y, map_neg (associated Q) x]
    simp
  rw [h1] at h
  exact h

/-- Points of the cone that pair positively lie on the same sheet. -/
theorem mem_upper_iff_of_associated_pos (Q : QuadraticForm ℝ V) (hpos : sigPos Q = 1) {t : V}
    (ht : 0 < Q t) {u v : V} (hu : u ∈ positiveCone Q) (hv : v ∈ positiveCone Q)
    (h : 0 < (associated Q) u v) :
    (u ∈ positiveCone.upper Q t ↔ v ∈ positiveCone.upper Q t) := by
  rcases mem_upper_or_mem_lower Q hpos ht hu with h1 | h1 <;>
    rcases mem_upper_or_mem_lower Q hpos ht hv with h2 | h2
  · exact ⟨fun _ => h2, fun _ => h1⟩
  · exact absurd h (not_lt.mpr (associated_neg_of_mem_upper_lower Q hpos ht h1 h2).le)
  · refine absurd h (not_lt.mpr ?_)
    rw [associated_comm]
    exact (associated_neg_of_mem_upper_lower Q hpos ht h2 h1).le
  · exact ⟨fun h3 => absurd h3.2 (not_lt.mpr h1.2.le),
      fun h3 => absurd h3.2 (not_lt.mpr h2.2.le)⟩

omit [FiniteDimensional ℝ V] in
/-- A convex combination of a same-sheet pair has positive value. -/
theorem quadratic_pos_of_convexCombination (Q : QuadraticForm ℝ V) {x y : V} (hQx : 0 < Q x)
    (hQy : 0 < Q y) (hpair : 0 < (associated Q) x y) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a + b = 1) : 0 < Q (a • x + b • y) := by
  rw [quadratic_expand]
  have hcross : 0 ≤ 2 * a * b * (associated Q) x y := by
    have hab' : 0 ≤ a * b := mul_nonneg ha hb
    nlinarith [hab', hpair]
  have hstrict : 0 < a ^ 2 * Q x + b ^ 2 * Q y := by
    rcases eq_or_lt_of_le ha with ha0 | hapos
    · have hb1 : b = 1 := by linarith
      rw [← ha0, hb1]
      simpa using hQy
    · have hterm : 0 < a ^ 2 * Q x := mul_pos (pow_pos hapos 2) hQx
      nlinarith [hterm, sq_nonneg b, hQy]
  linarith [hcross, hstrict]

theorem convex_upper (Q : QuadraticForm ℝ V) (hpos : sigPos Q = 1) {t : V} (ht : 0 < Q t) :
    Convex ℝ (positiveCone.upper Q t) := by
  intro x hx y hy a b ha hb hab
  obtain ⟨hQx, hBx⟩ := hx
  obtain ⟨hQy, hBy⟩ := hy
  have hpair : 0 < (associated Q) x y :=
    associated_pos_of_mem_upper Q hpos ht ⟨hQx, hBx⟩ ⟨hQy, hBy⟩
  constructor
  · exact quadratic_pos_of_convexCombination Q hQx hQy hpair ha hb hab
  · rw [map_add, map_smul, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
      LinearMap.smul_apply, smul_eq_mul, smul_eq_mul]
    rcases eq_or_lt_of_le ha with ha0 | hapos
    · have hb1 : b = 1 := by linarith
      rw [← ha0, hb1]
      simpa using hBy
    · have h1 : 0 < a * (associated Q) x t := mul_pos hapos hBx
      have h2 : 0 ≤ b * (associated Q) y t := mul_nonneg hb hBy.le
      linarith

theorem convex_lower (Q : QuadraticForm ℝ V) (hpos : sigPos Q = 1) {t : V} (ht : 0 < Q t) :
    Convex ℝ (positiveCone.lower Q t) := by
  intro x hx y hy a b ha hb hab
  obtain ⟨hQx, hBx⟩ := hx
  obtain ⟨hQy, hBy⟩ := hy
  have hpair : 0 < (associated Q) x y :=
    associated_pos_of_mem_lower Q hpos ht ⟨hQx, hBx⟩ ⟨hQy, hBy⟩
  constructor
  · exact quadratic_pos_of_convexCombination Q hQx hQy hpair ha hb hab
  · rw [map_add, map_smul, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
      LinearMap.smul_apply, smul_eq_mul, smul_eq_mul]
    rcases eq_or_lt_of_le ha with ha0 | hapos
    · have hb1 : b = 1 := by linarith
      rw [← ha0, hb1]
      simpa using hBy
    · have h1 : a * (associated Q) x t < 0 := mul_neg_of_pos_of_neg hapos hBx
      have h2 : b * (associated Q) y t ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hb hBy.le
      linarith

end Sheets

section Isometries

variable {V : Type u} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
variable {Q : QuadraticForm ℝ V}

omit [FiniteDimensional ℝ V] in
/-- An isometry of `Q` preserves the associated pairing. -/
theorem associated_map (f : Q.IsometryEquiv Q) (x y : V) :
    (associated Q) (f x) (f y) = (associated Q) x y := by
  have h1 := quadratic_expand Q (1 : ℝ) (1 : ℝ) (f x) (f y)
  simp only [one_smul, one_pow, one_mul] at h1
  have h2 := quadratic_expand Q (1 : ℝ) (1 : ℝ) x y
  simp only [one_smul, one_pow, one_mul] at h2
  have h3 : f x + f y = f (x + y) := (map_add f x y).symm
  rw [h3, QuadraticMap.IsometryEquiv.map_app, QuadraticMap.IsometryEquiv.map_app,
    QuadraticMap.IsometryEquiv.map_app] at h1
  linarith [h1, h2]

/-- The image of a sheet under an isometry lies inside one sheet. -/
theorem image_upper_subset_sheet (Q : QuadraticForm ℝ V) (hpos : sigPos Q = 1) {t : V}
    (ht : 0 < Q t) (f : Q.IsometryEquiv Q) :
    f '' positiveCone.upper Q t ⊆ positiveCone.upper Q t ∨
      f '' positiveCone.upper Q t ⊆ positiveCone.lower Q t := by
  have htUpper : t ∈ positiveCone.upper Q t := ⟨ht, by rw [associated_self_apply]; exact ht⟩
  have hftCone : f t ∈ positiveCone Q := by
    change 0 < Q (f t)
    rw [QuadraticMap.IsometryEquiv.map_app]
    exact ht
  have hkey : ∀ x ∈ positiveCone.upper Q t,
      (f x ∈ positiveCone.upper Q t ↔ f t ∈ positiveCone.upper Q t) := by
    intro x hx
    have hxcone : f x ∈ positiveCone Q := by
      change 0 < Q (f x)
      rw [QuadraticMap.IsometryEquiv.map_app]
      exact hx.1
    refine mem_upper_iff_of_associated_pos Q hpos ht hxcone hftCone ?_
    rw [associated_map f x t]
    exact hx.2
  rcases mem_upper_or_mem_lower Q hpos ht hftCone with h | h
  · left
    rintro z ⟨x, hx, rfl⟩
    exact (hkey x hx).mpr h
  · right
    rintro z ⟨x, hx, rfl⟩
    have hxcone : f x ∈ positiveCone Q := by
      change 0 < Q (f x)
      rw [QuadraticMap.IsometryEquiv.map_app]
      exact hx.1
    have hnot : ¬ f x ∈ positiveCone.upper Q t :=
      fun h' => absurd ((hkey x hx).mp h').2 (not_lt.mpr h.2.le)
    rcases mem_upper_or_mem_lower Q hpos ht hxcone with h' | h'
    · exact absurd h' hnot
    · exact h'

omit [FiniteDimensional ℝ V] in
/-- The two images of the two sheets are distinct, since `f` is injective and the sheets are
disjoint and nonempty. -/
theorem image_lower_ne_image_upper (Q : QuadraticForm ℝ V) {t : V} (ht : 0 < Q t)
    (f : Q.IsometryEquiv Q) :
    f '' positiveCone.lower Q t ≠ f '' positiveCone.upper Q t := by
  intro h
  have htUpper : t ∈ positiveCone.upper Q t := ⟨ht, by rw [associated_self_apply]; exact ht⟩
  have hntLower : -t ∈ positiveCone.lower Q t := by
    rw [← neg_mem_upper_iff Q t (-t), neg_neg]
    exact htUpper
  have hmem : f (-t) ∈ f '' positiveCone.upper Q t := by
    rw [← h]
    exact ⟨-t, hntLower, rfl⟩
  obtain ⟨y, hy, hyz⟩ := hmem
  have hyy : y = -t := f.injective hyz
  rw [hyy] at hy
  exact (Set.disjoint_left.mp (upper_disjoint_lower Q t)) hy hntLower

/-- **An isometry of a form of signature `(1, n)` permutes the two sheets of the cone.** -/
theorem image_upper_eq_upper_or_lower (Q : QuadraticForm ℝ V) (hpos : sigPos Q = 1) {t : V}
    (ht : 0 < Q t) (f : Q.IsometryEquiv Q) :
    f '' positiveCone.upper Q t = positiveCone.upper Q t ∨
      f '' positiveCone.upper Q t = positiveCone.lower Q t := by
  have hcone : f '' positiveCone Q = positiveCone Q := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      change 0 < Q (f x)
      rw [QuadraticMap.IsometryEquiv.map_app]
      exact hx
    · intro hz
      refine ⟨f.symm z, ?_, by simp⟩
      change 0 < Q (f.symm z)
      rw [← QuadraticMap.IsometryEquiv.map_app f (f.symm z), f.apply_symm_apply]
      exact hz
  rcases image_upper_subset_sheet Q hpos ht f with hsub | hsub
  · left
    have hlower : f '' positiveCone.lower Q t ⊆ positiveCone.lower Q t := by
      rintro z ⟨x, hx, rfl⟩
      have himg : f (-x) ∈ positiveCone.upper Q t :=
        hsub ⟨-x, (neg_mem_upper_iff Q t x).mpr hx, rfl⟩
      rw [map_neg] at himg
      exact (neg_mem_upper_iff Q t (f x)).mp himg
    refine Set.eq_of_subset_of_subset hsub ?_
    intro z hz
    have hzcone : z ∈ positiveCone Q := by
      rw [positiveCone_eq_upper_union_lower Q hpos ht]
      exact Or.inl hz
    have hmem : z ∈ f '' positiveCone.upper Q t ∪ f '' positiveCone.lower Q t := by
      rw [← Set.image_union, ← positiveCone_eq_upper_union_lower Q hpos ht, hcone]
      exact hzcone
    rcases hmem with h | h
    · exact h
    · exact absurd (hlower h) (fun hmem =>
        (Set.disjoint_left.mp (upper_disjoint_lower Q t)) hz hmem)
  · right
    have hlower : f '' positiveCone.lower Q t ⊆ positiveCone.upper Q t := by
      rintro z ⟨x, hx, rfl⟩
      have himg : f (-x) ∈ positiveCone.lower Q t :=
        hsub ⟨-x, (neg_mem_upper_iff Q t x).mpr hx, rfl⟩
      rw [map_neg] at himg
      have hm := (neg_mem_upper_iff Q t (-(f x))).mpr himg
      simpa using hm
    refine Set.eq_of_subset_of_subset hsub ?_
    intro z hz
    have hzcone : z ∈ positiveCone Q := by
      rw [positiveCone_eq_upper_union_lower Q hpos ht]
      exact Or.inr hz
    have hmem : z ∈ f '' positiveCone.upper Q t ∪ f '' positiveCone.lower Q t := by
      rw [← Set.image_union, ← positiveCone_eq_upper_union_lower Q hpos ht, hcone]
      exact hzcone
    rcases hmem with h | h
    · exact h
    · exact absurd (hlower h) (fun hmem =>
        (Set.disjoint_left.mp (upper_disjoint_lower Q t)) hmem hz)

/-- The image of the lower sheet under an isometry, in terms of the image of the upper one. -/
theorem image_lower_eq (Q : QuadraticForm ℝ V) (hpos : sigPos Q = 1) {t : V} (ht : 0 < Q t)
    (f : Q.IsometryEquiv Q) :
    f '' positiveCone.lower Q t =
      if f '' positiveCone.upper Q t = positiveCone.upper Q t
        then positiveCone.lower Q t else positiveCone.upper Q t := by
  by_cases h : f '' positiveCone.upper Q t = positiveCone.upper Q t
  · rw [if_pos h, image_lower_eq_neg_image_upper, h, neg_image_upper]
  · rw [if_neg h]
    have hswap : f '' positiveCone.upper Q t = positiveCone.lower Q t :=
      (image_upper_eq_upper_or_lower Q hpos ht f).resolve_left h
    rw [image_lower_eq_neg_image_upper, hswap, neg_image_lower]

omit [FiniteDimensional ℝ V] in
/-- The image of a sheet under a product is the iterated image. The group law composes
left-to-right: `(f * g) x = g (f x)`. -/
theorem image_mul (Q : QuadraticForm ℝ V) (f g : Q.IsometryEquiv Q) (s : Set V) :
    ((f * g : Q.IsometryEquiv Q)) '' s = g '' (f '' s) := by
  ext z
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨f y, ⟨y, hy, rfl⟩, rfl⟩
  · rintro ⟨w, ⟨y, hy, hwy⟩, hz⟩
    refine ⟨y, hy, ?_⟩
    rw [show (f * g : Q.IsometryEquiv Q) y = g (f y) from rfl, hwy]
    exact hz

/-- **An isometry that exchanges the sheets carries the lower sheet onto the upper one.** -/
theorem image_lower_of_swap (Q : QuadraticForm ℝ V) (hpos : sigPos Q = 1) {t : V}
    (ht : 0 < Q t) (f : Q.IsometryEquiv Q)
    (hf : f '' positiveCone.upper Q t = positiveCone.lower Q t) :
    f '' positiveCone.lower Q t = positiveCone.upper Q t := by
  have h := image_lower_eq Q hpos ht f
  rw [if_neg (by rw [hf]; exact (upper_ne_lower Q t ht).symm)] at h
  exact h

/-- The sign character of the cone: `1` on the isometries preserving the two sheets, `-1` on those
exchanging them. -/
noncomputable def positiveConeSign (Q : QuadraticForm ℝ V) (hpos : sigPos Q = 1) (t : V)
    (ht : 0 < Q t) : (Q.IsometryEquiv Q) →* ℤˣ where
  toFun f := by
    classical
    exact if f '' positiveCone.upper Q t = positiveCone.upper Q t then 1 else -1
  map_one' := by
    classical
    have hfun : ⇑((1 : Q.IsometryEquiv Q)) = id := funext fun x => rfl
    have h : ((1 : Q.IsometryEquiv Q)) '' positiveCone.upper Q t = positiveCone.upper Q t := by
      rw [hfun, Set.image_id]
    simp only [h, if_true]
  map_mul' f g := by
    classical
    have hne := upper_ne_lower Q t ht
    have hmul : ((f * g : Q.IsometryEquiv Q)) '' positiveCone.upper Q t =
        g '' (f '' positiveCone.upper Q t) := image_mul Q f g _
    have hgl : g '' positiveCone.lower Q t =
        if g '' positiveCone.upper Q t = positiveCone.upper Q t
          then positiveCone.lower Q t else positiveCone.upper Q t := image_lower_eq Q hpos ht g
    rw [hmul]
    by_cases hf : f '' positiveCone.upper Q t = positiveCone.upper Q t
    · rw [hf]
      by_cases hg : g '' positiveCone.upper Q t = positiveCone.upper Q t
      · rw [if_pos hg]
        simp
      · rw [if_neg hg]
        simp
    · have hfs : f '' positiveCone.upper Q t = positiveCone.lower Q t :=
        (image_upper_eq_upper_or_lower Q hpos ht f).resolve_left hf
      rw [hfs, hgl]
      by_cases hg : g '' positiveCone.upper Q t = positiveCone.upper Q t
      · rw [if_pos hg, if_pos hg, if_neg (Ne.symm hne)]
        simp
      · rw [if_neg hg, if_neg hg]
        simp [Ne.symm hne]

/-- **`O⁺(Q)`**: the isometries preserving each sheet of the positive cone, i.e. the stabilizer of
one sheet. -/
noncomputable def positiveConeStabilizer (Q : QuadraticForm ℝ V) (hpos : sigPos Q = 1) (t : V)
    (ht : 0 < Q t) : Subgroup (Q.IsometryEquiv Q) :=
  MonoidHom.ker (positiveConeSign Q hpos t ht)

theorem mem_positiveConeStabilizer_iff (Q : QuadraticForm ℝ V) (hpos : sigPos Q = 1) {t : V}
    (ht : 0 < Q t) (f : Q.IsometryEquiv Q) :
    f ∈ positiveConeStabilizer Q hpos t ht ↔
      f '' positiveCone.upper Q t = positiveCone.upper Q t := by
  classical
  rw [positiveConeStabilizer, MonoidHom.mem_ker]
  constructor
  · intro h
    by_contra hcon
    rw [show positiveConeSign Q hpos t ht f
        = if f '' positiveCone.upper Q t = positiveCone.upper Q t then 1 else -1
        from rfl, if_neg hcon] at h
    exact absurd h (by decide : ¬ (-1 : ℤˣ) = 1)
  · intro h
    rw [show positiveConeSign Q hpos t ht f
        = if f '' positiveCone.upper Q t = positiveCone.upper Q t then 1 else -1 from rfl,
      if_pos h]

/-- **`O⁺(Q)` has index at most two** in the orthogonal group. -/
theorem positiveConeStabilizer_index_le_two (Q : QuadraticForm ℝ V) (hpos : sigPos Q = 1)
    {t : V} (ht : 0 < Q t) : (positiveConeStabilizer Q hpos t ht).index ≤ 2 := by
  classical
  rw [positiveConeStabilizer, Subgroup.index_ker]
  calc Nat.card ↥(MonoidHom.range (positiveConeSign Q hpos t ht))
      ≤ Nat.card ℤˣ := Nat.card_le_card_of_injective _ Subtype.val_injective
    _ = 2 := by rw [Nat.card_eq_fintype_card, Fintype.card_units_int]

/-- `O⁺(Q)` has finite index in the orthogonal group. -/
theorem positiveConeStabilizer_finiteIndex (Q : QuadraticForm ℝ V) (hpos : sigPos Q = 1)
    {t : V} (ht : 0 < Q t) : (positiveConeStabilizer Q hpos t ht).FiniteIndex where
  index_ne_zero := by
    classical
    rw [positiveConeStabilizer, Subgroup.index_ker]
    exact Nat.card_ne_zero.mpr ⟨⟨1, Subgroup.one_mem _⟩, inferInstance⟩

end Isometries

end LeanCategories.Lattices.Valued
