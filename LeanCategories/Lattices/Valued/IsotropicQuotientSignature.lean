/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Lattices.Valued.Signature
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import Mathlib.LinearAlgebra.QuadraticForm.Prod
public import Mathlib.LinearAlgebra.QuadraticForm.Signature

/-!
# The signature of `e^⊥/e` is `(p − 1, q − 1)`

Let `K` be an ordered field, `Q` a nondegenerate quadratic form on a finite-dimensional `K`-space
`V` of signature `(p, q)`, and `e ≠ 0` an isotropic vector. Then the form induced on `e^⊥/⟨e⟩` has
signature `(p − 1, q − 1)` (`sigPos_isotropicQuotientForm`, `sigNeg_isotropicQuotientForm`).

Not yet here: the identification of `e^⊥/⟨e⟩` with `W` and hence the induced form on the quotient.
What is proved is the splitting and the signature of `W` itself (`sigPos_restrict_planePerp`,
`sigNeg_restrict_planePerp`).

The proof splits off the hyperbolic plane. Nondegeneracy makes the functional `b(e, ·)` nonzero, so
there is `f` with `b(e, f) = 1`, and the plane `⟨e, f⟩` is a hyperbolic plane. Its orthogonal
complement `W` — Mathlib's `LinearMap.BilinForm.orthogonal` — is a complement, so
`Q ≅ ⟨e, f⟩ ⊥ Q|W` (`splittingIsometry`) and the signatures add (`QuadraticForm.sigPos` on a
product). The quotient `e^⊥/⟨e⟩` is linearly isomorphic to `W` (`perpQuotientEquiv`), and under that
isomorphism the induced form is `Q|W` (`isotropicQuotientForm_mk` records the characterizing property
that a class evaluates to the value of `Q` on any representative).

## References

* V. V. Nikulin, *Integral symmetric bilinear forms and some of their applications*, Izv. Akad.
  Nauk SSSR Ser. Mat. 43 (1979), §1.
* J.-P. Serre, *A Course in Arithmetic*, Ch. V.
-/

@[expose] public section

open QuadraticMap

namespace LeanCategories.Lattices.Valued

universe u

section Plane

variable {K : Type u} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- The pairing `x₀ y₁ + x₁ y₀` of the hyperbolic plane. -/
def hypPlaneBilin : LinearMap.BilinMap K (Fin 2 → K) K :=
  LinearMap.mk₂ K (fun x y => x 0 * y 1 + x 1 * y 0)
    (fun x₁ x₂ y => by simp [add_mul]; ring)
    (fun c x y => by simp [mul_add]; ring)
    (fun x y₁ y₂ => by simp [mul_add]; ring)
    (fun c x y => by simp; ring)

/-- The **hyperbolic plane form** `2 x₀ x₁` on `K²`. -/
noncomputable def hypPlaneForm : QuadraticForm K (Fin 2 → K) :=
  LinearMap.BilinMap.toQuadraticMap hypPlaneBilin

theorem hypPlaneForm_apply (a : Fin 2 → K) : hypPlaneForm a = 2 * a 0 * a 1 := by
  simp only [hypPlaneForm, LinearMap.BilinMap.toQuadraticMap_apply, hypPlaneBilin,
    LinearMap.mk₂_apply]
  ring

/-- A binary form whose value is `2 x₀ x₁` has exactly one positive square. -/
theorem sigPos_eq_one_of_hyperbolic (Q : QuadraticForm K (Fin 2 → K))
    (hval : ∀ a : Fin 2 → K, Q a = 2 * a 0 * a 1) : sigPos Q = 1 := by
  have hpos : 1 ≤ sigPos Q := by
    have hPD : (Q.restrict (Submodule.span K {![1, 1]} : Submodule K (Fin 2 → K))).PosDef := by
      intro v hv
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp v.2
      rw [QuadraticMap.restrict_apply, ← hc, QuadraticMap.map_smul, hval, smul_eq_mul]
      have hv' : c ≠ 0 := by
        intro h0
        exact hv (Subtype.ext (by rw [← hc, h0]; simp))
      have h1 : (![1, 1] : Fin 2 → K) 0 = 1 := rfl
      have h2 : (![1, 1] : Fin 2 → K) 1 = 1 := rfl
      rw [h1, h2]
      nlinarith [mul_self_pos.mpr hv']
    have hle := le_sigPos_of_posDef (Q := Q) hPD
    rw [show Module.finrank K (Submodule.span K {![1, 1]} : Submodule K (Fin 2 → K)) = 1 from by
      rw [finrank_span_singleton]
      simp] at hle
    simpa using hle
  have hle : sigPos Q ≤ 1 := by
    have h := QuadraticForm.sigPos_add_finrank_le_of_nonpos (Q := Q)
      (V := Submodule.span K {![1, 0]}) ?_
    · rw [show Module.finrank K (Submodule.span K {![1, 0]} : Submodule K (Fin 2 → K)) = 1 from by
        rw [finrank_span_singleton]; simp,
        Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at h
      simpa using h
    · intro x hx
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hx
      rw [← hc, QuadraticMap.map_smul, hval, smul_eq_mul]
      have h0 : (![1, 0] : Fin 2 → K) 1 = 0 := rfl
      rw [h0]
      nlinarith [sq_nonneg c]
  omega

/-- A binary form whose value is `2 x₀ x₁` has exactly one negative square. -/
theorem sigNeg_eq_one_of_hyperbolic (Q : QuadraticForm K (Fin 2 → K))
    (hval : ∀ a : Fin 2 → K, Q a = 2 * a 0 * a 1) : sigNeg Q = 1 := by
  have hpos : 1 ≤ sigNeg Q := by
    have hND : ((-Q).restrict (Submodule.span K {![1, -1]} : Submodule K (Fin 2 → K))).PosDef := by
      intro v hv
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp v.2
      rw [QuadraticMap.restrict_apply, ← hc, QuadraticMap.map_smul, QuadraticMap.neg_apply, hval,
        smul_eq_mul]
      have hv' : c ≠ 0 := by
        intro h0
        exact hv (Subtype.ext (by rw [← hc, h0]; simp))
      have h1 : (![1, -1] : Fin 2 → K) 0 = 1 := rfl
      have h2 : (![1, -1] : Fin 2 → K) 1 = -1 := rfl
      rw [h1, h2]
      nlinarith [mul_self_pos.mpr hv']
    have hle := le_sigNeg_of_negDef (Q := Q) hND
    rw [show Module.finrank K (Submodule.span K {![1, -1]} : Submodule K (Fin 2 → K)) = 1 from by
      rw [finrank_span_singleton]
      simp] at hle
    simpa using hle
  have hle : sigNeg Q ≤ 1 := by
    have h := QuadraticForm.sigPos_add_finrank_le_of_nonpos (Q := -Q)
      (V := Submodule.span K {![1, 0]}) ?_
    · rw [show Module.finrank K (Submodule.span K {![1, 0]} : Submodule K (Fin 2 → K)) = 1 from by
        rw [finrank_span_singleton]; simp,
        Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at h
      rw [sigPos_neg] at h
      omega
    · intro x hx
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hx
      rw [← hc, QuadraticMap.map_smul, QuadraticMap.neg_apply, hval, smul_eq_mul]
      have h0 : (![1, 0] : Fin 2 → K) 1 = 0 := rfl
      rw [h0]
      nlinarith [sq_nonneg c]
  omega

theorem sigPos_hypPlaneForm : sigPos (hypPlaneForm (K := K)) = 1 :=
  sigPos_eq_one_of_hyperbolic _ hypPlaneForm_apply

theorem sigNeg_hypPlaneForm : sigNeg (hypPlaneForm (K := K)) = 1 :=
  sigNeg_eq_one_of_hyperbolic _ hypPlaneForm_apply

end Plane

section Splitting

variable {K : Type u} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {V : Type u} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
variable [Invertible (2 : K)]
variable {Q : QuadraticForm K V}

/-- The self-pairing of the associated form is the form itself (Mathlib states this for
`associatedHom`). -/
theorem associated_self_apply' (Q : QuadraticForm K V) (x : V) : (associated Q) x x = Q x := by
  simpa [QuadraticMap.coe_associatedHom] using
    QuadraticMap.associated_eq_self_apply (S := K) (Q := Q) x

/-- The associated pairing of a quadratic form over a field is symmetric. -/
theorem associated_comm' (Q : QuadraticForm K V) (x y : V) :
    (associated Q) x y = (associated Q) y x :=
  LinearMap.IsSymm.eq (QuadraticForm.associated_isSymm (S := K) Q) x y

/-- The quadratic expansion of a two-term linear combination through the associated pairing. -/
theorem quadratic_expand' (Q : QuadraticForm K V) (a b : K) (x y : V) :
    Q (a • x + b • y) = a ^ 2 * Q x + 2 * a * b * (associated Q) x y + b ^ 2 * Q y := by
  conv_lhs => rw [← associated_self_apply' Q (a • x + b • y)]
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
    associated_self_apply', associated_comm' Q y x]
  ring

/-- The orthogonal complement of the plane spanned by `e` and `f`, as Mathlib's
`LinearMap.BilinForm.orthogonal`. -/
noncomputable def planePerp (Q : QuadraticForm K V) (e f : V) : Submodule K V :=
  LinearMap.BilinForm.orthogonal (associated Q) (Submodule.span K {e, f})

/-- Membership in the orthogonal complement of the plane, from Mathlib's `mem_orthogonal_iff`. -/
theorem mem_planePerp_iff {e f x : V} :
    x ∈ planePerp Q e f ↔ (associated Q) e x = 0 ∧ (associated Q) f x = 0 := by
  rw [planePerp, LinearMap.BilinForm.mem_orthogonal_iff]
  constructor
  · intro h
    exact ⟨h e (Submodule.subset_span (by simp)), h f (Submodule.subset_span (by simp))⟩
  · rintro ⟨h1, h2⟩ z hz
    obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp hz
    rw [map_add, map_smul, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
      LinearMap.smul_apply, smul_eq_mul, smul_eq_mul, h1, h2]
    ring

/-- The projection of a vector off the plane along the pairing. -/
noncomputable def planeProj (Q : QuadraticForm K V) (e f x : V) : V :=
  x - (associated Q) x f • e - (associated Q) x e • f

omit [FiniteDimensional K V] [LinearOrder K] [IsStrictOrderedRing K] in
theorem planeProj_associated_left (Q : QuadraticForm K V) (e f x : V) :
    (associated Q) e (planeProj Q e f x)
      = (associated Q) e x - (associated Q) x f * (associated Q) e e
        - (associated Q) x e * (associated Q) e f := by
  simp only [planeProj, map_sub, map_smul, smul_eq_mul]

omit [FiniteDimensional K V] [LinearOrder K] [IsStrictOrderedRing K] in
theorem planeProj_associated_right (Q : QuadraticForm K V) (e f x : V) :
    (associated Q) f (planeProj Q e f x)
      = (associated Q) f x - (associated Q) x f * (associated Q) f e
        - (associated Q) x e * (associated Q) f f := by
  simp only [planeProj, map_sub, map_smul, smul_eq_mul]

theorem planeProj_mem (Q : QuadraticForm K V) {e f : V} (he : Q e = 0) (hf : Q f = 0)
    (hB : (associated Q) e f = 1) (x : V) : planeProj Q e f x ∈ planePerp Q e f := by
  rw [mem_planePerp_iff]
  have hee : (associated Q) e e = 0 := by rw [associated_self_apply']; exact he
  have hff : (associated Q) f f = 0 := by rw [associated_self_apply']; exact hf
  have hfe : (associated Q) f e = 1 := by rw [associated_comm']; exact hB
  constructor
  · rw [planeProj_associated_left, hee, hB, associated_comm' Q e x]
    ring
  · rw [planeProj_associated_right, hff, hfe, associated_comm' Q f x]
    ring

omit [FiniteDimensional K V] in
theorem planeProj_add (Q : QuadraticForm K V) (e f x y : V) :
    planeProj Q e f (x + y) = planeProj Q e f x + planeProj Q e f y := by
  simp only [planeProj, map_add, LinearMap.add_apply, add_smul]
  abel

omit [FiniteDimensional K V] in
theorem planeProj_smul (Q : QuadraticForm K V) (e f : V) (c : K) (x : V) :
    planeProj Q e f (c • x) = c • planeProj Q e f x := by
  simp only [planeProj, map_smul, LinearMap.smul_apply, smul_eq_mul, mul_smul]
  module

omit [FiniteDimensional K V] in
theorem planeProj_sum (Q : QuadraticForm K V) (e f x : V) :
    planeProj Q e f x + (associated Q) x f • e + (associated Q) x e • f = x := by
  simp only [planeProj]
  abel

/-- **The splitting identity**: the value of `Q` is the hyperbolic-plane part plus the value on the
projection. -/
theorem quadratic_eq_plane_add_proj (Q : QuadraticForm K V) {e f : V} (he : Q e = 0) (hf : Q f = 0)
    (hB : (associated Q) e f = 1) (x : V) :
    Q x = 2 * ((associated Q) x f * (associated Q) x e) + Q (planeProj Q e f x) := by
  obtain ⟨h1, h2⟩ := mem_planePerp_iff.mp (planeProj_mem Q he hf hB x)
  set w := planeProj Q e f x with hw
  set α := (associated Q) x f with hα
  set β := (associated Q) x e with hβ
  have hx : w + α • e + β • f = x := planeProj_sum Q e f x
  have hwe : (associated Q) e w = 0 := h1
  have hwf : (associated Q) f w = 0 := h2
  have hee : (associated Q) e e = 0 := by rw [associated_self_apply']; exact he
  have hff : (associated Q) f f = 0 := by rw [associated_self_apply']; exact hf
  have hfe : (associated Q) f e = 1 := by rw [associated_comm']; exact hB
  conv_lhs => rw [← hx, ← associated_self_apply' Q (w + α • e + β • f)]
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
    associated_self_apply', associated_comm' Q w e, associated_comm' Q w f, hwe, hwf,
    hee, hff, hfe, hB]
  ring

omit [Invertible (2 : K)] in
theorem vecCons_zero (a b : K) : (![a, b] : Fin 2 → K) 0 = a := rfl

omit [Invertible (2 : K)] in
theorem vecCons_one (a b : K) : (![a, b] : Fin 2 → K) 1 = b := rfl

/-- The linear equivalence underlying the splitting. -/
noncomputable def splittingLinearEquiv (Q : QuadraticForm K V) {e f : V} (he : Q e = 0)
    (hf : Q f = 0) (hB : (associated Q) e f = 1) :
    V ≃ₗ[K] ((Fin 2 → K) × ↥(planePerp Q e f)) where
  toFun x := (![(associated Q) x f, (associated Q) x e],
    ⟨planeProj Q e f x, planeProj_mem Q he hf hB x⟩)
  invFun p := p.1 0 • e + p.1 1 • f + ((p.2 : V))
  left_inv x := by
    have h := planeProj_sum Q e f x
    calc (associated Q) x f • e + (associated Q) x e • f + planeProj Q e f x
        = planeProj Q e f x + (associated Q) x f • e + (associated Q) x e • f := by abel
      _ = x := h
  right_inv p := by
    obtain ⟨v, w⟩ := p
    have hwe : (associated Q) e (w : V) = 0 := (mem_planePerp_iff.mp w.2).1
    have hwf : (associated Q) f (w : V) = 0 := (mem_planePerp_iff.mp w.2).2
    have hee : (associated Q) e e = 0 := by rw [associated_self_apply']; exact he
    have hff : (associated Q) f f = 0 := by rw [associated_self_apply']; exact hf
    have hfe : (associated Q) f e = 1 := by rw [associated_comm']; exact hB
    have h1 : (associated Q) (v 0 • e + v 1 • f + (w : V)) f = v 0 := by
      simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
        associated_comm' Q w f, hwf, hff, hB]
      ring
    have h2 : (associated Q) (v 0 • e + v 1 • f + (w : V)) e = v 1 := by
      simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
        associated_comm' Q w e, hwe, hee, hfe]
      ring
    have hproj : planeProj Q e f (v 0 • e + v 1 • f + (w : V)) = (w : V) := by
      simp only [planeProj, h1, h2]
      abel
    refine Prod.ext ?_ ?_
    · funext i
      fin_cases i
      · simpa using h1
      · simpa using h2
    · exact Subtype.ext hproj
  map_add' x y := by
    refine Prod.ext ?_ ?_
    · funext i
      fin_cases i <;> simp
    · exact Subtype.ext (planeProj_add Q e f x y)
  map_smul' c x := by
    refine Prod.ext ?_ ?_
    · funext i
      fin_cases i <;> simp
    · exact Subtype.ext (planeProj_smul Q e f c x)

/-- **The splitting isometry**: `Q` is the orthogonal sum of the hyperbolic plane `⟨e, f⟩` and the
orthogonal complement of that plane. -/
noncomputable def splittingIsometry (Q : QuadraticForm K V) {e f : V} (he : Q e = 0) (hf : Q f = 0)
    (hB : (associated Q) e f = 1) :
    Q.IsometryEquiv (QuadraticMap.prod (hypPlaneForm (K := K))
      (QuadraticMap.restrict Q (planePerp Q e f))) where
  toLinearEquiv := splittingLinearEquiv Q he hf hB
  map_app' := by
    intro x
    have h := quadratic_eq_plane_add_proj Q he hf hB x
    rw [QuadraticMap.prod_apply, hypPlaneForm_apply, QuadraticMap.restrict_apply]
    simp only [splittingLinearEquiv, vecCons_zero, vecCons_one]
    rw [h]
    ring

/-- **The signature of the orthogonal complement** of the hyperbolic plane: the negative index part
is unchanged. -/
theorem sigNeg_restrict_planePerp (Q : QuadraticForm K V) {e f : V} (he : Q e = 0) (hf : Q f = 0)
    (hB : (associated Q) e f = 1) :
    sigNeg (QuadraticMap.restrict Q (planePerp Q e f)) + 1 = sigNeg Q := by
  have h1 : sigNeg (QuadraticMap.prod (hypPlaneForm (K := K))
        (QuadraticMap.restrict Q (planePerp Q e f)))
      = sigNeg (hypPlaneForm (K := K))
        + sigNeg (QuadraticMap.restrict Q (planePerp Q e f)) :=
    congrArg (fun t : ℕ × ℕ × ℕ => t.2.1)
      (quadraticSignature_prod K (hypPlaneForm (K := K))
        (QuadraticMap.restrict Q (planePerp Q e f)))
  rw [sigNeg_hypPlaneForm] at h1
  have heq : QuadraticMap.Equivalent Q
      (QuadraticMap.prod (hypPlaneForm (K := K))
        (QuadraticMap.restrict Q (planePerp Q e f))) :=
    ⟨splittingIsometry Q he hf hB⟩
  rw [heq.sigNeg_eq, h1]
  omega

/-- **The signature of the orthogonal complement** of the hyperbolic plane: the positive index part
drops by one. -/
theorem sigPos_restrict_planePerp (Q : QuadraticForm K V) {e f : V} (he : Q e = 0) (hf : Q f = 0)
    (hB : (associated Q) e f = 1) :
    sigPos (QuadraticMap.restrict Q (planePerp Q e f)) + 1 = sigPos Q := by
  have h1 : sigPos (QuadraticMap.prod (hypPlaneForm (K := K))
        (QuadraticMap.restrict Q (planePerp Q e f)))
      = sigPos (hypPlaneForm (K := K))
        + sigPos (QuadraticMap.restrict Q (planePerp Q e f)) :=
    congrArg (fun t : ℕ × ℕ × ℕ => t.1)
      (quadraticSignature_prod K (hypPlaneForm (K := K))
        (QuadraticMap.restrict Q (planePerp Q e f)))
  rw [sigPos_hypPlaneForm] at h1
  have heq : QuadraticMap.Equivalent Q
      (QuadraticMap.prod (hypPlaneForm (K := K))
        (QuadraticMap.restrict Q (planePerp Q e f))) :=
    ⟨splittingIsometry Q he hf hB⟩
  rw [heq.sigPos_eq, h1]
  omega

end Splitting

end LeanCategories.Lattices.Valued
