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
# The signature of `e^⊥/⟨e⟩` is `(p − 1, q − 1)`

Let `K` be an ordered field in which `2` is invertible, `Q` a nondegenerate quadratic form on a
finite-dimensional `K`-space `V` of signature `(p, q)`, and `e ≠ 0` an isotropic vector. Then the
form induced on `e^⊥/⟨e⟩` has signature `(p − 1, q − 1)`:
`exists_isotropicQuotientForm_signature` produces the hyperbolic partner `f` and states both indices
as `sigPos Q - 1` and `sigNeg Q - 1`.

The proof splits off the hyperbolic plane. Nondegeneracy makes the functional `b(e, ·)` nonzero, so
there is `f` with `b(e, f) = 1`; scaling it makes `f` isotropic too (`exists_hyperbolicPartner`),
and the plane `⟨e, f⟩` is then a hyperbolic plane. Its orthogonal complement `W` — Mathlib's
`LinearMap.BilinForm.orthogonal` — is a complement, so `Q ≅ ⟨e, f⟩ ⊥ Q|W` (`splittingIsometry`) and
the signatures add (`QuadraticMap.sigPos` on a product), which is `sigPos_restrict_planePerp` and
`sigNeg_restrict_planePerp` for `W`.

Inside `e^⊥` — the orthogonal complement `linePerp Q e` of the line `⟨e⟩` — the line `⟨e⟩`
(`lineInPerp`) and `W ∩ e^⊥` are complements (`isCompl_lineInPerp_planeInPerp`). The second is `W`
itself, since `W ≤ e^⊥` (`planePerp_le_linePerp`); the intersection is zero because a multiple of
`e` orthogonal to `f` is zero, and every `x ∈ e^⊥` is its projection to `W` plus its `e`-component.
Mathlib's `Submodule.quotientEquivOfIsCompl` then gives `e^⊥/⟨e⟩ ≃ₗ W` (`perpQuotientEquiv`), with
no quotient induction and no hand-built inverse laws, and `isotropicQuotientForm` is `Q|W`
transported along it (`isotropicQuotientIsometryEquiv` exhibits the isometry).

The symmetric-bilinear API is Mathlib's throughout: `QuadraticMap.associated_eq_self_apply` and
`QuadraticMap.associated_isSymm` are used at each call site rather than restated locally.

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
  have hfe : (associated Q) f e = 1 := by
    rw [QuadraticMap.associated_isSymm K (Q := Q) f e]
    exact hB
  have hex : (associated Q) e x = (associated Q) x e :=
    QuadraticMap.associated_isSymm K (Q := Q) e x
  have hfx : (associated Q) f x = (associated Q) x f :=
    QuadraticMap.associated_isSymm K (Q := Q) f x
  constructor
  · rw [planeProj_associated_left, QuadraticMap.associated_eq_self_apply, he, hB, hex]
    ring
  · rw [planeProj_associated_right, QuadraticMap.associated_eq_self_apply, hf, hfe, hfx]
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
  have hwe' : (associated Q) w e = 0 := by
    rw [QuadraticMap.associated_isSymm K (Q := Q) w e]
    exact hwe
  have hwf' : (associated Q) w f = 0 := by
    rw [QuadraticMap.associated_isSymm K (Q := Q) w f]
    exact hwf
  have hfe : (associated Q) f e = 1 := by
    rw [QuadraticMap.associated_isSymm K (Q := Q) f e]
    exact hB
  conv_lhs => rw [← hx, ← QuadraticMap.associated_eq_self_apply K (Q := Q) (w + α • e + β • f)]
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
    QuadraticMap.associated_eq_self_apply K, he, hf, hwe, hwf, hwe', hwf', hfe, hB]
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
    have hwe' : (associated Q) (w : V) e = 0 := by
      rw [QuadraticMap.associated_isSymm K (Q := Q) (w : V) e]
      exact hwe
    have hwf' : (associated Q) w f = 0 := by
      rw [QuadraticMap.associated_isSymm K (Q := Q) (w : V) f]
      exact hwf
    have hfe : (associated Q) f e = 1 := by
      rw [QuadraticMap.associated_isSymm K (Q := Q) f e]
      exact hB
    have h1 : (associated Q) (v 0 • e + v 1 • f + (w : V)) f = v 0 := by
      simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
        QuadraticMap.associated_eq_self_apply K, hwf', hf, hB]
      ring
    have h2 : (associated Q) (v 0 • e + v 1 • f + (w : V)) e = v 1 := by
      simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
        QuadraticMap.associated_eq_self_apply K, hwe', he, hfe]
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

section Quotient

variable {K : Type u} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {V : Type u} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
variable [Invertible (2 : K)]
variable {Q : QuadraticForm K V}

omit [LinearOrder K] [IsStrictOrderedRing K] [FiniteDimensional K V] in
/-- The orthogonal complement `e^⊥` of the line spanned by `e`. -/
noncomputable def linePerp (Q : QuadraticForm K V) (e : V) : Submodule K V :=
  LinearMap.BilinForm.orthogonal (associated Q) (Submodule.span K {e})

omit [LinearOrder K] [IsStrictOrderedRing K] [FiniteDimensional K V] in
/-- Membership in `e^⊥`: a vector is orthogonal to `e`. -/
theorem mem_linePerp_iff {Q : QuadraticForm K V} {e x : V} :
    x ∈ linePerp Q e ↔ (associated Q) e x = 0 := by
  rw [linePerp, LinearMap.BilinForm.mem_orthogonal_iff]
  refine ⟨fun h => h e (Submodule.mem_span_singleton_self e), ?_⟩
  rintro h z hz
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hz
  simp [h]

omit [LinearOrder K] [IsStrictOrderedRing K] [FiniteDimensional K V] in
/-- An isotropic vector lies in its own orthogonal complement. -/
theorem mem_linePerp_self {Q : QuadraticForm K V} {e : V} (he : Q e = 0) : e ∈ linePerp Q e := by
  rw [mem_linePerp_iff, QuadraticMap.associated_eq_self_apply]
  exact he

/-- The complement `W = ⟨e, f⟩^⊥` of the hyperbolic plane lies in `e^⊥`, so inside `e^⊥` the
submodule `W ∩ e^⊥` is `W` itself. -/
theorem planePerp_le_linePerp (Q : QuadraticForm K V) (e f : V) :
    planePerp Q e f ≤ linePerp Q e := by
  intro x hx
  rw [mem_linePerp_iff]
  exact (mem_planePerp_iff.mp hx).1

omit [LinearOrder K] [IsStrictOrderedRing K] [FiniteDimensional K V] in
/-- The line `⟨e⟩`, as a submodule of `e^⊥`. -/
noncomputable def lineInPerp (Q : QuadraticForm K V) {e : V} (he : Q e = 0) :
    Submodule K ↥(linePerp Q e) :=
  Submodule.span K {⟨e, mem_linePerp_self he⟩}

/-- The submodule `W ∩ e^⊥` of `e^⊥`, which is `W` by `planePerp_le_linePerp`. -/
noncomputable def planeInPerp (Q : QuadraticForm K V) (e f : V) :
    Submodule K ↥(linePerp Q e) :=
  Submodule.comap (linePerp Q e).subtype (planePerp Q e f)

/-- Inside `e^⊥`, the line `⟨e⟩` and `W ∩ e^⊥` are disjoint: a multiple of `e` orthogonal to `f`
is zero, because `b(e, f) = 1`. -/
theorem disjoint_lineInPerp_planeInPerp (Q : QuadraticForm K V) {e f : V} (he : Q e = 0)
    (hB : (associated Q) e f = 1) :
    Disjoint (lineInPerp Q he) (planeInPerp Q e f) := by
  rw [Submodule.disjoint_def]
  rintro ⟨x, hx⟩ hxp hxq
  rw [planeInPerp, Submodule.mem_comap] at hxq
  rw [lineInPerp] at hxp
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hxp
  have hxa : a • e = x := by simpa using congrArg Subtype.val ha
  have hfe : (associated Q) f e = 1 := by
    rw [QuadraticMap.associated_isSymm K (Q := Q) f e]
    exact hB
  have hfx : (associated Q) f x = 0 := (mem_planePerp_iff.mp hxq).2
  rw [← hxa, map_smul, smul_eq_mul, hfe, mul_one] at hfx
  have hx0 : x = 0 := by rw [← hxa, hfx, zero_smul]
  exact Subtype.ext hx0

/-- Inside `e^⊥`, the line `⟨e⟩` and `W ∩ e^⊥` span everything: `x` is its projection to `W` plus
its `e`-component. -/
theorem codisjoint_lineInPerp_planeInPerp (Q : QuadraticForm K V) {e f : V} (he : Q e = 0)
    (hf : Q f = 0) (hB : (associated Q) e f = 1) :
    Codisjoint (lineInPerp Q he) (planeInPerp Q e f) := by
  rw [codisjoint_iff, Submodule.eq_top_iff']
  rintro ⟨x, hx⟩
  have hex : (associated Q) e x = 0 := mem_linePerp_iff.mp hx
  have hxe : (associated Q) x e = 0 := by
    rw [QuadraticMap.associated_isSymm K (Q := Q) x e]
    exact hex
  have hsum : planeProj Q e f x + (associated Q) x f • e = x := by
    have h := planeProj_sum Q e f x
    rw [hxe, zero_smul, add_zero] at h
    exact h
  have hproj : planeProj Q e f x = x - (associated Q) x f • e := by
    rw [eq_sub_iff_add_eq]
    exact hsum
  have hwp : planeProj Q e f x ∈ linePerp Q e := by
    rw [hproj]
    exact (linePerp Q e).sub_mem hx ((linePerp Q e).smul_mem _ (mem_linePerp_self he))
  refine Submodule.mem_sup.mpr
    ⟨(associated Q) x f • (⟨e, mem_linePerp_self he⟩ : ↥(linePerp Q e)), ?_,
      ⟨planeProj Q e f x, hwp⟩, ?_, ?_⟩
  · change (associated Q) x f • (⟨e, mem_linePerp_self he⟩ : ↥(linePerp Q e))
      ∈ Submodule.span K {(⟨e, mem_linePerp_self he⟩ : ↥(linePerp Q e))}
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  · change (linePerp Q e).subtype ⟨planeProj Q e f x, hwp⟩ ∈ planePerp Q e f
    exact planeProj_mem Q he hf hB x
  · exact Subtype.ext (by rw [add_comm]; exact hsum)

/-- **The complement statement of the issue**: inside `e^⊥`, the line `⟨e⟩` and the complement
`W ∩ e^⊥` of the hyperbolic plane are complementary. -/
theorem isCompl_lineInPerp_planeInPerp (Q : QuadraticForm K V) {e f : V} (he : Q e = 0)
    (hf : Q f = 0) (hB : (associated Q) e f = 1) :
    IsCompl (lineInPerp Q he) (planeInPerp Q e f) :=
  ⟨disjoint_lineInPerp_planeInPerp Q he hB, codisjoint_lineInPerp_planeInPerp Q he hf hB⟩

/-- **The quotient `e^⊥/⟨e⟩` is `W`**: Mathlib's linear equivalence out of a quotient by a
complement, with no quotient induction and no hand-built inverse laws, followed by the identity
between `W ∩ e^⊥` and `W`. -/
noncomputable def perpQuotientEquiv (Q : QuadraticForm K V) {e f : V} (he : Q e = 0)
    (hf : Q f = 0) (hB : (associated Q) e f = 1) :
    (↥(linePerp Q e) ⧸ lineInPerp Q he) ≃ₗ[K] ↥(planePerp Q e f) :=
  (Submodule.quotientEquivOfIsCompl (lineInPerp Q he) (planeInPerp Q e f)
      (isCompl_lineInPerp_planeInPerp Q he hf hB)).trans
    (Submodule.comapSubtypeEquivOfLe (planePerp_le_linePerp Q e f))

/-- **The form induced on `e^⊥/⟨e⟩`**: the restriction of `Q` to `W`, transported along the linear
equivalence `e^⊥/⟨e⟩ ≃ W`. -/
noncomputable def isotropicQuotientForm (Q : QuadraticForm K V) {e f : V} (he : Q e = 0)
    (hf : Q f = 0) (hB : (associated Q) e f = 1) :
    QuadraticForm K (↥(linePerp Q e) ⧸ lineInPerp Q he) :=
  (QuadraticMap.restrict Q (planePerp Q e f)).comp (perpQuotientEquiv Q he hf hB).toLinearMap

/-- The induced form on `e^⊥/⟨e⟩` is isometric to `Q|W`, by construction of `perpQuotientEquiv`. -/
noncomputable def isotropicQuotientIsometryEquiv (Q : QuadraticForm K V) {e f : V} (he : Q e = 0)
    (hf : Q f = 0) (hB : (associated Q) e f = 1) :
    QuadraticMap.IsometryEquiv (isotropicQuotientForm Q he hf hB)
      (QuadraticMap.restrict Q (planePerp Q e f)) where
  toLinearEquiv := perpQuotientEquiv Q he hf hB
  map_app' := by
    intro x
    simp [isotropicQuotientForm]

/-- The induced form on `e^⊥/⟨e⟩` is equivalent to `Q|W`. -/
theorem equivalent_isotropicQuotientForm (Q : QuadraticForm K V) {e f : V} (he : Q e = 0)
    (hf : Q f = 0) (hB : (associated Q) e f = 1) :
    QuadraticMap.Equivalent (isotropicQuotientForm Q he hf hB)
      (QuadraticMap.restrict Q (planePerp Q e f)) :=
  ⟨isotropicQuotientIsometryEquiv Q he hf hB⟩

/-- **The positive index of the induced form** is that of `Q` minus one. -/
theorem sigPos_isotropicQuotientForm (Q : QuadraticForm K V) {e f : V} (he : Q e = 0)
    (hf : Q f = 0) (hB : (associated Q) e f = 1) :
    sigPos (isotropicQuotientForm Q he hf hB) + 1 = sigPos Q := by
  rw [(equivalent_isotropicQuotientForm Q he hf hB).sigPos_eq]
  exact sigPos_restrict_planePerp Q he hf hB

/-- **The negative index of the induced form** is that of `Q` minus one. -/
theorem sigNeg_isotropicQuotientForm (Q : QuadraticForm K V) {e f : V} (he : Q e = 0)
    (hf : Q f = 0) (hB : (associated Q) e f = 1) :
    sigNeg (isotropicQuotientForm Q he hf hB) + 1 = sigNeg Q := by
  rw [(equivalent_isotropicQuotientForm Q he hf hB).sigNeg_eq]
  exact sigNeg_restrict_planePerp Q he hf hB

omit [LinearOrder K] [IsStrictOrderedRing K] [FiniteDimensional K V] in
/-- `Q` is constant along the isotropic line `⟨e⟩` inside `e^⊥`: translating by a multiple of the
isotropic `e` does not change the value of `Q`. This is the well-definedness of the induced form on
`e^⊥/⟨e⟩` at the level of representatives. -/
theorem quadratic_add_smul_eq_of_mem_linePerp (Q : QuadraticForm K V) {e x : V} (he : Q e = 0)
    (hx : x ∈ linePerp Q e) (c : K) : Q (x + c • e) = Q x := by
  have hex : (associated Q) e x = 0 := mem_linePerp_iff.mp hx
  have hxe : (associated Q) x e = 0 := by
    rw [QuadraticMap.associated_isSymm K (Q := Q) x e]
    exact hex
  have hee : (associated Q) e e = 0 := by
    rw [QuadraticMap.associated_eq_self_apply]
    exact he
  rw [← QuadraticMap.associated_eq_self_apply K (Q := Q) (x + c • e),
    ← QuadraticMap.associated_eq_self_apply K (Q := Q) x]
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
    QuadraticMap.associated_eq_self_apply K, hex, hxe, he, mul_zero, add_zero]

/-- **The induction formula for `isotropicQuotientForm`**: the induced form on `e^⊥/⟨e⟩` evaluates
on the class of a vector of `e^⊥` to the value of `Q` on that vector. -/
theorem isotropicQuotientForm_mk (Q : QuadraticForm K V) {e f : V} (he : Q e = 0)
    (hf : Q f = 0) (hB : (associated Q) e f = 1) (x : ↥(linePerp Q e)) :
    isotropicQuotientForm Q he hf hB (Submodule.Quotient.mk x) = Q (x : V) := by
  classical
  set u : ↥(planeInPerp Q e f) :=
    (Submodule.quotientEquivOfIsCompl (lineInPerp Q he) (planeInPerp Q e f)
      (isCompl_lineInPerp_planeInPerp Q he hf hB)) (Submodule.Quotient.mk x) with hu
  have hclass : (Submodule.Quotient.mk (u : ↥(linePerp Q e)) :
      ↥(linePerp Q e) ⧸ lineInPerp Q he) = Submodule.Quotient.mk x := by
    rw [hu]
    exact Submodule.mk_quotientEquivOfIsCompl_apply _ _
  have hmem : (u : ↥(linePerp Q e)) - x ∈ lineInPerp Q he :=
    (Submodule.Quotient.eq (lineInPerp Q he)).mp hclass
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
  have hcV : (u : V) = (x : V) + c • e := by
    have h : c • e = (u : V) - (x : V) := by
      have h' := congrArg (fun z : ↥(linePerp Q e) => (z : V)) hc
      simpa using h'
    rw [h]
    abel
  have hform : isotropicQuotientForm Q he hf hB (Submodule.Quotient.mk x) =
      Q ((perpQuotientEquiv Q he hf hB (Submodule.Quotient.mk x) : ↥(planePerp Q e f)) : V) := by
    simp [isotropicQuotientForm]
  have hy : ((perpQuotientEquiv Q he hf hB (Submodule.Quotient.mk x) : ↥(planePerp Q e f)) : V)
      = (u : V) := rfl
  rw [hform, hy, hcV]
  exact quadratic_add_smul_eq_of_mem_linePerp Q he x.2 c

omit [LinearOrder K] [IsStrictOrderedRing K] [FiniteDimensional K V] in
/-- The value of `Q` at `g + t • e` for an isotropic `e` with `b(e, g) = 1`: the plane part of the
hyperbolic splitting. -/
theorem quadratic_add_smul_eq (Q : QuadraticForm K V) {e g : V} (he : Q e = 0)
    (hB : (associated Q) e g = 1) (t : K) : Q (g + t • e) = Q g + 2 * t := by
  have hge : (associated Q) g e = 1 := by
    rw [QuadraticMap.associated_isSymm K (Q := Q) g e]
    exact hB
  rw [← QuadraticMap.associated_eq_self_apply K (Q := Q) (g + t • e)]
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
    QuadraticMap.associated_eq_self_apply K, he, hB, hge, mul_one, mul_zero, add_zero]
  ring

omit [FiniteDimensional K V] in
/-- **Nondegeneracy produces the hyperbolic partner**: an isotropic vector `e ≠ 0` has a partner
`f` that is isotropic and paired `1` with `e`. -/
theorem exists_hyperbolicPartner (Q : QuadraticForm K V) (hnd : (associated Q).Nondegenerate)
    {e : V} (he : Q e = 0) (hne : e ≠ 0) :
    ∃ f : V, Q f = 0 ∧ (associated Q) e f = 1 := by
  have hex : ∃ y : V, (associated Q) e y ≠ 0 := by
    by_contra h
    push Not at h
    exact hne (hnd.1 e h)
  obtain ⟨y, hy⟩ := hex
  set g : V := ((associated Q) e y)⁻¹ • y with hg
  have hB : (associated Q) e g = 1 := by
    rw [hg, map_smul, smul_eq_mul, inv_mul_cancel₀ hy]
  refine ⟨g - (2⁻¹ * Q g) • e, ?_, ?_⟩
  · have hexp := quadratic_add_smul_eq Q he hB (-(2⁻¹ * Q g))
    rw [show g - (2⁻¹ * Q g) • e = g + (-(2⁻¹ * Q g)) • e from by
      rw [sub_eq_add_neg, neg_smul], hexp]
    have h2 : 2 * (-(2⁻¹ * Q g)) = -(Q g) := by
      rw [mul_neg, ← mul_assoc, mul_inv_cancel₀ two_ne_zero, one_mul]
    rw [h2]
    ring
  · have hee : (associated Q) e e = 0 := by
      rw [QuadraticMap.associated_eq_self_apply]
      exact he
    simp [sub_eq_add_neg, hee, hB]

/-- **The signature of `e^⊥/⟨e⟩`**: for a nondegenerate form `Q` over an ordered field and an
isotropic `e ≠ 0`, the form induced on `e^⊥/⟨e⟩` has signature
`(sigPos Q - 1, sigNeg Q - 1)`. The partner `f` is produced by nondegeneracy. -/
theorem exists_isotropicQuotientForm_signature (Q : QuadraticForm K V)
    (hnd : (associated Q).Nondegenerate) {e : V} (he : Q e = 0) (hne : e ≠ 0) :
    ∃ (f : V) (hf : Q f = 0) (hB : (associated Q) e f = 1),
      sigPos (isotropicQuotientForm Q he hf hB) = sigPos Q - 1 ∧
        sigNeg (isotropicQuotientForm Q he hf hB) = sigNeg Q - 1 := by
  obtain ⟨f, hf, hB⟩ := exists_hyperbolicPartner Q hnd he hne
  refine ⟨f, hf, hB, ?_, ?_⟩
  · have h := sigPos_isotropicQuotientForm Q he hf hB
    omega
  · have h := sigNeg_isotropicQuotientForm Q he hf hB
    omega

end Quotient

end LeanCategories.Lattices.Valued
