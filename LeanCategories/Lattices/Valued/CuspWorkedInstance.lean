/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Lattices.Valued.CuspIsotropic
public import LeanCategories.Lattices.Valued.CuspVector
public import LeanCategories.Lattices.Valued.CuspHomFibre
public import LeanCategories.Lattices.Valued.Standard

/-!
# The worked cusp instance: `L = U ⊕ U` has one 0-cusp (#113)

The issue's worked instance: for the orthogonal sum of two hyperbolic planes with `Γ = O(L)`,
the primitive isotropic lines form a single orbit. The lattice is presented on `Fin 4 → ℤ` in
split coordinates `e = (x₀, x₂)`, `f = (x₁, x₃)` with pairing
`x · y = eₓ • f_y + fₓ • e_y`, whose Gram matrix at the standard basis is block-diagonal in two
copies of `hyperbolicPlaneGramMatrix`.

Since the discriminant group of a unimodular lattice is trivial, `ker ρ = O(L)` and the issue's
`Γ = O(L)` is the fibre theorem's own `Γ`. Transitivity of `O(L)` on primitive isotropic lines is
proved with elementary split-coordinate isometries — the two shears, the `E`/`F` swap, negation
and the `GL₂(ℤ)` action — and a Euclidean descent on the coprime pair of coordinates of the
normal form `(d, 0, 0, ν)`. The orbit count itself then comes from
`cuspOrbitsStableEquivStabilizer`:
every orbit lies in the fibre, and the fibre is the quotient of a stabilizer in the trivial range,
a point.
-/

@[expose] public section

open LeanCategories.Modules.Bilinear.Valued
open LeanCategories.Modules.Quadratic.Valued

namespace LeanCategories.Lattices.Valued

/-! ## The lattice -/

/-- The bilinear map of `U ⊕ U` in split coordinates: `x · y = eₓ • f_y + fₓ • e_y`. -/
def twoHyperbolicPlanesBilinMap : LinearMap.BilinMap ℤ (Fin 4 → ℤ) ℤ :=
  LinearMap.mk₂ ℤ
    (fun x y => x 0 * y 1 + x 1 * y 0 + x 2 * y 3 + x 3 * y 2)
    (fun _ _ _ => by intros; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring)
    (fun _ _ _ => by intros; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring)
    (fun _ _ _ => by intros; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring)
    (fun _ _ _ => by intros; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring)

/-- `U ⊕ U` presented on `Fin 4 → ℤ`: two hyperbolic planes in split coordinates. -/
def twoHyperbolicPlanes : IntegralLatticeCat ℤ :=
  ⟨BilinModuleCat.ofBilinMap twoHyperbolicPlanesBilinMap, by
    change Module.Projective ℤ (Fin 4 → ℤ)
    infer_instance, by
    intro x y
    show x 0 * y 1 + x 1 * y 0 + x 2 * y 3 + x 3 * y 2 =
      y 0 * x 1 + y 1 * x 0 + y 2 * x 3 + y 3 * x 2
    ring⟩

/-- The carrier of `U ⊕ U` is `ℤ⁴`, hence torsion-free: what makes the line of a vector primitive
and the generators of a line differ by units. -/
instance twoHyperbolicPlanesCarrierTorsionFree :
    NoZeroSMulDivisors ℤ ↥twoHyperbolicPlanes.obj.carrier :=
  inferInstanceAs (NoZeroSMulDivisors ℤ (Fin 4 → ℤ))
attribute [local instance 10000] twoHyperbolicPlanesCarrierTorsionFree

/-- The pairing is the split-coordinate dot product plus its flip. -/
theorem twoHyperbolicPlanes_pairing (x y : Fin 4 → ℤ) :
    twoHyperbolicPlanes.obj.pairing x y =
      x 0 * y 1 + x 1 * y 0 + x 2 * y 3 + x 3 * y 2 := rfl

/-- The standard vector: a primitive isotropic generator of the standard line. -/
def standardVector : Fin 4 → ℤ := ![1, 0, 0, 0]

/-- Polarization: a linear equivalence preserving every self-pairing preserves the pairing. -/
theorem pairing_of_self (x' : (Fin 4 → ℤ) ≃ₗ[ℤ] (Fin 4 → ℤ))
    (h : ∀ x : Fin 4 → ℤ,
      twoHyperbolicPlanes.obj.pairing (x' x) (x' x) =
        twoHyperbolicPlanes.obj.pairing x x)
    (x y : Fin 4 → ℤ) :
    twoHyperbolicPlanes.obj.pairing (x' x) (x' y) =
      twoHyperbolicPlanes.obj.pairing x y := by
  have qeq : ∀ z : Fin 4 → ℤ,
      x' z 0 * x' z 1 + x' z 2 * x' z 3 = z 0 * z 1 + z 2 * z 3 := by
    intro z
    have hz := h z
    rw [twoHyperbolicPlanes_pairing, twoHyperbolicPlanes_pairing] at hz
    linarith
  have h1 := qeq (x + y)
  have h2 := qeq x
  have h3 := qeq y
  simp only [map_add, Pi.add_apply] at h1
  rw [twoHyperbolicPlanes_pairing, twoHyperbolicPlanes_pairing]
  linear_combination h1 - h2 - h3

/-! ## The elementary isometries -/

/-- The shear on the `F`-coordinates: `f ↦ f + n • Rot e`, where `Rot (a, b) = (b, -a)`. -/
def hyperbolicShearF (n : ℤ) : (Fin 4 → ℤ) ≃ₗ[ℤ] (Fin 4 → ℤ) :=
  { toFun := fun x => ![x 0, x 1 + n * x 2, x 2, x 3 - n * x 0]
    invFun := fun x => ![x 0, x 1 - n * x 2, x 2, x 3 + n * x 0]
    left_inv := by
      intro x; funext i; fin_cases i <;> simp <;> ring
    right_inv := by
      intro x; funext i; fin_cases i <;> simp <;> ring
    map_add' := by
      intro x y; funext i; fin_cases i <;> simp <;> ring
    map_smul' := by
      intro r x; funext i; fin_cases i <;> simp <;> ring }

@[simp] theorem hyperbolicShearF_apply (n : ℤ) (x : Fin 4 → ℤ) :
    hyperbolicShearF n x = ![x 0, x 1 + n * x 2, x 2, x 3 - n * x 0] := rfl

@[simp] theorem hyperbolicShearF_zero (n : ℤ) (x : Fin 4 → ℤ) :
    hyperbolicShearF n x 0 = x 0 := rfl
@[simp] theorem hyperbolicShearF_one (n : ℤ) (x : Fin 4 → ℤ) :
    hyperbolicShearF n x 1 = x 1 + n * x 2 := rfl
@[simp] theorem hyperbolicShearF_two (n : ℤ) (x : Fin 4 → ℤ) :
    hyperbolicShearF n x 2 = x 2 := rfl
@[simp] theorem hyperbolicShearF_three (n : ℤ) (x : Fin 4 → ℤ) :
    hyperbolicShearF n x 3 = x 3 - n * x 0 := rfl

/-- The shear on the `E`-coordinates: `e ↦ e + m • Rot f`. -/
def hyperbolicShearE (m : ℤ) : (Fin 4 → ℤ) ≃ₗ[ℤ] (Fin 4 → ℤ) :=
  { toFun := fun x => ![x 0 + m * x 3, x 1, x 2 - m * x 1, x 3]
    invFun := fun x => ![x 0 - m * x 3, x 1, x 2 + m * x 1, x 3]
    left_inv := by
      intro x; funext i; fin_cases i <;> simp <;> ring
    right_inv := by
      intro x; funext i; fin_cases i <;> simp <;> ring
    map_add' := by
      intro x y; funext i; fin_cases i <;> simp <;> ring
    map_smul' := by
      intro r x; funext i; fin_cases i <;> simp <;> ring }

@[simp] theorem hyperbolicShearE_apply (m : ℤ) (x : Fin 4 → ℤ) :
    hyperbolicShearE m x = ![x 0 + m * x 3, x 1, x 2 - m * x 1, x 3] := rfl

@[simp] theorem hyperbolicShearE_zero (m : ℤ) (x : Fin 4 → ℤ) :
    hyperbolicShearE m x 0 = x 0 + m * x 3 := rfl
@[simp] theorem hyperbolicShearE_one (m : ℤ) (x : Fin 4 → ℤ) :
    hyperbolicShearE m x 1 = x 1 := rfl
@[simp] theorem hyperbolicShearE_two (m : ℤ) (x : Fin 4 → ℤ) :
    hyperbolicShearE m x 2 = x 2 - m * x 1 := rfl
@[simp] theorem hyperbolicShearE_three (m : ℤ) (x : Fin 4 → ℤ) :
    hyperbolicShearE m x 3 = x 3 := rfl

/-- The swap of the `E`- and `F`-coordinates. -/
def hyperbolicSwap : (Fin 4 → ℤ) ≃ₗ[ℤ] (Fin 4 → ℤ) :=
  { toFun := fun x => ![x 1, x 0, x 3, x 2]
    invFun := fun x => ![x 1, x 0, x 3, x 2]
    left_inv := by
      intro x; funext i; fin_cases i <;> simp
    right_inv := by
      intro x; funext i; fin_cases i <;> simp
    map_add' := by
      intro x y; funext i; fin_cases i <;> simp <;> ring
    map_smul' := by
      intro r x; funext i; fin_cases i <;> simp <;> ring }

@[simp] theorem hyperbolicSwap_apply (x : Fin 4 → ℤ) :
    hyperbolicSwap x = ![x 1, x 0, x 3, x 2] := rfl

@[simp] theorem hyperbolicSwap_zero (x : Fin 4 → ℤ) : hyperbolicSwap x 0 = x 1 := rfl
@[simp] theorem hyperbolicSwap_one (x : Fin 4 → ℤ) : hyperbolicSwap x 1 = x 0 := rfl
@[simp] theorem hyperbolicSwap_two (x : Fin 4 → ℤ) : hyperbolicSwap x 2 = x 3 := rfl
@[simp] theorem hyperbolicSwap_three (x : Fin 4 → ℤ) : hyperbolicSwap x 3 = x 2 := rfl

/-- Negation. -/
def hyperbolicNeg : (Fin 4 → ℤ) ≃ₗ[ℤ] (Fin 4 → ℤ) :=
  { toFun := fun x => fun i => -(x i)
    invFun := fun x => fun i => -(x i)
    left_inv := by intro x; funext i; simp
    right_inv := by intro x; funext i; simp
    map_add' := by intro x y; funext i; simp <;> ring
    map_smul' := by intro r x; funext i; simp <;> ring }

@[simp] theorem hyperbolicNeg_apply (x : Fin 4 → ℤ) :
    hyperbolicNeg x = fun i => -(x i) := rfl

/-- The four coordinate shears, swap and negation preserve all self-pairings. -/
theorem self_pairing_elementary :
    (∀ n : ℤ, ∀ x : Fin 4 → ℤ,
      twoHyperbolicPlanes.obj.pairing (hyperbolicShearF n x) (hyperbolicShearF n x) =
        twoHyperbolicPlanes.obj.pairing x x) ∧
    (∀ n : ℤ, ∀ x : Fin 4 → ℤ,
      twoHyperbolicPlanes.obj.pairing (hyperbolicShearE n x) (hyperbolicShearE n x) =
        twoHyperbolicPlanes.obj.pairing x x) ∧
    (∀ x : Fin 4 → ℤ,
      twoHyperbolicPlanes.obj.pairing (hyperbolicSwap x) (hyperbolicSwap x) =
        twoHyperbolicPlanes.obj.pairing x x) ∧
    (∀ x : Fin 4 → ℤ,
      twoHyperbolicPlanes.obj.pairing (hyperbolicNeg x) (hyperbolicNeg x) =
        twoHyperbolicPlanes.obj.pairing x x) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro n x
    rw [twoHyperbolicPlanes_pairing, twoHyperbolicPlanes_pairing]
    simp only [hyperbolicShearF_zero, hyperbolicShearF_one, hyperbolicShearF_two,
      hyperbolicShearF_three]
    ring
  · intro n x
    rw [twoHyperbolicPlanes_pairing, twoHyperbolicPlanes_pairing]
    simp only [hyperbolicShearE_zero, hyperbolicShearE_one, hyperbolicShearE_two,
      hyperbolicShearE_three]
    ring
  · intro x
    rw [twoHyperbolicPlanes_pairing, twoHyperbolicPlanes_pairing]
    simp only [hyperbolicSwap_zero, hyperbolicSwap_one, hyperbolicSwap_two,
      hyperbolicSwap_three]
    ring
  · intro x
    rw [twoHyperbolicPlanes_pairing, twoHyperbolicPlanes_pairing]
    simp only [hyperbolicNeg_apply, Pi.neg_apply, neg_mul_neg]

/-- The `E`-coordinates of a vector. -/
def eCoord (x : Fin 4 → ℤ) : Fin 2 → ℤ := ![x 0, x 2]

/-- The `F`-coordinates of a vector. -/
def fCoord (x : Fin 4 → ℤ) : Fin 2 → ℤ := ![x 1, x 3]

/-- The pairing in split coordinates: `eₓ • f_y + fₓ • e_y`. -/
theorem twoHyperbolicPlanes_pairing' (x y : Fin 4 → ℤ) :
    twoHyperbolicPlanes.obj.pairing x y =
      eCoord x ⬝ᵥ fCoord y + fCoord x ⬝ᵥ eCoord y := by
  rw [twoHyperbolicPlanes_pairing]
  simp only [eCoord, fCoord, dotProduct, Fin.sum_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  ring

/-- Two inverse matrices act on the two sides of the split dot product. -/
theorem mulVec_dot_mulVec (M N : Matrix (Fin 2) (Fin 2) ℤ) (hNM : N * M = 1)
    (u w : Fin 2 → ℤ) : (M.mulVec u) ⬝ᵥ ((Matrix.transpose N).mulVec w) = u ⬝ᵥ w := by
  have h00 : N 0 0 * M 0 0 + N 0 1 * M 1 0 = 1 := by
    have h := congrFun (congrFun hNM 0) 0
    simpa [Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_two] using h
  have h01 : N 0 0 * M 0 1 + N 0 1 * M 1 1 = 0 := by
    have h := congrFun (congrFun hNM 0) 1
    simpa [Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_two] using h
  have h10 : N 1 0 * M 0 0 + N 1 1 * M 1 0 = 0 := by
    have h := congrFun (congrFun hNM 1) 0
    simpa [Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_two] using h
  have h11 : N 1 0 * M 0 1 + N 1 1 * M 1 1 = 1 := by
    have h := congrFun (congrFun hNM 1) 1
    simpa [Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_two] using h
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.transpose_apply]
  linear_combination u 0 * w 0 * h00 + u 1 * w 1 * h11 + u 0 * w 1 * h10 + u 1 * w 0 * h01

/-- The action of an inverse matrix pair on a vector: `e ↦ M • e`, `f ↦ (M⁻¹)ᵀ • f`. -/
def hyperbolicLinearFn (M N : Matrix (Fin 2) (Fin 2) ℤ) (x : Fin 4 → ℤ) : Fin 4 → ℤ :=
  ![(M.mulVec (eCoord x)) 0, ((Matrix.transpose N).mulVec (fCoord x)) 0,
    (M.mulVec (eCoord x)) 1, ((Matrix.transpose N).mulVec (fCoord x)) 1]

@[simp] theorem eCoord_hyperbolicLinearFn (M N : Matrix (Fin 2) (Fin 2) ℤ) (x : Fin 4 → ℤ) :
    eCoord (hyperbolicLinearFn M N x) = M.mulVec (eCoord x) := by
  funext j; fin_cases j <;> rfl

@[simp] theorem fCoord_hyperbolicLinearFn (M N : Matrix (Fin 2) (Fin 2) ℤ) (x : Fin 4 → ℤ) :
    fCoord (hyperbolicLinearFn M N x) = (Matrix.transpose N).mulVec (fCoord x) := by
  funext j; fin_cases j <;> rfl

theorem eCoord_add (x y : Fin 4 → ℤ) : eCoord (x + y) = eCoord x + eCoord y := by
  funext j; fin_cases j <;> simp [eCoord]

theorem fCoord_add (x y : Fin 4 → ℤ) : fCoord (x + y) = fCoord x + fCoord y := by
  funext j; fin_cases j <;> simp [fCoord]

theorem eCoord_smul (r : ℤ) (x : Fin 4 → ℤ) : eCoord (r • x) = r • eCoord x := by
  funext j; fin_cases j <;> simp [eCoord]

theorem fCoord_smul (r : ℤ) (x : Fin 4 → ℤ) : fCoord (r • x) = r • fCoord x := by
  funext j; fin_cases j <;> simp [fCoord]

/-- The `GL₂(ℤ)` isometry of the split coordinates, with the inverse matrix supplied as `N`. -/
def hyperbolicLinear (M N : Matrix (Fin 2) (Fin 2) ℤ) (hMN : M * N = 1) (hNM : N * M = 1) :
    (Fin 4 → ℤ) ≃ₗ[ℤ] (Fin 4 → ℤ) where
  toFun := hyperbolicLinearFn M N
  invFun := hyperbolicLinearFn N M
  left_inv := by
    intro x
    funext i
    fin_cases i
    · show (N.mulVec (eCoord (hyperbolicLinearFn M N x))) 0 = x 0
      rw [eCoord_hyperbolicLinearFn, Matrix.mulVec_mulVec, hNM, Matrix.one_mulVec]
      rfl
    · show ((Matrix.transpose M).mulVec (fCoord (hyperbolicLinearFn M N x))) 0 = x 1
      rw [fCoord_hyperbolicLinearFn, Matrix.mulVec_mulVec, ← Matrix.transpose_mul, hNM,
        Matrix.transpose_one, Matrix.one_mulVec]
      rfl
    · show (N.mulVec (eCoord (hyperbolicLinearFn M N x))) 1 = x 2
      rw [eCoord_hyperbolicLinearFn, Matrix.mulVec_mulVec, hNM, Matrix.one_mulVec]
      rfl
    · show ((Matrix.transpose M).mulVec (fCoord (hyperbolicLinearFn M N x))) 1 = x 3
      rw [fCoord_hyperbolicLinearFn, Matrix.mulVec_mulVec, ← Matrix.transpose_mul, hNM,
        Matrix.transpose_one, Matrix.one_mulVec]
      rfl
  right_inv := by
    intro x
    funext i
    fin_cases i
    · show (M.mulVec (eCoord (hyperbolicLinearFn N M x))) 0 = x 0
      rw [eCoord_hyperbolicLinearFn, Matrix.mulVec_mulVec, hMN, Matrix.one_mulVec]
      rfl
    · show ((Matrix.transpose N).mulVec (fCoord (hyperbolicLinearFn N M x))) 0 = x 1
      rw [fCoord_hyperbolicLinearFn, Matrix.mulVec_mulVec, ← Matrix.transpose_mul, hMN,
        Matrix.transpose_one, Matrix.one_mulVec]
      rfl
    · show (M.mulVec (eCoord (hyperbolicLinearFn N M x))) 1 = x 2
      rw [eCoord_hyperbolicLinearFn, Matrix.mulVec_mulVec, hMN, Matrix.one_mulVec]
      rfl
    · show ((Matrix.transpose N).mulVec (fCoord (hyperbolicLinearFn N M x))) 1 = x 3
      rw [fCoord_hyperbolicLinearFn, Matrix.mulVec_mulVec, ← Matrix.transpose_mul, hMN,
        Matrix.transpose_one, Matrix.one_mulVec]
      rfl
  map_add' := by
    intro x y
    funext i
    fin_cases i <;> simp [hyperbolicLinearFn, eCoord_add, fCoord_add, Matrix.mulVec_add]
  map_smul' := by
    intro r x
    show hyperbolicLinearFn M N (r • x) = r • hyperbolicLinearFn M N x
    funext i
    fin_cases i <;>
      simp [hyperbolicLinearFn, eCoord, fCoord, Matrix.mulVec, dotProduct,
        Fin.sum_univ_two, Matrix.mul_apply] <;> ring

/-- The `GL₂(ℤ)` isometry preserves all self-pairings. -/
theorem hyperbolicLinear_self (M N : Matrix (Fin 2) (Fin 2) ℤ) (hMN : M * N = 1) (hNM : N * M = 1)
    (x : Fin 4 → ℤ) :
    twoHyperbolicPlanes.obj.pairing (hyperbolicLinear M N hMN hNM x)
        (hyperbolicLinear M N hMN hNM x) =
      twoHyperbolicPlanes.obj.pairing x x := by
  rw [twoHyperbolicPlanes_pairing', twoHyperbolicPlanes_pairing']
  have h1 : (M.mulVec (eCoord x)) ⬝ᵥ ((Matrix.transpose N).mulVec (fCoord x)) =
      eCoord x ⬝ᵥ fCoord x :=
    mulVec_dot_mulVec M N hNM (eCoord x) (fCoord x)
  have h2 : ((Matrix.transpose N).mulVec (fCoord x)) ⬝ᵥ (M.mulVec (eCoord x)) =
      fCoord x ⬝ᵥ eCoord x := by
    rw [dotProduct_comm ((Matrix.transpose N).mulVec (fCoord x)) (M.mulVec (eCoord x)),
      dotProduct_comm (fCoord x) (eCoord x)]
    exact mulVec_dot_mulVec M N hNM (eCoord x) (fCoord x)
  rw [show eCoord (hyperbolicLinear M N hMN hNM x) = M.mulVec (eCoord x) from
      eCoord_hyperbolicLinearFn M N x,
    show fCoord (hyperbolicLinear M N hMN hNM x) =
      (Matrix.transpose N).mulVec (fCoord x) from
      fCoord_hyperbolicLinearFn M N x]
  rw [h1, h2]

/-! ## The isometries as orthogonal-group elements -/

/-- The shear on `F`-coordinates, as an element of the orthogonal group. -/
def shearFGroup (n : ℤ) : OrthogonalGroup twoHyperbolicPlanes :=
  ⟨hyperbolicShearF n, pairing_of_self _ (self_pairing_elementary.1 n)⟩

/-- The shear on `E`-coordinates, as an element of the orthogonal group. -/
def shearEGroup (m : ℤ) : OrthogonalGroup twoHyperbolicPlanes :=
  ⟨hyperbolicShearE m, pairing_of_self _ (self_pairing_elementary.2.1 m)⟩

/-- The coordinate swap, as an element of the orthogonal group. -/
def swapGroup : OrthogonalGroup twoHyperbolicPlanes :=
  ⟨hyperbolicSwap, pairing_of_self _ self_pairing_elementary.2.2.1⟩

/-- Negation, as an element of the orthogonal group. -/
def negGroup : OrthogonalGroup twoHyperbolicPlanes :=
  ⟨hyperbolicNeg, pairing_of_self _ self_pairing_elementary.2.2.2⟩

/-- The `GL₂(ℤ)` isometry, as an element of the orthogonal group. -/
def linearGroup (M N : Matrix (Fin 2) (Fin 2) ℤ) (hMN : M * N = 1) (hNM : N * M = 1) :
    OrthogonalGroup twoHyperbolicPlanes :=
  ⟨hyperbolicLinear M N hMN hNM, pairing_of_self _ (hyperbolicLinear_self M N hMN hNM)⟩

/-- Multiplication in the orthogonal group acts by composition. -/
theorem group_mul_apply (g h : OrthogonalGroup twoHyperbolicPlanes) (x : Fin 4 → ℤ) :
    (g * h).1 x = g.1 (h.1 x) := rfl

/-! ## Bézout matrices and the normal form -/

/-- The Bézout normalizing pair: for a nonzero pair `(a, b)`, inverse matrices `M, N` with `M`
sending `(a, b)` to `(↑(a.gcd b), 0)`. The Bézout coefficients are `Int.gcdA` and `Int.gcdB`,
replacing a hand-rolled Bézout. -/
theorem exists_normalizing_pair (a b : ℤ) (hab : a ≠ 0 ∨ b ≠ 0) :
    ∃ (M N : Matrix (Fin 2) (Fin 2) ℤ) (c : ℤ), M * N = 1 ∧ N * M = 1 ∧ c ≠ 0 ∧
      M.mulVec ![a, b] = ![c, 0] := by
  have hg0 : a.gcd b ≠ 0 := by
    intro h0
    rw [Int.gcd_eq_zero_iff] at h0
    rcases hab with h | h <;> [exact h h0.1; exact h h0.2]
  set c : ℤ := (a.gcd b : ℤ) with hc
  have hbez : a * a.gcdA b + b * a.gcdB b = c := (Int.gcd_eq_gcd_ab a b).symm
  have hdva : c ∣ a := by
    rw [hc]; exact Int.gcd_dvd_left a b
  have hdvb : c ∣ b := by
    rw [hc]; exact Int.gcd_dvd_right a b
  have hda : a / c * c = a := Int.ediv_mul_cancel hdva
  have hdb : b / c * c = b := Int.ediv_mul_cancel hdvb
  have hcne : c ≠ 0 := by rw [hc]; exact_mod_cast hg0
  have key : a.gcdA b * (a / c) + a.gcdB b * (b / c) = 1 := by
    have h1 : (a.gcdA b * (a / c) + a.gcdB b * (b / c)) * c = 1 * c := by
      linear_combination a.gcdA b * hda + a.gcdB b * hdb + hbez
    exact mul_right_cancel₀ hcne h1
  have key2 : (a / c) * b = (b / c) * a := by
    linear_combination (b / c) * hda - (a / c) * hdb
  refine ⟨!![a.gcdA b, a.gcdB b; -(b / c), a / c],
    !![a / c, -(a.gcdB b); b / c, a.gcdA b], c, ?_, ?_, ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> simp
    all_goals linarith [key]
  · ext i j
    fin_cases i <;> fin_cases j <;> simp
    all_goals linarith [key]
  · exact hcne
  · funext j
    fin_cases j <;> simp [Matrix.mulVec, dotProduct]
    all_goals linarith [hbez, key2]

/-! ## The normal form -/

/-- The normal form when the `E`-coordinates do not vanish: normalize the `E`-part by a Bézout
matrix; the `F`-part lands in the second coordinate by isotropy. -/
theorem exists_normalForm_aux (v : Fin 4 → ℤ) (he : eCoord v ≠ 0)
    (hiso : twoHyperbolicPlanes.obj.pairing v v = 0) :
    ∃ (g : OrthogonalGroup twoHyperbolicPlanes) (d ν : ℤ),
      g.1 v = ![d, 0, 0, ν] ∧ d ≠ 0 := by
  have hab : eCoord v 0 ≠ 0 ∨ eCoord v 1 ≠ 0 := by
    by_contra h
    push Not at h
    apply he
    funext j
    fin_cases j
    · exact h.1
    · exact h.2
  obtain ⟨M, N, c, hMN, hNM, hc, hmv⟩ :=
    exists_normalizing_pair (eCoord v 0) (eCoord v 1) hab
  refine ⟨linearGroup M N hMN hNM, c, (Matrix.transpose N).mulVec (fCoord v) 1, ?_, hc⟩
  set w := (linearGroup M N hMN hNM).1 v with hw
  have hE : eCoord w = M.mulVec (eCoord v) := eCoord_hyperbolicLinearFn M N v
  have hF : fCoord w = (Matrix.transpose N).mulVec (fCoord v) :=
    fCoord_hyperbolicLinearFn M N v
  have hE' : eCoord w = ![c, 0] := by
    rw [hE]
    exact hmv
  -- isotropy forces the first F-coordinate to vanish
  have hpair : twoHyperbolicPlanes.obj.pairing w w = 0 := by
    have h := (linearGroup M N hMN hNM).2 v v
    rw [hiso] at h
    exact h
  have hsplit : eCoord w ⬝ᵥ fCoord w + fCoord w ⬝ᵥ eCoord w = 0 := by
    rw [← twoHyperbolicPlanes_pairing' w w]
    exact hpair
  rw [hE', hF] at hsplit
  have hν₁ : (Matrix.transpose N).mulVec (fCoord v) 0 = 0 := by
    simp only [dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons] at hsplit
    have h2 : c * (Matrix.transpose N).mulVec (fCoord v) 0 = 0 := by linarith
    exact (mul_eq_zero.mp h2).resolve_left hc
  funext i
  fin_cases i
  · exact congrFun hE' 0
  · exact (congrFun hF 0).trans hν₁
  · exact congrFun hE' 1
  · exact congrFun hF 1
/-- Every nonzero isotropic vector can be moved to `(d, 0, 0, ν)` with `d ≠ 0`. -/
theorem exists_normalForm_isometry (v : Fin 4 → ℤ) (hv : v ≠ 0)
    (hiso : twoHyperbolicPlanes.obj.pairing v v = 0) :
    ∃ (g : OrthogonalGroup twoHyperbolicPlanes) (d ν : ℤ),
      g.1 v = ![d, 0, 0, ν] ∧ d ≠ 0 := by
  by_cases he : eCoord v = 0
  · -- the `E`-part vanishes: swap first, so the new `E`-part is the old `F`-part
    have hf : fCoord v ≠ 0 := by
      intro h0
      have hv0 : v 0 = 0 := by
        have := congrFun he 0; simpa [eCoord] using this
      have hv2 : v 2 = 0 := by
        have := congrFun he 1; simpa [eCoord] using this
      have hv1 : v 1 = 0 := by
        have := congrFun h0 0; simpa [fCoord] using this
      have hv3 : v 3 = 0 := by
        have := congrFun h0 1; simpa [fCoord] using this
      apply hv
      funext i
      fin_cases i <;> simp [hv0, hv1, hv2, hv3]
    have hiso' : twoHyperbolicPlanes.obj.pairing (hyperbolicSwap v) (hyperbolicSwap v) =
        twoHyperbolicPlanes.obj.pairing v v :=
      pairing_of_self _ self_pairing_elementary.2.2.1 v v
    rw [hiso] at hiso'
    have he' : eCoord (hyperbolicSwap v) ≠ 0 := by
      intro h0
      apply hf
      rw [← h0]
      funext j; fin_cases j <;> simp [eCoord, fCoord, hyperbolicSwap]
    obtain ⟨g, d, ν, hg, hd⟩ := exists_normalForm_aux (hyperbolicSwap v) he' hiso'
    exact ⟨g * swapGroup, d, ν, by rw [group_mul_apply]; exact hg, hd⟩
  · obtain ⟨g, d, ν, hg, hd⟩ := exists_normalForm_aux v he hiso
    exact ⟨g, d, ν, hg, hd⟩


/-! ## The Euclidean descent -/

/-- The swap matrix in dimension two. -/
def swapMatrix : Matrix (Fin 2) (Fin 2) ℤ := !![0, 1; 1, 0]

theorem swapMatrix_mul : swapMatrix * swapMatrix = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

/-- The normal-form coordinate swap `(d, 0, 0, ν) ↦ (ν, 0, 0, d)`, as one group element. -/
def normalSwapGroup : OrthogonalGroup twoHyperbolicPlanes :=
  linearGroup swapMatrix swapMatrix swapMatrix_mul swapMatrix_mul * swapGroup

theorem normalSwapGroup_apply (d ν : ℤ) :
    normalSwapGroup.1 ![d, 0, 0, ν] = ![ν, 0, 0, d] := by
  rw [normalSwapGroup, group_mul_apply]
  have h1 : swapGroup.1 ![d, 0, 0, ν] = ![0, d, ν, 0] := by
    funext i
    fin_cases i <;> rfl
  rw [h1]
  funext i
  fin_cases i
  · show (swapMatrix.mulVec ![0, ν]) 0 = ν
    simp [Matrix.mulVec, swapMatrix]
  · show (Matrix.transpose swapMatrix).mulVec ![d, 0] 0 = 0
    simp [Matrix.mulVec, swapMatrix]
  · show (swapMatrix.mulVec ![0, ν]) 1 = 0
    simp [Matrix.mulVec, swapMatrix]
  · show (Matrix.transpose swapMatrix).mulVec ![d, 0] 1 = d
    simp [Matrix.mulVec, swapMatrix]

/-- Bézout coefficients witness coprimality. -/
theorem isCoprime_of_bezout (x y s t : ℤ) (h : x * s + y * t = 1) : IsCoprime x y :=
  ⟨s, t, by linear_combination h⟩

/-- Coprimality is preserved by subtracting a multiple. -/
theorem isCoprime_sub_mul (d ν q : ℤ) (h : IsCoprime d ν) : IsCoprime (d - ν * q) ν := by
  obtain ⟨a, b, hbez⟩ := h
  exact ⟨a, b + q * a, by linear_combination hbez⟩

/-- The Euclidean descent: a coprime normal form `(d, 0, 0, ν)` can be moved to the standard
vector by a shear, the coordinate swap and induction on `|ν|`. -/
theorem exists_descent_isometry (k : ℕ) :
    ∀ d ν : ℤ, IsCoprime d ν → ν.natAbs ≤ k →
      ∃ g : OrthogonalGroup twoHyperbolicPlanes, g.1 ![d, 0, 0, ν] = standardVector := by
  induction k with
  | zero =>
    intro d ν hc hk
    have hν : ν = 0 := Int.natAbs_eq_zero.mp (Nat.eq_zero_of_le_zero hk)
    subst hν
    have hd : d = 1 ∨ d = -1 := by
      rw [← Int.isUnit_iff]
      exact isCoprime_zero_right.mp hc
    rcases hd with hd | hd
    · refine ⟨1, ?_⟩
      rw [hd]
      rfl
    · refine ⟨negGroup, ?_⟩
      rw [hd]
      funext i
      fin_cases i <;> rfl
  | succ k ih =>
    intro d ν hc hk
    by_cases hν : ν = 0
    · subst hν
      have hd : d = 1 ∨ d = -1 := by
        rw [← Int.isUnit_iff]
        exact isCoprime_zero_right.mp hc
      rcases hd with hd | hd
      · refine ⟨1, ?_⟩
        rw [hd]
        rfl
      · refine ⟨negGroup, ?_⟩
        rw [hd]
        funext i
        fin_cases i <;> rfl
    · -- the shear reduces `d` modulo `ν`
      have hr : d % ν = d - ν * (d / ν) := by
        linear_combination Int.mul_ediv_add_emod d ν
      have hshear : (shearEGroup (-(d / ν))).1 ![d, 0, 0, ν] = ![d % ν, 0, 0, ν] := by
        funext i
        fin_cases i
        · show d + (-(d / ν)) * ν = d % ν
          linear_combination -hr
        · show (0 : ℤ) = 0
          rfl
        · show (0 : ℤ) - (-(d / ν)) * 0 = 0
          ring
        · show (ν : ℤ) = ν
          rfl
      -- the swap exchanges the two coordinates of the normal form
      have hswap : (linearGroup swapMatrix swapMatrix swapMatrix_mul swapMatrix_mul).1
          (swapGroup.1 ![d % ν, 0, 0, ν]) = ![ν, 0, 0, d % ν] := by
        have h1 : swapGroup.1 ![d % ν, 0, 0, ν] = ![0, d % ν, ν, 0] := by
          funext i
          fin_cases i <;> rfl
        rw [h1]
        funext i
        fin_cases i
        · show (swapMatrix.mulVec ![0, ν]) 0 = ν
          simp [Matrix.mulVec, swapMatrix]
        · show (Matrix.transpose swapMatrix).mulVec ![d % ν, 0] 0 = 0
          simp [Matrix.mulVec, swapMatrix]
        · show (swapMatrix.mulVec ![0, ν]) 1 = 0
          simp [Matrix.mulVec, swapMatrix]
        · show (Matrix.transpose swapMatrix).mulVec ![d % ν, 0] 1 = d % ν
          simp [Matrix.mulVec, swapMatrix]
      -- the coprimality and the measure transfer
      have hcr : IsCoprime (d % ν) ν := by
        rw [hr]
        exact isCoprime_sub_mul d ν (d / ν) hc
      have hle : (d % ν).natAbs ≤ k := by
        have h0 : 0 ≤ d % ν := Int.emod_nonneg d hν
        have hu : d % ν < (ν.natAbs : ℤ) := Int.emod_lt d hν
        have hlt : (d % ν).natAbs < ν.natAbs := by
          rw [← Nat.cast_lt (α := ℤ), Int.natAbs_of_nonneg h0]
          exact hu
        exact Nat.lt_succ_iff.mp (Nat.lt_of_lt_of_le hlt hk)
      obtain ⟨g', hg'⟩ := ih ν (d % ν) hcr.symm hle
      refine ⟨g' * (normalSwapGroup * shearEGroup (-(d / ν))), ?_⟩
      have s1 : (g' * (normalSwapGroup * shearEGroup (-(d / ν)))).1 ![d, 0, 0, ν]
          = g'.1 ((normalSwapGroup * shearEGroup (-(d / ν))).1 ![d, 0, 0, ν]) :=
        group_mul_apply g' (normalSwapGroup * shearEGroup (-(d / ν))) ![d, 0, 0, ν]
      have s2 : g'.1 ((normalSwapGroup * shearEGroup (-(d / ν))).1 ![d, 0, 0, ν])
          = g'.1 (normalSwapGroup.1 ((shearEGroup (-(d / ν))).1 ![d, 0, 0, ν])) :=
        congrArg (fun t => g'.1 t)
          (group_mul_apply normalSwapGroup (shearEGroup (-(d / ν))) ![d, 0, 0, ν])
      have s3 : g'.1 (normalSwapGroup.1 ((shearEGroup (-(d / ν))).1 ![d, 0, 0, ν]))
          = g'.1 (normalSwapGroup.1 ![d % ν, 0, 0, ν]) :=
        congrArg (fun t => g'.1 (normalSwapGroup.1 t)) hshear
      have s4 : g'.1 (normalSwapGroup.1 ![d % ν, 0, 0, ν])
          = g'.1 ![ν, 0, 0, d % ν] :=
        congrArg (fun t => g'.1 t) (normalSwapGroup_apply (d % ν) ν)
      exact s1.trans (s2.trans (s3.trans (s4.trans hg')))

/-! ## Transitivity on primitive isotropic lines -/

/-- Every indivisible isotropic vector can be moved to the standard vector. -/
theorem exists_isometry_apply_eq (v : Fin 4 → ℤ) (hv : v ≠ 0)
    (hiso : twoHyperbolicPlanes.obj.pairing v v = 0)
    (hdiv : ∀ (c : ℤ) (w : Fin 4 → ℤ), v = c • w → c = 1 ∨ c = -1) :
    ∃ g : OrthogonalGroup twoHyperbolicPlanes, g.1 v = standardVector := by
  obtain ⟨g₁, d, ν, hg₁, hd⟩ := exists_normalForm_isometry v hv hiso
  -- the image is indivisible, since the isometry transports divisibility
  have hdiv' : ∀ (c : ℤ) (w : Fin 4 → ℤ), ![d, 0, 0, ν] = c • w → c = 1 ∨ c = -1 := by
    intro c w h
    refine hdiv c (g₁.1.symm w) ?_
    have hv' : v = g₁.1.symm ![d, 0, 0, ν] := by
      rw [← hg₁]
      exact (g₁.1.symm_apply_apply _).symm
    rw [hv', h]
    exact LinearEquiv.map_smul _ _ _
  -- so the pair of coordinates is coprime
  have hc : IsCoprime d ν := by
    by_contra hcon
    have hg1 : d.gcd ν ≠ 1 := fun h => hcon (Int.isCoprime_iff_gcd_eq_one.mpr h)
    have hdvdd : (d.gcd ν : ℤ) ∣ d := Int.gcd_dvd_left d ν
    have hdvdν : (d.gcd ν : ℤ) ∣ ν := Int.gcd_dvd_right d ν
    have hdivby : ![d, 0, 0, ν] = (d.gcd ν : ℤ) •
        ![d / (d.gcd ν : ℤ), 0, 0, ν / (d.gcd ν : ℤ)] := by
      funext i
      fin_cases i
      · show d = (d.gcd ν : ℤ) * (d / (d.gcd ν : ℤ))
        rw [mul_comm, Int.ediv_mul_cancel hdvdd]
      · show (0 : ℤ) = (d.gcd ν : ℤ) * 0
        ring
      · show (0 : ℤ) = (d.gcd ν : ℤ) * 0
        ring
      · show ν = (d.gcd ν : ℤ) * (ν / (d.gcd ν : ℤ))
        rw [mul_comm, Int.ediv_mul_cancel hdvdν]
    rcases hdiv' _ _ hdivby with h | h
    · exact hg1 (by exact_mod_cast h)
    · omega
  obtain ⟨g₂, hg₂⟩ := exists_descent_isometry ν.natAbs d ν hc le_rfl
  refine ⟨g₂ * g₁, ?_⟩
  rw [group_mul_apply, hg₁]
  exact hg₂

/-! ## The standard line -/

/-- Membership in the standard line is the vanishing of the last three coordinates. -/
theorem mem_standardSpan_iff (z : Fin 4 → ℤ) :
    z ∈ Submodule.span ℤ {standardVector} ↔ z 1 = 0 ∧ z 2 = 0 ∧ z 3 = 0 := by
  rw [Submodule.mem_span_singleton]
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨by simp [standardVector], by simp [standardVector], by simp [standardVector]⟩
  · rintro ⟨h1, h2, h3⟩
    refine ⟨z 0, ?_⟩
    funext i
    fin_cases i <;> simp [standardVector, h1, h2, h3]

/-- The zeroth coordinate identifies the standard line with `ℤ`. -/
def standardSpanCoord : Submodule.span ℤ {standardVector} ≃ₗ[ℤ] ℤ where
  toFun x := x.1 0
  invFun n := ⟨n • standardVector, Submodule.smul_mem _ n
    (Submodule.mem_span_singleton_self _)⟩
  left_inv := by
    intro x
    obtain ⟨k, hk⟩ := Submodule.mem_span_singleton.mp x.2
    ext j
    have hk0 : x.1 0 = k := by
      have h0 := congrFun hk 0
      simpa [standardVector] using h0.symm
    show ((x.1 0) • standardVector) j = x.1 j
    rw [hk0, hk]
  right_inv := by
    intro n
    simp [standardVector]
  map_add' := by
    intro x y; rfl
  map_smul' := by
    intro r x; rfl

/-- The quotient by the standard span is torsion-free: the last three coordinates of a
multiple detect membership. -/
theorem standardSpan_torsionFree :
    Module.IsTorsionFree ℤ ((Fin 4 → ℤ) ⧸ Submodule.span ℤ {standardVector}) := by
  refine ⟨fun r hr => ?_⟩
  have hr0 : r ≠ 0 := isRegular_iff_ne_zero.mp hr
  have key : ∀ q : (Fin 4 → ℤ) ⧸ Submodule.span ℤ {standardVector},
      r • q = 0 → q = 0 := by
    intro q
    induction q using Quotient.inductionOn with
    | _ x =>
      intro hq
      have h2 : r • x ∈ Submodule.span ℤ {standardVector} := by
        refine (Submodule.Quotient.mk_eq_zero _).mp ?_
        rw [Submodule.Quotient.mk_smul]
        exact hq
      obtain ⟨h1, h2', h3⟩ := (mem_standardSpan_iff _).mp h2
      rw [Pi.smul_apply, smul_eq_mul] at h1 h2' h3
      exact (Submodule.Quotient.mk_eq_zero _).mpr ((mem_standardSpan_iff _).mpr
        ⟨(mul_eq_zero.mp h1).resolve_left hr0,
         (mul_eq_zero.mp h2').resolve_left hr0,
         (mul_eq_zero.mp h3).resolve_left hr0⟩)
  show Function.Injective ((r • ·) :
    (Fin 4 → ℤ) ⧸ Submodule.span ℤ {standardVector} →
      (Fin 4 → ℤ) ⧸ Submodule.span ℤ {standardVector})
  intro q1 q2 h
  have h' : r • q1 = r • q2 := h
  have h0 : r • (q1 - q2) = 0 := by
    rw [smul_sub, h', sub_self]
  exact sub_eq_zero.mp (key (q1 - q2) h0)

/-- The standard primitive isotropic line: the span of `standardVector`. -/
def standardLine : PrimitiveIsotropic twoHyperbolicPlanes 1 where
  toSubmodule := Submodule.span ℤ {standardVector}
  isotropic := by
    intro x hx y hy
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hx
    obtain ⟨b, hb⟩ := Submodule.mem_span_singleton.mp hy
    show x 0 * y 1 + x 1 * y 0 + x 2 * y 3 + x 3 * y 2 = 0
    rw [← ha, ← hb]
    show a * 1 * (b * 0) + a * 0 * (b * 1) + a * 0 * (b * 0) + a * 0 * (b * 0) = 0
    ring
  finrank_eq := by
    have h : Module.finrank ℤ (Submodule.span ℤ {standardVector}) = 1 := by
      rw [LinearEquiv.finrank_eq standardSpanCoord]
      exact Module.finrank_self ℤ
    exact h
  primitive := standardSpan_torsionFree

/-! ## The conjugacy of primitive isotropic lines -/

/-- Every primitive isotropic line has an indivisible generator. -/
theorem PrimitiveIsotropic.exists_generator (N : PrimitiveIsotropic twoHyperbolicPlanes 1) :
    ∃ v : Fin 4 → ℤ, N.toSubmodule = Submodule.span ℤ {v} ∧ v ≠ 0 ∧
      (∀ (c : ℤ) (w : Fin 4 → ℤ), v = c • w → c = 1 ∨ c = -1) := by
  -- a `Fin 4`-typed copy of the submodule, to keep instance matching uniform
  set P : Submodule ℤ (Fin 4 → ℤ) := N.toSubmodule with hPdef
  obtain ⟨n, b⟩ := Submodule.basisOfPid (Pi.basisFun ℤ (Fin 4)) P
  have hn : n = 1 := by
    have h1 : Module.finrank ℤ ↥P = Fintype.card (Fin n) := Module.finrank_eq_card_basis b
    have h2 : Module.finrank ℤ ↥P = 1 := N.finrank_eq
    rw [h2] at h1
    rw [Fintype.card_fin] at h1
    omega
  subst hn
  have hvne : b ⟨0, by omega⟩ ≠ 0 := linearIndependent_unique_iff.mp b.linearIndependent
  have hvne' : (b ⟨0, by omega⟩ : Fin 4 → ℤ) ≠ 0 := fun h => hvne (Subtype.ext h)
  have hspaneq : P = Submodule.span ℤ {(b ⟨0, by omega⟩ : Fin 4 → ℤ)} := by
    refine le_antisymm ?_ ?_
    · intro x hx
      rw [Submodule.mem_span_singleton]
      have hrepr := b.sum_repr ⟨x, hx⟩
      rw [Fin.sum_univ_one] at hrepr
      refine ⟨b.repr ⟨x, hx⟩ ⟨0, by omega⟩, ?_⟩
      exact congrArg (Subtype.val) hrepr
    · rw [Submodule.span_le]
      intro t ht
      rcases ht with rfl | ht
      exact Submodule.coe_mem _
  refine ⟨b ⟨0, by omega⟩, hspaneq, hvne', ?_⟩
  -- the generator is indivisible: the quotient is torsion-free
  intro c w hcv
  by_contra hcon
  push Not at hcon
  have hc0 : c ≠ 0 := by
    intro h0
    rw [h0, zero_smul] at hcv
    exact hvne' hcv
  have hmem : c • w ∈ P := by
    rw [← hcv]
    exact Submodule.coe_mem _
  letI : Module.IsTorsionFree ℤ ((Fin 4 → ℤ) ⧸ P) := N.primitive
  have hzero : c • (P.mkQ w) = 0 := by
    have h1 : P.mkQ (c • w) = c • P.mkQ w := LinearMap.map_smul _ c w
    rw [← h1, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact hmem
  have hwzero : P.mkQ w = 0 :=
    (smul_eq_zero.mp hzero).resolve_left hc0
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, hspaneq] at hwzero
  obtain ⟨k, hk⟩ := Submodule.mem_span_singleton.mp hwzero
  have hck : c * k = 1 := by
    have hvck : (b ⟨0, by omega⟩ : Fin 4 → ℤ) = c • (k • (b ⟨0, by omega⟩ : Fin 4 → ℤ)) :=
      hcv.trans (congrArg (fun t => c • t) hk.symm)
    have hzero2 : (1 - c * k) • (b ⟨0, by omega⟩ : Fin 4 → ℤ) = 0 := by
      rw [sub_smul, one_smul, mul_smul, ← hvck, sub_self]
    rcases smul_eq_zero.mp hzero2 with h | h
    · omega
    · exact absurd h hvne'
  rcases Int.isUnit_iff.mp ((isUnit_iff_exists.mpr ⟨k, hck, (mul_comm k c).trans hck⟩)) with
    h1 | h1
  · exact hcon.1 h1
  · exact hcon.2 h1

/-- Every primitive isotropic line is conjugate to the standard line. -/
theorem exists_isometry_smul_eq (N : PrimitiveIsotropic twoHyperbolicPlanes 1) :
    ∃ g : OrthogonalGroup twoHyperbolicPlanes, g • N = standardLine := by
  obtain ⟨v, hspan, hv, hdiv⟩ := N.exists_generator
  have hvN : v ∈ N.toSubmodule := by
    rw [hspan]
    exact Submodule.mem_span_singleton_self _
  have hiso : twoHyperbolicPlanes.obj.pairing v v = 0 :=
    N.isotropic v hvN v hvN
  obtain ⟨g, hg⟩ := exists_isometry_apply_eq v hv hiso hdiv
  refine ⟨g, PrimitiveIsotropic.ext ?_⟩
  show (g • N).toSubmodule = standardLine.toSubmodule
  show g • N.toSubmodule = Submodule.span ℤ {standardVector}
  rw [OrthogonalGroup.smul_submodule_eq_map, hspan]
  have hg' : (g.1 : twoHyperbolicPlanes.obj.carrier →ₗ[ℤ] twoHyperbolicPlanes.obj.carrier)
      (v : twoHyperbolicPlanes.obj.carrier) =
      (standardVector : twoHyperbolicPlanes.obj.carrier) := hg
  have hmap : (Submodule.map
      (g.1 : twoHyperbolicPlanes.obj.carrier →ₗ[ℤ] twoHyperbolicPlanes.obj.carrier)
      (ℤ ∙ (v : twoHyperbolicPlanes.obj.carrier)) :
      Submodule ℤ twoHyperbolicPlanes.obj.carrier) =
      (ℤ ∙ (standardVector : twoHyperbolicPlanes.obj.carrier) :
        Submodule ℤ twoHyperbolicPlanes.obj.carrier) := by
    refine le_antisymm ?_ ?_
    · rw [Submodule.map_le_iff_le_comap, Submodule.span_le]
      intro t ht
      rcases ht with rfl | ht
      exact Submodule.mem_comap.mpr (by
        rw [hg']
        exact Submodule.mem_span_singleton_self _)
    · rw [Submodule.span_le]
      intro t ht
      rcases ht with rfl | ht
      exact Submodule.mem_map.mpr ⟨(v : twoHyperbolicPlanes.obj.carrier),
        Submodule.mem_span_singleton_self _, hg'⟩
  exact hmap

/-! ## The trivial discriminant -/

/-- The Gram matrix of the split form at the standard basis. -/
def splitGramMatrix : Matrix (Fin 4) (Fin 4) ℤ :=
  !![0, 1, 0, 0; 1, 0, 0, 0; 0, 0, 0, 1; 0, 0, 1, 0]

theorem splitGramMatrix_mul : splitGramMatrix * splitGramMatrix = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

theorem twoHyperbolicPlanes_gramMatrix :
    gramMatrix twoHyperbolicPlanes (Pi.basisFun ℤ (Fin 4)) = splitGramMatrix := by
  ext i j
  have h1 : gramMatrix twoHyperbolicPlanes (Pi.basisFun ℤ (Fin 4)) i j =
      twoHyperbolicPlanes.obj.bilinMap ((Pi.basisFun ℤ (Fin 4)) i)
        ((Pi.basisFun ℤ (Fin 4)) j) :=
    LinearMap.BilinForm.toMatrix_apply (Pi.basisFun ℤ (Fin 4))
      twoHyperbolicPlanes.obj.bilinMap i j
  rw [h1]
  show twoHyperbolicPlanes.obj.pairing _ _ = _
  rw [twoHyperbolicPlanes_pairing]
  fin_cases i <;> fin_cases j <;> simp [splitGramMatrix, Pi.single_apply, Pi.basisFun_apply]

/-- `U ⊕ U` is perfect over the fraction field: its Gram matrix is an involution. -/
theorem twoHyperbolicPlanes_isFractionFieldPerfect :
    IsFractionFieldPerfect ℤ twoHyperbolicPlanes := by
  rw [isFractionFieldPerfect_iff_determinant_ne_zero ℤ twoHyperbolicPlanes
    (Pi.basisFun ℤ (Fin 4))]
  intro h0
  have h0' : splitGramMatrix.det = 0 := by
    have hgem : (gramMatrix twoHyperbolicPlanes (Pi.basisFun ℤ (Fin 4))).det = 0 := h0
    rw [twoHyperbolicPlanes_gramMatrix] at hgem
    exact hgem
  have hsq : splitGramMatrix.det * splitGramMatrix.det = 1 := by
    calc splitGramMatrix.det * splitGramMatrix.det
        = (splitGramMatrix * splitGramMatrix).det := by rw [Matrix.det_mul]
      _ = (1 : Matrix (Fin 4) (Fin 4) ℤ).det := by rw [splitGramMatrix_mul]
      _ = 1 := Matrix.det_one
  rw [h0', zero_mul] at hsq
  norm_num at hsq

/-- The adjoint of `U ⊕ U` is surjective: every functional is a pairing with a vector. -/
theorem twoHyperbolicPlanes_adjoint_surjective :
    Function.Surjective (twoHyperbolicPlanes.obj.adjoint) := by
  intro φ
  have hc : ∀ j : Fin 4, φ (Pi.single j (1 : ℤ)) = φ (Pi.single j (1 : ℤ)) := fun _ => rfl
  refine ⟨![φ (Pi.single 1 (1 : ℤ)), φ (Pi.single 0 (1 : ℤ)),
    φ (Pi.single 3 (1 : ℤ)), φ (Pi.single 2 (1 : ℤ))], ?_⟩
  ext y
  set y' : Fin 4 → ℤ := y with hy'
  have hrep : y' = ∑ j, y' j • (Pi.single j (1 : ℤ)) := by
    have hsum := (Pi.basisFun ℤ (Fin 4)).sum_repr y'
    have hre : (Pi.basisFun ℤ (Fin 4)).repr y' = y' := rfl
    rw [hre] at hsum
    simpa using hsum.symm
  have hφy : φ y' = ∑ j, y' j * φ (Pi.single j (1 : ℤ)) := by
    conv => lhs; rw [hrep]
    have h2 : φ ((∑ j, y' j • (Pi.single j (1 : ℤ)) : Fin 4 → ℤ)) =
        ∑ j, φ (y' j • (Pi.single j (1 : ℤ))) :=
      map_sum φ (fun j => y' j • (Pi.single j (1 : ℤ))) Finset.univ
    rw [h2]
    refine Finset.sum_congr rfl fun j _ => ?_
    exact map_smul φ (y' j) (Pi.single j (1 : ℤ))
  show twoHyperbolicPlanes.obj.pairing _ y = φ y
  rw [← hy', hφy, twoHyperbolicPlanes_pairing]
  simp [Fin.sum_univ_four]
  ring

/-- The discriminant group of `U ⊕ U` is trivial. -/
theorem twoHyperbolicPlanes_defect_subsingleton :
    Subsingleton twoHyperbolicPlanes.obj.defect := by
  have hrange : LinearMap.range twoHyperbolicPlanes.obj.adjoint = ⊤ :=
    LinearMap.range_eq_top.mpr twoHyperbolicPlanes_adjoint_surjective
  refine ⟨fun a b => ?_⟩
  induction a using Quotient.inductionOn with
  | _ x =>
    induction b using Quotient.inductionOn with
    | _ y =>
      refine (Submodule.Quotient.eq (p := _)).mpr ?_
      rw [hrange]
      trivial

/-- All submodules of the trivial discriminant group coincide. -/
theorem twoHyperbolicPlanes_defect_submodules (P Q : Submodule ℤ twoHyperbolicPlanes.obj.defect) :
    P = Q := by
  haveI : Subsingleton twoHyperbolicPlanes.obj.defect :=
    twoHyperbolicPlanes_defect_subsingleton
  have hP : P = ⊥ := (Submodule.eq_bot_iff _).mpr fun x _ => Subsingleton.elim x 0
  have hQ : Q = ⊥ := (Submodule.eq_bot_iff _).mpr fun x _ => Subsingleton.elim x 0
  rw [hP, hQ]

/-! ## The worked instance -/

-- The value module `Frac(ℤ)/ℤ` carries two definitionally distinct `ℤ`-module structures
-- (the quotient one and the one induced by its additive group). The lattice definitions are
-- elaborated with the quotient one, so synthesis must pick it too.
attribute [local instance 10000] Submodule.Quotient.module

/-- Any two points of the trivial discriminant group are equal. -/
theorem twoHyperbolicPlanes_defect_allEqual (x y : twoHyperbolicPlanes.obj.defect) : x = y := by
  haveI := twoHyperbolicPlanes_defect_subsingleton
  exact Subsingleton.elim x y

/-- Any two elements of the orthogonal group of the trivial discriminant form are equal. -/
theorem twoHyperbolicPlanes_discGroup_allEqual
    (a b : BilinModuleCat.OrthogonalGroup
      (discriminantBilinObject ℤ twoHyperbolicPlanes
        twoHyperbolicPlanes_isFractionFieldPerfect)) : a = b :=
  Subtype.ext (LinearEquiv.ext fun x => twoHyperbolicPlanes_defect_allEqual (a.1 x) (b.1 x))

/-- Any two elements of the discriminant range are equal. -/
theorem twoHyperbolicPlanes_range_allEqual
    (a b : ↥(OrthogonalGroup.discriminantRepresentation
      twoHyperbolicPlanes_isFractionFieldPerfect).range) : a = b :=
  Subtype.ext (twoHyperbolicPlanes_discGroup_allEqual _ _)

/-- Any two elements of the stabilizer in the range are equal. -/
theorem twoHyperbolicPlanes_stabilizer_allEqual
    (a b : ↥(MulAction.stabilizer ↥(OrthogonalGroup.discriminantRepresentation
      twoHyperbolicPlanes_isFractionFieldPerfect).range (isotropicSubgroup standardLine))) :
    a = b :=
  Subtype.ext (twoHyperbolicPlanes_range_allEqual _ _)

/-- The stabilizer quotient of the fibre theorem is a subsingleton. -/
theorem twoHyperbolicPlanes_stabilizerQuotient_subsingleton :
    Subsingleton (↥(MulAction.stabilizer ↥(OrthogonalGroup.discriminantRepresentation
        twoHyperbolicPlanes_isFractionFieldPerfect).range (isotropicSubgroup standardLine)) ⧸
      ((MulAction.stabilizer (OrthogonalGroup twoHyperbolicPlanes) standardLine).map
        (OrthogonalGroup.discriminantRepresentation
          twoHyperbolicPlanes_isFractionFieldPerfect).rangeRestrict).subgroupOf
      (MulAction.stabilizer ↥(OrthogonalGroup.discriminantRepresentation
        twoHyperbolicPlanes_isFractionFieldPerfect).range (isotropicSubgroup standardLine))) := by
  refine ⟨fun a b => ?_⟩
  induction a using Quotient.inductionOn with
  | _ x =>
    induction b using Quotient.inductionOn with
    | _ y =>
      exact congrArg (fun z => (QuotientGroup.mk z :
        ↥(MulAction.stabilizer ↥(OrthogonalGroup.discriminantRepresentation
            twoHyperbolicPlanes_isFractionFieldPerfect).range (isotropicSubgroup standardLine)) ⧸
          ((MulAction.stabilizer (OrthogonalGroup twoHyperbolicPlanes) standardLine).map
            (OrthogonalGroup.discriminantRepresentation
              twoHyperbolicPlanes_isFractionFieldPerfect).rangeRestrict).subgroupOf
          (MulAction.stabilizer ↥(OrthogonalGroup.discriminantRepresentation
            twoHyperbolicPlanes_isFractionFieldPerfect).range (isotropicSubgroup standardLine))))
        (twoHyperbolicPlanes_stabilizer_allEqual x y)

/-- The stable group is all of `O(L)`: the discriminant group of `U ⊕ U` is trivial. -/
theorem twoHyperbolicPlanes_stable_eq_top :
    OrthogonalGroup.stableOrthogonalGroup twoHyperbolicPlanes_isFractionFieldPerfect = ⊤ := by
  refine (Subgroup.eq_top_iff' _).mpr fun g => ?_
  show g ∈ MonoidHom.ker (OrthogonalGroup.discriminantRepresentation
    twoHyperbolicPlanes_isFractionFieldPerfect)
  rw [MonoidHom.mem_ker]
  exact twoHyperbolicPlanes_discGroup_allEqual _ _

/-- The stable group has finite index. -/
theorem twoHyperbolicPlanes_finiteIndex :
    (OrthogonalGroup.stableOrthogonalGroup
      twoHyperbolicPlanes_isFractionFieldPerfect).FiniteIndex :=
  ⟨by rw [twoHyperbolicPlanes_stable_eq_top, Subgroup.index_top]; norm_num⟩

/-- The fibre of the fibre theorem at the standard line is a subsingleton, because the
stabilizer quotient is. -/
theorem twoHyperbolicPlanes_stableFibre_subsingleton :
    Subsingleton (StableFibre twoHyperbolicPlanes_isFractionFieldPerfect
      twoHyperbolicPlanes_finiteIndex 1 standardLine) := by
  have e := cuspOrbitsStableEquivStabilizer (R := ℤ) twoHyperbolicPlanes_isFractionFieldPerfect
    twoHyperbolicPlanes_finiteIndex standardLine
  have h := twoHyperbolicPlanes_stabilizerQuotient_subsingleton
  exact ⟨fun a b => e.injective (Subsingleton.elim (e a) (e b))⟩

/-- The `Γ` of the worked instance: the stable group, which is all of `O(L)` because the
discriminant group of `U ⊕ U` is trivial. -/
noncomputable def twoHyperbolicPlanesGamma : FiniteIndexSubgroup twoHyperbolicPlanes :=
  ⟨OrthogonalGroup.stableOrthogonalGroup twoHyperbolicPlanes_isFractionFieldPerfect,
    twoHyperbolicPlanes_finiteIndex⟩

theorem twoHyperbolicPlanesGamma_toSubgroup :
    twoHyperbolicPlanesGamma.toSubgroup = ⊤ :=
  twoHyperbolicPlanes_stable_eq_top

/-- The worked instance of #113: `L = U ⊕ U` with `Γ = O(L)` has exactly one primitive isotropic
line orbit. Every `Γ`-orbit lies in the fibre of the fibre theorem over the standard line
(by transitivity of `O(L)` on primitive isotropic lines), and that fibre is a quotient of a
stabilizer in the trivial discriminant range, hence a point. -/
@[instance_reducible]
noncomputable def twoHyperbolicPlanesCuspUnique :
    Unique (CuspOrbits twoHyperbolicPlanes twoHyperbolicPlanesGamma 1) := by
  classical
  -- The fibre element attached to a primitive isotropic line. It is a `let`-bound lambda rather
  -- than a `have`-bound tactic block: a `have` introduces an opaque local, so `(fibreOf N).1.1`
  -- would not reduce to `CuspOrbits.mk N` for the `congrArg` below.
  let fibreOf : ∀ N : PrimitiveIsotropic twoHyperbolicPlanes 1,
      StableFibre twoHyperbolicPlanes_isFractionFieldPerfect
        twoHyperbolicPlanes_finiteIndex 1 standardLine := fun N => by
    let g : OrthogonalGroup twoHyperbolicPlanes := Classical.choose (exists_isometry_smul_eq N)
    have hg : g • N = standardLine := Classical.choose_spec (exists_isometry_smul_eq N)
    have hmem : N ∈ MulAction.orbit (OrthogonalGroup twoHyperbolicPlanes) standardLine := by
      refine MulAction.mem_orbit_iff.mpr ⟨g⁻¹, ?_⟩
      show g⁻¹ • standardLine = N
      rw [← hg, inv_smul_smul]
    exact ⟨⟨CuspOrbits.mk _ N, ⟨N, hmem, rfl⟩⟩,
      twoHyperbolicPlanes_defect_submodules _ _⟩
  haveI hfibre : Subsingleton (StableFibre twoHyperbolicPlanes_isFractionFieldPerfect
      twoHyperbolicPlanes_finiteIndex 1 standardLine) :=
    twoHyperbolicPlanes_stableFibre_subsingleton
  have hsub : Subsingleton (CuspOrbits twoHyperbolicPlanes twoHyperbolicPlanesGamma 1) := by
    refine ⟨fun a b => ?_⟩
    induction a using Quotient.inductionOn with
    | _ N =>
      induction b using Quotient.inductionOn with
      | _ M =>
        exact congrArg (fun s => s.1.1) (Subsingleton.elim (fibreOf N) (fibreOf M))
  exact uniqueOfSubsingleton (CuspOrbits.mk _ standardLine)


/-! ## The vector form of the worked instance

Issue #113 states the worked instance for primitive isotropic **vectors** of `U ⊕ U`; the section
above counts **line** orbits. The two are related by `PrimitiveIsotropicVector.toLine`, and the
transitivity of `O(L)` on primitive isotropic vectors is `exists_isometry_apply_eq`, proved above for
the normal-form argument. Both formulations are recorded here, together with the two facts that make
the passage exact: the standard vector spans the standard line, and the sign `-1` lies in `Γ = O(L)`,
so the unit ambiguity of a line's generators is invisible on `Γ`-orbits. -/

/-- The line spanned by the standard vector is primitive: the other three coordinates of a vector
annihilated into the line by a nonzero scalar vanish. -/
theorem standardVector_primitiveSpan :
    IsPrimitiveSubmodule (Submodule.span ℤ {standardVector}) := by
  rw [isPrimitiveSubmodule_iff_saturation_eq]
  refine le_antisymm ?_ (le_saturation _)
  intro x hx
  obtain ⟨r, hr, hrx⟩ :=
    (mem_saturation_iff (R := ℤ) (Submodule.span ℤ {standardVector}) x).mp hx
  rw [Submodule.mem_span_singleton] at hrx ⊢
  obtain ⟨c, hc⟩ := hrx
  refine ⟨x 0, ?_⟩
  funext i
  fin_cases i
  · simp [standardVector, smul_eq_mul]
  · have h := congrFun hc 1
    simp only [standardVector, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons,
      Matrix.tail_cons, mul_zero, zero_mul] at h
    have hx' : x 1 = 0 := (mul_eq_zero.mp h.symm).resolve_left hr
    simp [hx', standardVector, smul_eq_mul]
  · have h := congrFun hc 2
    simp only [standardVector, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons,
      Matrix.tail_cons, mul_zero, zero_mul] at h
    have hx' : x 2 = 0 := (mul_eq_zero.mp h.symm).resolve_left hr
    simp [hx', standardVector, smul_eq_mul]
  · have h := congrFun hc 3
    simp only [standardVector, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons,
      Matrix.tail_cons, mul_zero, zero_mul] at h
    have hx' : x 3 = 0 := (mul_eq_zero.mp h.symm).resolve_left hr
    simp [hx', standardVector, smul_eq_mul]

/-- The standard vector as a primitive isotropic vector. -/
noncomputable def twoHyperbolicPlanesVector : PrimitiveIsotropicVector twoHyperbolicPlanes where
  toVector := standardVector
  nonzero := by
    intro h
    have h0 := congrFun h 0
    simp only [standardVector, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, Pi.zero_apply] at h0
    exact one_ne_zero h0
  isotropic := by
    rw [twoHyperbolicPlanes_pairing]
    simp [standardVector]
  indivisible := by
    intro c w hw
    have h0 := congrFun hw 0
    simp only [standardVector, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons,
      Matrix.tail_cons, mul_one] at h0
    exact isUnit_iff_exists.mpr ⟨w 0, h0.symm, by rw [mul_comm]; exact h0.symm⟩
  primitiveSpan := standardVector_primitiveSpan

@[simp]
theorem twoHyperbolicPlanesVector_toVector :
    twoHyperbolicPlanesVector.toVector = standardVector :=
  rfl

/-- The standard vector generates the standard line. This is the submodule form of
`PrimitiveIsotropicVector.toLine twoHyperbolicPlanesVector = standardLine`, stated without the
torsion-freeness instance that `toLine` carries as an argument: `toLine_toSubmodule` turns one into
the other. -/
theorem twoHyperbolicPlanesVector_span :
    Submodule.span ℤ {twoHyperbolicPlanesVector.toVector} = standardLine.toSubmodule :=
  rfl

/-- **The vector-orbit result**: `O(L)` is transitive on primitive isotropic vectors of `U ⊕ U`.
This is `exists_isometry_apply_eq`, the transitivity proved for the normal form, read on the type of
primitive isotropic vectors. -/
theorem twoHyperbolicPlanes_vectorTransitive (u : PrimitiveIsotropicVector twoHyperbolicPlanes) :
    ∃ g : OrthogonalGroup twoHyperbolicPlanes, g • twoHyperbolicPlanesVector = u := by
  have hdiv : ∀ (c : ℤ) (w : Fin 4 → ℤ), u.toVector = c • w → c = 1 ∨ c = -1 := by
    intro c w hw
    exact Int.isUnit_iff.mp (u.indivisible c w hw)
  obtain ⟨g, hg⟩ := exists_isometry_apply_eq u.toVector u.nonzero u.isotropic hdiv
  refine ⟨g⁻¹, ?_⟩
  apply PrimitiveIsotropicVector.ext
  rw [PrimitiveIsotropicVector.smul_toVector, twoHyperbolicPlanesVector_toVector]
  show (g⁻¹).1 standardVector = u.toVector
  rw [← hg]
  simp

/-- Transitivity in the form used for orbits: any two primitive isotropic vectors are related by an
isometry. -/
theorem twoHyperbolicPlanes_vectorOrbit_unique (u w : PrimitiveIsotropicVector twoHyperbolicPlanes) :
    ∃ g : OrthogonalGroup twoHyperbolicPlanes, g • u = w := by
  obtain ⟨g₁, h₁⟩ := twoHyperbolicPlanes_vectorTransitive u
  obtain ⟨g₂, h₂⟩ := twoHyperbolicPlanes_vectorTransitive w
  refine ⟨g₂ * g₁⁻¹, ?_⟩
  have hstep : g₁⁻¹ • u = twoHyperbolicPlanesVector := by
    rw [← h₁, inv_smul_smul]
  rw [mul_smul, hstep, h₂]

/-- The sign `-1` lies in `Γ = O(L)`: the two generators of a primitive isotropic line are therefore
in the same `Γ`-orbit, so the vector formulation and the line formulation of the worked instance
count the same orbits. -/
theorem twoHyperbolicPlanes_neg_mem :
    negGroup ∈ twoHyperbolicPlanesGamma.toSubgroup := by
  rw [twoHyperbolicPlanesGamma_toSubgroup]
  exact Subgroup.mem_top _

/-- The worked instance in the issue's vector formulation: with `Γ = O(L)`, the primitive isotropic
vectors of `U ⊕ U` form a single `Γ`-orbit. -/
theorem twoHyperbolicPlanes_vectorOrbit_single :
    ∀ u w : PrimitiveIsotropicVector twoHyperbolicPlanes,
      ∃ γ : twoHyperbolicPlanesGamma.toSubgroup, γ • u = w := by
  intro u w
  obtain ⟨g, hg⟩ := twoHyperbolicPlanes_vectorOrbit_unique u w
  exact ⟨⟨g, by rw [twoHyperbolicPlanesGamma_toSubgroup]; exact Subgroup.mem_top g⟩, hg⟩


attribute [local instance 10000] Submodule.Quotient.module

/-- `U ⊕ U` is even: the diagonal of its form vanishes in the standard basis, so the basis
criterion `isEven_of_basis` applies. -/
theorem twoHyperbolicPlanes_isEven : IsEven twoHyperbolicPlanes := by
  apply isEven_of_basis twoHyperbolicPlanes (Pi.basisFun ℤ (Fin 4))
  intro i
  rw [Ideal.mem_span_singleton]
  refine ⟨0, ?_⟩
  change twoHyperbolicPlanes.obj.pairing ((Pi.basisFun ℤ (Fin 4)) i)
      ((Pi.basisFun ℤ (Fin 4)) i) = 2 * 0
  fin_cases i <;> simp [twoHyperbolicPlanes_pairing]

/-- The quadratic discriminant representation of `U ⊕ U` is surjective onto the whole quadratic
orthogonal group `O(q_{U ⊕ U})`: the quadratic discriminant module is a subsingleton (the
lattice is
unimodular), so every quadratic isometry is the identity, and the identity isometry is a preimage.
This is the explicit surjectivity hypothesis of `vectorFibreEquivQuadraticSurjective`, proved
rather than assumed. -/
theorem twoHyperbolicPlanes_quadraticRepresentation_surjective :
    Function.Surjective (OrthogonalGroup.evenDiscriminantRepresentation
      twoHyperbolicPlanes_isFractionFieldPerfect twoHyperbolicPlanes_isEven) := by
  letI : Subsingleton (evenDiscriminantQuadraticObject twoHyperbolicPlanes
      twoHyperbolicPlanes_isFractionFieldPerfect twoHyperbolicPlanes_isEven).carrier :=
    twoHyperbolicPlanes_defect_subsingleton
  intro y
  refine ⟨1, ?_⟩
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  exact Subsingleton.elim _ _

/-- The kernel of the quadratic representation of `U ⊕ U` is all of `O(L)` — the discriminant is
trivial, so every isometry acts as the identity on it — and hence has finite index (index 1). This
is the finiteness hypothesis of `vectorFibreEquivQuadraticSurjective`, proved rather than assumed;
it also identifies the theorem's `Γ = ker ρ` with `O(L)`, as in the line formulation. -/
theorem twoHyperbolicPlanes_quadratic_kernel_finiteIndex :
    (MonoidHom.ker (OrthogonalGroup.evenDiscriminantRepresentation
      twoHyperbolicPlanes_isFractionFieldPerfect twoHyperbolicPlanes_isEven)).FiniteIndex := by
  have hk : MonoidHom.ker (OrthogonalGroup.evenDiscriminantRepresentation
      twoHyperbolicPlanes_isFractionFieldPerfect twoHyperbolicPlanes_isEven) = ⊤ := by
    refine (Subgroup.eq_top_iff' _).mpr (fun g => ?_)
    letI : Subsingleton (evenDiscriminantQuadraticObject twoHyperbolicPlanes
        twoHyperbolicPlanes_isFractionFieldPerfect twoHyperbolicPlanes_isEven).carrier :=
      twoHyperbolicPlanes_defect_subsingleton
    rw [MonoidHom.mem_ker]
    apply Subtype.ext
    apply LinearEquiv.ext
    intro x
    exact Subsingleton.elim _ _
  refine ⟨?_⟩
  rw [hk, Subgroup.index_top]
  norm_num

/-- The discriminant class `[v/d]` of the standard vector of `U ⊕ U`, read in the quadratic
discriminant module: the image of the lift `toMetricDual v` under the discriminant projection,
which is `[v/d]` for the divisor `d = 1`. That the divisor is `1` is unimodularity: the defect of
`U ⊕ U` is trivial (`twoHyperbolicPlanes_defect_subsingleton`), so by
`isUnimodular_iff_toMetricDual_surjective` the metric dual is the integral image and the primitive
lift of `v` in `L^∨` is `toMetricDual v` itself. -/
noncomputable def twoHyperbolicPlanesQuadraticClass :
    quadraticDiscriminantCarrier twoHyperbolicPlanes_isFractionFieldPerfect
      twoHyperbolicPlanes_isEven :=
  metricDualToDiscriminant ℤ twoHyperbolicPlanes
    (toMetricDual ℤ twoHyperbolicPlanes twoHyperbolicPlanesVector.toVector)

/-- The class `[v/d]` is trivial: the lift `toMetricDual v` lies in the image of `toMetricDual`,
which is exactly the kernel of the discriminant projection. -/
theorem twoHyperbolicPlanesQuadraticClass_eq_zero :
    twoHyperbolicPlanesQuadraticClass = 0 := by
  letI : Subsingleton (evenDiscriminantQuadraticObject twoHyperbolicPlanes
      twoHyperbolicPlanes_isFractionFieldPerfect twoHyperbolicPlanes_isEven).carrier :=
    twoHyperbolicPlanes_defect_subsingleton
  exact Subsingleton.elim _ _

/-- Every isometry stabilizing the standard vector fixes its discriminant class: the quadratic
discriminant module of `U ⊕ U` is a subsingleton, so the fixation is automatic — but it is the
`hstab` hypothesis of the fibre theorem, stated and proved rather than assumed. -/
theorem twoHyperbolicPlanes_quadratic_stabilizer_fixes_class
    (h : OrthogonalGroup twoHyperbolicPlanes)
    (_hf : h • twoHyperbolicPlanesVector = twoHyperbolicPlanesVector) :
    OrthogonalGroup.evenDiscriminantRepresentation twoHyperbolicPlanes_isFractionFieldPerfect
        twoHyperbolicPlanes_isEven h • twoHyperbolicPlanesQuadraticClass =
      twoHyperbolicPlanesQuadraticClass := by
  letI : Subsingleton (evenDiscriminantQuadraticObject twoHyperbolicPlanes
      twoHyperbolicPlanes_isFractionFieldPerfect twoHyperbolicPlanes_isEven).carrier :=
    twoHyperbolicPlanes_defect_subsingleton
  exact Subsingleton.elim _ _

set_option maxHeartbeats 1200000 in
-- instantiating the theorem re-elaborates the nested DoubleCoset/quotient-of-subgroup type
/-- **The `U ⊕ U` instance through the quadratic-discriminant fibre theorem** (#113): for
`L = U ⊕ U` (even, unimodular), `v` the standard primitive isotropic vector with divisor `d = 1`
and class `[v/d] = 0`, the fibre of the discriminant-class map `ker ρ · g · Stab(v) ↦
`ρ(g)·[v/d]`
over `[v/d]` is the stabilizer of `[v/d]` in `O(q_{U ⊕ U})` modulo `ρ(Stab_{O(L)}(v))`. Every
hypothesis of `vectorFibreEquivQuadraticSurjective` is discharged by a proved fact of this lattice:
surjectivity of the quadratic representation and the stabilizer fixation of the class; the
kernel is all of `O(L)` and so has finite index
(`twoHyperbolicPlanes_quadratic_kernel_finiteIndex`),
which identifies the theorem's `Γ = ker ρ` with `O(L)`. -/
noncomputable def twoHyperbolicPlanesQuadraticFibre :=
  @vectorFibreEquivQuadraticSurjective ℤ _ _ twoHyperbolicPlanes
    twoHyperbolicPlanesCarrierTorsionFree
    twoHyperbolicPlanes_isFractionFieldPerfect twoHyperbolicPlanes_isEven
    twoHyperbolicPlanesVector twoHyperbolicPlanesQuadraticClass
    (fun s hs => twoHyperbolicPlanes_quadratic_stabilizer_fixes_class s
      (MulAction.mem_stabilizer_iff.mp hs))
    twoHyperbolicPlanes_quadraticRepresentation_surjective
end LeanCategories.Lattices.Valued
