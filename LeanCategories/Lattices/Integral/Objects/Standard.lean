module

public import LeanCategories.Lattices.Integral.Objects.Basic

@[expose] public section

namespace LeanCategories.Lattices.Integral

/-- Hyperbolic plane bilinear form with Gram matrix `[[0,1],[1,0]]`. -/
def hyperbolicPlaneForm : LinearMap.BilinForm ℤ (ℤ × ℤ) where
  toFun v :=
    { toFun w := v.1 * w.2 + v.2 * w.1
      map_add' := fun w₁ w₂ => by dsimp; ring
      map_smul' := fun r w => by dsimp; ring }
  map_add' v₁ v₂ := by apply LinearMap.ext; intro w; dsimp; ring
  map_smul' r v := by apply LinearMap.ext; intro w; dsimp; ring

/-- Hyperbolic plane U with Gram matrix [[0,1],[1,0]]. -/
def HyperbolicPlane : IntegralLattice where
  carrier := ℤ × ℤ
  form := hyperbolicPlaneForm
  isSymm := by
    rw [LinearMap.BilinForm.isSymm_def]
    intro ⟨x₁, x₂⟩ ⟨y₁, y₂⟩
    dsimp [hyperbolicPlaneForm]
    ring
  nondegenerate := by
    constructor
    · intro v hv
      have h1 := hv (1, 0)
      have h2 := hv (0, 1)
      simp only [hyperbolicPlaneForm, LinearMap.coe_mk, AddHom.coe_mk] at h1 h2
      simp only [Prod.ext_iff, Prod.fst_zero, Prod.snd_zero]
      omega
    · intro v hv
      have h1 := hv (1, 0)
      have h2 := hv (0, 1)
      simp only [hyperbolicPlaneForm, LinearMap.coe_mk, AddHom.coe_mk] at h1 h2
      simp only [Prod.ext_iff, Prod.fst_zero, Prod.snd_zero]
      omega

/-- The carrier of U is the standard rank-two free module. -/
def hyperbolicPlaneCarrier : HyperbolicPlane.carrier ≃ₗ[ℤ] ℤ × ℤ :=
  LinearEquiv.refl ℤ (ℤ × ℤ)

/-- Scale a lattice form by a nonzero integer, keeping the carrier. -/
def scale (L : IntegralLattice) (n : ℤ) (hn : n ≠ 0) : IntegralLattice where
  carrier := L.carrier
  form := n • L.form
  isSymm := by
    refine ⟨fun x y => ?_⟩
    simp only [LinearMap.smul_apply, smul_eq_mul]
    rw [L.isSymm.eq x y]
  nondegenerate := by
    constructor
    · intro x hx
      refine L.nondegenerate.1 x fun y => ?_
      have := hx y
      simp only [LinearMap.smul_apply, smul_eq_mul] at this
      exact (mul_eq_zero.mp this).resolve_left hn
    · intro y hy
      refine L.nondegenerate.2 y fun x => ?_
      have := hy x
      simp only [LinearMap.smul_apply, smul_eq_mul] at this
      exact (mul_eq_zero.mp this).resolve_left hn

/-- Scaling preserves the carrier. -/
def scaleCarrierEquiv (L : IntegralLattice) (n : ℤ) (hn : n ≠ 0) :
    (scale L n hn).carrier ≃ₗ[ℤ] L.carrier :=
  LinearEquiv.refl ℤ L.carrier

/-- Scaling multiplies the bilinear form by `n`. -/
theorem scale_form (L : IntegralLattice) (n : ℤ) (hn : n ≠ 0) (x y : L.carrier) :
    (scale L n hn).form x y = n * L.form x y := rfl

/-- The named rank-one lattice ⟨n⟩ for n ≠ 0. -/
axiom rankOneLattice (n : ℤ) (hn : n ≠ 0) : IntegralLattice

end LeanCategories.Lattices.Integral
