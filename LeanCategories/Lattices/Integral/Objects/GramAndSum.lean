module

public import LeanCategories.Lattices.Integral.Objects.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.RingTheory.Finiteness.Prod
public import Mathlib.LinearAlgebra.Basis.Prod

@[expose] public section

namespace LeanCategories.Lattices.Integral

/-- Gram matrix of a lattice with respect to an indexed family. -/
def gramMatrix {n : ℕ} (L : IntegralLattice) (b : Fin n → L.carrier) :
    Matrix (Fin n) (Fin n) ℤ := fun i j => L.form (b i) (b j)

/-- Gram determinant of an indexed family. -/
noncomputable def determinant {n : ℕ} (L : IntegralLattice) (b : Fin n → L.carrier) : ℤ :=
  Matrix.det (gramMatrix L b)

/-- Direct sum bilinear form on `L₁.carrier × L₂.carrier`. -/
def directSumForm (L₁ L₂ : IntegralLattice) :
    LinearMap.BilinForm ℤ (L₁.carrier × L₂.carrier) where
  toFun v :=
    { toFun w := L₁.form v.1 w.1 + L₂.form v.2 w.2
      map_add' := fun w₁ w₂ => by
        dsimp
        rw [(L₁.form v.1).map_add, (L₂.form v.2).map_add]
        ring
      map_smul' := fun r w => by
        dsimp
        rw [(L₁.form v.1).map_smul_of_tower r w.1, (L₂.form v.2).map_smul_of_tower r w.2]
        ring }
  map_add' v₁ v₂ := by
    refine LinearMap.ext fun w => ?_
    dsimp
    rw [L₁.form.map_add, L₂.form.map_add, LinearMap.add_apply, LinearMap.add_apply]
    ring
  map_smul' r v := by
    refine LinearMap.ext fun w => ?_
    dsimp
    rw [L₁.form.map_smul_of_tower r v.1, L₂.form.map_smul_of_tower r v.2,
      LinearMap.smul_apply, LinearMap.smul_apply]
    ring

/-- Orthogonal direct sum of integral lattices.

The carrier is the biproduct of the carriers in `Mod_ℤ`; the form is the sum of
the component forms, which is exactly what makes the two summands orthogonal. -/
def OrthogonalSum (L₁ L₂ : IntegralLattice) : IntegralLattice where
  carrier := L₁.carrier × L₂.carrier
  finite := Module.Finite.prod (R := ℤ) (M := L₁.carrier) (N := L₂.carrier)
  free := Module.Free.prod ℤ L₁.carrier L₂.carrier
  form := directSumForm L₁ L₂
  isSymm := by
    rw [LinearMap.BilinForm.isSymm_def]
    intro ⟨x₁, x₂⟩ ⟨y₁, y₂⟩
    dsimp [directSumForm]
    rw [L₁.isSymm.eq x₁ y₁, L₂.isSymm.eq x₂ y₂]
  nondegenerate := by
    constructor
    · intro v hv
      have h₁ : v.1 = 0 := by
        refine L₁.nondegenerate.1 v.1 fun w => ?_
        simpa [directSumForm] using hv (w, 0)
      have h₂ : v.2 = 0 := by
        refine L₂.nondegenerate.1 v.2 fun w => ?_
        simpa [directSumForm] using hv (0, w)
      simp only [Prod.ext_iff, Prod.fst_zero, Prod.snd_zero]
      exact ⟨h₁, h₂⟩
    · intro v hv
      have h₁ : v.1 = 0 := by
        refine L₁.nondegenerate.2 v.1 fun w => ?_
        simpa [directSumForm] using hv (w, 0)
      have h₂ : v.2 = 0 := by
        refine L₂.nondegenerate.2 v.2 fun w => ?_
        simpa [directSumForm] using hv (0, w)
      simp only [Prod.ext_iff, Prod.fst_zero, Prod.snd_zero]
      exact ⟨h₁, h₂⟩

/-- The direct-sum form is the sum of the two component forms. -/
theorem orthogonalSum_form (L₁ L₂ : IntegralLattice) :
    ∃ e : (OrthogonalSum L₁ L₂).carrier ≃ₗ[ℤ] L₁.carrier × L₂.carrier,
      ∀ x y, (OrthogonalSum L₁ L₂).form x y =
        L₁.form (e x).1 (e y).1 + L₂.form (e x).2 (e y).2 :=
  ⟨LinearEquiv.refl ℤ (L₁.carrier × L₂.carrier), fun _ _ => rfl⟩

end LeanCategories.Lattices.Integral
