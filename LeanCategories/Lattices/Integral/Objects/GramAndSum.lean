module

public import LeanCategories.Lattices.Integral.Objects.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

@[expose] public section

namespace LeanCategories.Lattices.Integral

/-- Gram matrix of a lattice with respect to an indexed family. -/
def gramMatrix {n : ℕ} (L : IntegralLattice) (b : Fin n → L.carrier) :
    Matrix (Fin n) (Fin n) ℤ := fun i j => L.form (b i) (b j)

/-- Gram determinant of an indexed family. -/
noncomputable def determinant {n : ℕ} (L : IntegralLattice) (b : Fin n → L.carrier) : ℤ :=
  Matrix.det (gramMatrix L b)

/-- Orthogonal direct sum of integral lattices.

Still an axiom: `IntegralLattice` carries `AddCommGroup carrier` and
`Module ℤ carrier` as independent fields, so on a product carrier Lean fixes the
module field to `AddCommGroup.toIntModule` while Mathlib's `Module.Finite.prod`
and `Module.Free.prod` produce the `Prod.instModule` form. The two are not
definitionally equal, and no choice of the `module` field satisfies both the
form and the finiteness/freeness obligations at once. Discharging this axiom
needs the redundant `module` field removed from `IntegralLattice`, which is a
change to the core structure rather than to this file. -/
axiom OrthogonalSum (L₁ L₂ : IntegralLattice) : IntegralLattice

/-- The direct-sum form is the sum of the two component forms. -/
axiom orthogonalSum_form (L₁ L₂ : IntegralLattice) :
  ∃ e : (OrthogonalSum L₁ L₂).carrier ≃ₗ[ℤ] L₁.carrier × L₂.carrier,
    ∀ x y, (OrthogonalSum L₁ L₂).form x y =
      L₁.form (e x).1 (e y).1 + L₂.form (e x).2 (e y).2

end LeanCategories.Lattices.Integral
