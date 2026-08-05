module

public import LeanCategories.Lattices.Integral.Unbundled.Basic
public import Mathlib.LinearAlgebra.Basis.Basic

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.BilinearForm

@[expose] public section

namespace LeanCategories.Lattices.Integral.Unbundled


/-!
# Dual Lattices and Discriminant Groups

This module constructs the dual lattice $L^\vee$ of an intrinsic integral lattice $L$,
its discriminant group $A_L = L^\vee / L$, and basic determinant properties.
-/

namespace IntegralLattice

variable {L : Type*} [AddCommGroup L] [Module ℤ L] [Module.Finite ℤ L] [Module.Free ℤ L]

/-- The dual space $L^\vee = \{ v \in L \otimes_\mathbb{Z} \mathbb{Q} \mid \forall x \in L, B(v, x) \in \mathbb{Z} \}$.
For an intrinsic lattice $L$, the dual module is represented via the linear map $L \to \text{Hom}_\mathbb{Z}(L, \mathbb{Z})$. -/
def dualMap (M : IntegralLattice L) : L →ₗ[ℤ] (L →ₗ[ℤ] ℤ) :=
  M.B

/-- The discriminant of an integral lattice relative to a basis. -/
noncomputable def discrWithBasis {ι : Type*} [Fintype ι] [DecidableEq ι] (M : IntegralLattice L) (b : Module.Basis ι ℤ L) : ℤ :=
  (Matrix.of (fun i j => M.eval (b i) (b j))).det



end IntegralLattice

end LeanCategories.Lattices.Integral.Unbundled
