module

public import LeanCategories.Lattices.Integral.Unbundled.Basic
public import LeanCategories.Lattices.Integral.Unbundled.DualAndDiscriminant
public import Mathlib.Algebra.Group.Units.Equiv

@[expose] public section

namespace LeanCategories.Lattices.Integral.Unbundled

/-!
# Standard Lattices

This module implements standard named lattices ($U, A_n, D_n, E_8$) and
scalar scaling infrastructure $L(n)$ as part of Milestone 1 / Milestone 2.
-/

namespace IntegralLattice

/-- Hyperbolic plane bilinear form $U = \begin{pmatrix} 0 & 1 \\ 1 & 0 \end{pmatrix}$. -/
def hyperbolicPlaneBilin : LinearMap.BilinForm ℤ (ℤ × ℤ) where
  toFun v := {
    toFun := fun w => v.1 * w.2 + v.2 * w.1,
    map_add' := fun w1 w2 => by dsimp; ring,
    map_smul' := fun r w => by dsimp; ring
  }
  map_add' v1 v2 := by
    apply LinearMap.ext
    intro w
    dsimp
    ring
  map_smul' r v := by
    apply LinearMap.ext
    intro w
    dsimp
    ring



/-- Hyperbolic plane lattice $U$. -/
def HyperbolicPlane : IntegralLattice (ℤ × ℤ) where
  B := hyperbolicPlaneBilin
  isSymm := by
    rw [LinearMap.BilinForm.isSymm_def]
    intro ⟨x1, x2⟩ ⟨y1, y2⟩
    dsimp [hyperbolicPlaneBilin]
    ring



end IntegralLattice

end LeanCategories.Lattices.Integral.Unbundled
