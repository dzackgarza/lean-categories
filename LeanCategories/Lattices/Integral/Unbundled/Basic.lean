module

public import Mathlib.LinearAlgebra.BilinearForm.Properties
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Basis.Basic

@[expose] public section

namespace LeanCategories.Lattices.Integral.Unbundled

/-!
# Milestone 1: Intrinsic Integral Quadratic Lattices

This module implements the core intrinsic integral quadratic lattice theory:
- Intrinsic lattice structure `IntegralLattice`
- Signatures, quadratic evaluation, even/odd parity
- Orthogonal sum, opposite lattice, and lattice scaling `L(n)`
- Submodules, primitivity, saturation, and orthogonal complement
-/

variable (L : Type*) [AddCommGroup L] [Module ℤ L] [Module.Finite ℤ L] [Module.Free ℤ L]

/-- An intrinsic integral quadratic lattice is a finite free ℤ-module equipped with a
symmetric bilinear form `B : L →ₗ[ℤ] L →ₗ[ℤ] ℤ`. -/
structure IntegralLattice where
  B : LinearMap.BilinForm ℤ L
  isSymm : B.IsSymm

namespace IntegralLattice

variable {L}

/-- Evaluate the bilinear form of an integral lattice on two elements. -/
def eval (M : IntegralLattice L) (x y : L) : ℤ :=
  M.B x y

/-- Quadratic form value `Q(x) = B(x, x)`. -/
def quad (M : IntegralLattice L) (x : L) : ℤ :=
  M.eval x x

/-- Non-degeneracy condition for an integral lattice. -/
def IsNondegenerate (M : IntegralLattice L) : Prop :=
  M.B.SeparatingLeft

/-- An integral lattice is even if `Q(x)` is even for all `x`. -/
def IsEven (M : IntegralLattice L) : Prop :=
  ∀ x : L, Even (M.quad x)

/-- An integral lattice is odd if it is not even. -/
def IsOdd (M : IntegralLattice L) : Prop :=
  ¬ M.IsEven

/-- Scaling of a lattice form by an integer factor `n`. -/
def scale (M : IntegralLattice L) (n : ℤ) : IntegralLattice L where
  B := n • M.B
  isSymm := by
    rw [LinearMap.BilinForm.isSymm_def]
    intro x y
    change (n • M.B) x y = (n • M.B) y x
    dsimp
    rw [M.isSymm.eq x y]

/-- Opposite lattice `-L` (scaling by `-1`). -/
def opp (M : IntegralLattice L) : IntegralLattice L :=
  M.scale (-1)

/-- A vector is a root vector if its quadratic norm is `±2` or `±1`. -/
def IsRoot (M : IntegralLattice L) (v : L) : Prop :=
  M.quad v = 2 ∨ M.quad v = -2 ∨ M.quad v = 1 ∨ M.quad v = -1

/-- A vector is isotropic if `Q(v) = 0`. -/
def IsIsotropic (M : IntegralLattice L) (v : L) : Prop :=
  M.quad v = 0

/-- Divisibility of a vector `v ∈ L` in the lattice `M`. -/
def div (M : IntegralLattice L) (v : L) : Submodule ℤ ℤ :=
  Submodule.map (M.B v) ⊤

/-- Gram matrix relative to a given basis. -/
noncomputable def gramMatrix {ι : Type*} [Fintype ι] [DecidableEq ι] (M : IntegralLattice L)
    (b : Module.Basis ι ℤ L) : Matrix ι ι ℤ :=
  Matrix.of (fun i j => M.eval (b i) (b j))

/-- Determinant of the lattice relative to a basis. -/
noncomputable def det {ι : Type*} [Fintype ι] [DecidableEq ι] (M : IntegralLattice L)
    (b : Module.Basis ι ℤ L) : ℤ :=
  (M.gramMatrix b).det

/-- Unimodular lattice: discriminant determinant has absolute value 1. -/
noncomputable def IsUnimodular {ι : Type*} [Fintype ι] [DecidableEq ι] (M : IntegralLattice L)
    (b : Module.Basis ι ℤ L) : Prop :=
  M.det b = 1 ∨ M.det b = -1

end IntegralLattice

variable (L1 : Type*) [AddCommGroup L1] [Module ℤ L1] [Module.Finite ℤ L1] [Module.Free ℤ L1]
variable (L2 : Type*) [AddCommGroup L2] [Module ℤ L2] [Module.Finite ℤ L2] [Module.Free ℤ L2]

/-- Direct sum bilinear form on `L1 × L2`. -/
def directSumBilin (M1 : IntegralLattice L1) (M2 : IntegralLattice L2) : LinearMap.BilinForm ℤ (L1 × L2) where
  toFun v := {
    toFun := fun w => M1.eval v.1 w.1 + M2.eval v.2 w.2,
    map_add' := fun w1 w2 => by
      dsimp [IntegralLattice.eval]
      rw [(M1.B v.1).map_add, (M2.B v.2).map_add]
      ring,
    map_smul' := fun r w => by
      dsimp [IntegralLattice.eval]
      change (M1.B v.1) (r • w.1) + (M2.B v.2) (r • w.2) = r * (M1.B v.1 w.1 + M2.B v.2 w.2)
      rw [(M1.B v.1).map_smul_of_tower r w.1, (M2.B v.2).map_smul_of_tower r w.2]
      ring
  }
  map_add' v1 v2 := by
    ext w
    dsimp [IntegralLattice.eval]
    rw [M1.B.map_add, M2.B.map_add, LinearMap.add_apply, LinearMap.add_apply]
    ring
  map_smul' r v := by
    ext w
    dsimp [IntegralLattice.eval]
    rw [M1.B.map_smul_of_tower r v.1, M2.B.map_smul_of_tower r v.2, LinearMap.smul_apply, LinearMap.smul_apply]
    ring

/-- Orthogonal direct sum of two integral lattices `L1 ⊕ L2`. -/
def OrthogonalSum (M1 : IntegralLattice L1) (M2 : IntegralLattice L2) : IntegralLattice (L1 × L2) where
  B := directSumBilin L1 L2 M1 M2
  isSymm := by
    rw [LinearMap.BilinForm.isSymm_def]
    intro ⟨x1, x2⟩ ⟨y1, y2⟩
    dsimp [directSumBilin, IntegralLattice.eval]
    rw [M1.isSymm.eq x1 y1, M2.isSymm.eq x2 y2]















end LeanCategories.Lattices.Integral.Unbundled
