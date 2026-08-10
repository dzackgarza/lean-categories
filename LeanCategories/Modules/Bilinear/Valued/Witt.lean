/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Modules.Bilinear.Valued.Fixed
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.QuadraticForm.Dual

@[expose] public section

namespace LeanCategories.Modules.Bilinear.Valued

universe u

variable {R : Type u} [CommRing R]

namespace BilinModuleCat

/-- The orthogonal submodule of a scalar-valued bilinear module. -/
def orthogonalSubmodule (L : BilinModuleCat R R)
    (P : Submodule R L.carrier) : Submodule R L.carrier :=
  LinearMap.BilinForm.orthogonal L.bilinMap P

@[simp]
theorem mem_orthogonalSubmodule_iff (L : BilinModuleCat R R)
    (P : Submodule R L.carrier) (x : L.carrier) :
    x ∈ L.orthogonalSubmodule P ↔
      ∀ p ∈ P, L.pairing p x = 0 :=
  Iff.rfl

/-- A submodule is totally isotropic when it lies in its orthogonal. -/
def IsTotallyIsotropic (L : BilinModuleCat R R)
    (P : Submodule R L.carrier) : Prop :=
  P ≤ L.orthogonalSubmodule P

/-- A submodule is Lagrangian when it equals its orthogonal. -/
def IsLagrangian (L : BilinModuleCat R R)
    (P : Submodule R L.carrier) : Prop :=
  L.orthogonalSubmodule P = P

/-- A scalar-valued form is metabolic when it has a Lagrangian submodule. -/
def IsMetabolic (L : BilinModuleCat R R) : Prop :=
  ∃ P, L.IsLagrangian P

/-- A scalar-valued form is anisotropic when zero is its only isotropic vector. -/
def IsAnisotropic (L : BilinModuleCat R R) : Prop :=
  ∀ x, L.pairing x x = 0 → x = 0

/-- Every Lagrangian submodule is totally isotropic. -/
theorem IsLagrangian.isTotallyIsotropic
    {L : BilinModuleCat R R} {P : Submodule R L.carrier}
    (hP : L.IsLagrangian P) : L.IsTotallyIsotropic P := by
  intro x hx
  rw [hP]
  exact hx

end BilinModuleCat

variable {K M : Type u} [Field K] [AddCommGroup M] [Module K M]

/-- The hyperbolic bilinear module on `Mᵛ × M`. -/
def hyperbolicBilinModule (K M : Type u) [Field K]
    [AddCommGroup M] [Module K M] : BilinModuleCat K K :=
  BilinModuleCat.ofBilinMap (LinearMap.dualProd K M)

@[simp]
theorem hyperbolicBilinModule_pairing
    (x y : Module.Dual K M × M) :
    (hyperbolicBilinModule K M).pairing x y =
      x.1 y.2 + y.1 x.2 := by
  change (LinearMap.dualProd K M) x y = _
  simp [add_comm]

/-- The standard Lagrangian `Mᵛ × {0}` in a hyperbolic module. -/
def hyperbolicLagrangian (K M : Type u) [Field K]
    [AddCommGroup M] [Module K M] :
    Submodule K (hyperbolicBilinModule K M).carrier :=
  LinearMap.ker (LinearMap.snd K (Module.Dual K M) M)

@[simp]
theorem mem_hyperbolicLagrangian_iff
    (x : (hyperbolicBilinModule K M).carrier) :
    x ∈ hyperbolicLagrangian K M ↔ x.2 = 0 :=
  Iff.rfl

/-- The standard hyperbolic submodule is Lagrangian. -/
theorem hyperbolicLagrangian_isLagrangian :
    (hyperbolicBilinModule K M).IsLagrangian
      (hyperbolicLagrangian K M) := by
  ext x
  constructor
  · intro hx
    rw [mem_hyperbolicLagrangian_iff]
    apply Module.eval_apply_injective K
    apply LinearMap.ext
    intro f
    have h := hx (f, 0) (by
      change (0 : M) = 0
      rfl)
    rw [BilinModuleCat.bilinMap_apply,
      hyperbolicBilinModule_pairing] at h
    simpa using h
  · intro hx
    rw [BilinModuleCat.mem_orthogonalSubmodule_iff]
    rw [mem_hyperbolicLagrangian_iff] at hx
    intro p hp
    rw [mem_hyperbolicLagrangian_iff] at hp
    rw [hyperbolicBilinModule_pairing]
    simp [hx, hp]

/-- Every standard hyperbolic bilinear module is metabolic. -/
theorem hyperbolicBilinModule_isMetabolic :
    (hyperbolicBilinModule K M).IsMetabolic :=
  ⟨hyperbolicLagrangian K M, hyperbolicLagrangian_isLagrangian⟩

end LeanCategories.Modules.Bilinear.Valued
