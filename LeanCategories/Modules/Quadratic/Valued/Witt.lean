/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Modules.Quadratic.Valued.Fixed

@[expose] public section

namespace LeanCategories.Modules.Quadratic.Valued

universe u

variable {R W : Type u} [CommRing R] [AddCommGroup W] [Module R W]

namespace QuadModuleCat

/-- A submodule is totally isotropic when the quadratic form vanishes on it. -/
def IsTotallyIsotropic (Q : QuadModuleCat R W)
    (P : Submodule R Q.carrier) : Prop :=
  ∀ x ∈ P, Q.form x = 0

/-- A quadratic module is anisotropic when zero is its only isotropic vector. -/
def IsAnisotropic (Q : QuadModuleCat R W) : Prop :=
  Q.form.Anisotropic

/-- The polarization vanishes on a totally isotropic submodule. -/
theorem IsTotallyIsotropic.polar_eq_zero
    {Q : QuadModuleCat R W} {P : Submodule R Q.carrier}
    (hP : Q.IsTotallyIsotropic P) {x y : Q.carrier}
    (hx : x ∈ P) (hy : y ∈ P) :
    QuadraticMap.polar Q.form x y = 0 := by
  rw [QuadraticMap.polar, hP (x + y) (P.add_mem hx hy), hP x hx,
    hP y hy]
  simp

end QuadModuleCat

end LeanCategories.Modules.Quadratic.Valued
