/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Modules.Quadratic.Valued.Fixed
public import Mathlib.LinearAlgebra.QuadraticForm.IsometryEquiv

@[expose] public section

namespace LeanCategories.Modules.Quadratic.Valued

universe u

variable {R W : Type u} [CommRing R] [AddCommGroup W] [Module R W]

namespace QuadModuleCat

/-- Form-preserving linear automorphisms of a quadratic module. -/
def orthogonalSubgroup (Q : QuadModuleCat R W) :
    Subgroup (Q.carrier ≃ₗ[R] Q.carrier) where
  carrier f := ∀ x, Q.form (f x) = Q.form x
  one_mem' := fun _ ↦ rfl
  mul_mem' := by
    intro f g hf hg x
    exact (hf (g x)).trans (hg x)
  inv_mem' := by
    intro f hf x
    simpa using (hf (f.symm x)).symm

/-- The orthogonal group of a quadratic module. -/
abbrev OrthogonalGroup (Q : QuadModuleCat R W) :=
  orthogonalSubgroup Q

namespace OrthogonalGroup

variable {Q : QuadModuleCat R W}

/-- A quadratic orthogonal-group element as a Mathlib isometry. -/
def toMathlibIsometryEquiv (g : OrthogonalGroup Q) :
    Q.form.IsometryEquiv Q.form where
  __ := g.1
  map_app' x := g.property x

/-- A Mathlib quadratic isometry as an orthogonal-group element. -/
def fromMathlibIsometryEquiv (g : Q.form.IsometryEquiv Q.form) :
    OrthogonalGroup Q :=
  ⟨g.toLinearEquiv, g.map_app⟩

@[simp]
theorem from_toMathlibIsometryEquiv (g : OrthogonalGroup Q) :
    fromMathlibIsometryEquiv (toMathlibIsometryEquiv g) = g :=
  rfl

@[simp]
theorem to_fromMathlibIsometryEquiv (g : Q.form.IsometryEquiv Q.form) :
    toMathlibIsometryEquiv (fromMathlibIsometryEquiv g) = g :=
  rfl

end OrthogonalGroup

end QuadModuleCat

end LeanCategories.Modules.Quadratic.Valued
