/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Modules.Bilinear.Valued.Isometry
public import Mathlib.LinearAlgebra.BilinearForm.IsometryEquiv

@[expose] public section

namespace LeanCategories.Modules.Bilinear.Valued

universe u

variable {R W : Type u} [CommRing R] [AddCommGroup W] [Module R W]

namespace BilinModuleCat

/-- Form-preserving linear automorphisms of a formed module. -/
def orthogonalSubgroup (M : BilinModuleCat R W) :
    Subgroup (M.carrier ≃ₗ[R] M.carrier) where
  carrier f := ∀ x y, M.pairing (f x) (f y) = M.pairing x y
  one_mem' := fun _ _ ↦ rfl
  mul_mem' := by
    intro f g hf hg x y
    exact (hf (g x) (g y)).trans (hg x y)
  inv_mem' := by
    intro f hf x y
    simpa using (hf (f.symm x) (f.symm y)).symm

/-- The orthogonal group of a formed module. -/
abbrev OrthogonalGroup (M : BilinModuleCat R W) :=
  orthogonalSubgroup M

namespace OrthogonalGroup

variable {M : BilinModuleCat R W}

/-- An orthogonal-group element of a scalar-valued form as a Mathlib isometry. -/
def toMathlibIsometryEquiv {N : BilinModuleCat R R}
    (g : OrthogonalGroup N) :
    N.asBilinForm.IsometryEquiv N.asBilinForm where
  __ := g.1
  map_app' x y := g.property x y

/-- A Mathlib isometric equivalence as an orthogonal-group element. -/
def fromMathlibIsometryEquiv {N : BilinModuleCat R R}
    (g : N.asBilinForm.IsometryEquiv N.asBilinForm) :
    OrthogonalGroup N := by
  refine ⟨g.toLinearEquiv, ?_⟩
  intro x y
  exact g.map_app y x

@[simp]
theorem from_toMathlibIsometryEquiv {N : BilinModuleCat R R}
    (g : OrthogonalGroup N) :
    fromMathlibIsometryEquiv (toMathlibIsometryEquiv g) = g :=
  rfl

@[simp]
theorem to_fromMathlibIsometryEquiv
    {N : BilinModuleCat R R}
    (g : N.asBilinForm.IsometryEquiv N.asBilinForm) :
    toMathlibIsometryEquiv (fromMathlibIsometryEquiv g) = g :=
  rfl

/-- The action of the orthogonal group on the carrier. -/
def actOnVector (g : OrthogonalGroup M) (x : M.carrier) : M.carrier :=
  g.1 x

/-- The image of a submodule under an orthogonal-group element. -/
def actOnSubmodule (g : OrthogonalGroup M)
    (P : Submodule R M.carrier) : Submodule R M.carrier :=
  P.map g.1.toLinearMap

@[simp]
theorem actOnSubmodule_one (P : Submodule R M.carrier) :
    actOnSubmodule (1 : OrthogonalGroup M) P = P := by
  simp [actOnSubmodule]

theorem actOnSubmodule_mul (g h : OrthogonalGroup M)
    (P : Submodule R M.carrier) :
    actOnSubmodule (g * h) P =
      actOnSubmodule g (actOnSubmodule h P) := by
  exact Submodule.map_comp h.1.toLinearMap g.1.toLinearMap P

end OrthogonalGroup

end BilinModuleCat

end LeanCategories.Modules.Bilinear.Valued
