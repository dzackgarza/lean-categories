/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Lattices.Valued.Constructions
public import LeanCategories.Modules.Bilinear.Valued.Isometry
public import Mathlib.LinearAlgebra.BilinearForm.IsometryEquiv

@[expose] public section

open LeanCategories.Modules.Bilinear.Valued

namespace LeanCategories.Lattices.Valued

universe u

variable {R : Type u} [CommRing R]

/-- Form-preserving linear automorphisms of a lattice. -/
def orthogonalSubgroup (L : IntegralLatticeCat R) :
    Subgroup (L.obj.carrier ≃ₗ[R] L.obj.carrier) where
  carrier f := ∀ x y, L.obj.pairing (f x) (f y) = L.obj.pairing x y
  one_mem' := fun _ _ ↦ rfl
  mul_mem' := by
    intro f g hf hg x y
    exact (hf (g x) (g y)).trans (hg x y)
  inv_mem' := by
    intro f hf x y
    simpa using (hf (f.symm x) (f.symm y)).symm

/-- The orthogonal group `O(L)`. -/
abbrev OrthogonalGroup (L : IntegralLatticeCat R) :=
  orthogonalSubgroup L

namespace OrthogonalGroup

variable {L : IntegralLatticeCat R}

/-- An orthogonal-group element as a Mathlib isometric equivalence. -/
def toMathlibIsometryEquiv (g : OrthogonalGroup L) :
    L.obj.asBilinForm.IsometryEquiv L.obj.asBilinForm where
  __ := g.1
  map_app' x y := by
    exact g.property x y

/-- A Mathlib isometric equivalence as an orthogonal-group element. -/
def fromMathlibIsometryEquiv
    (g : L.obj.asBilinForm.IsometryEquiv L.obj.asBilinForm) :
    OrthogonalGroup L := by
  refine ⟨g.toLinearEquiv, ?_⟩
  intro x y
  exact g.map_app y x

@[simp]
theorem from_toMathlibIsometryEquiv (g : OrthogonalGroup L) :
    fromMathlibIsometryEquiv (toMathlibIsometryEquiv g) = g :=
  rfl

@[simp]
theorem to_fromMathlibIsometryEquiv
    (g : L.obj.asBilinForm.IsometryEquiv L.obj.asBilinForm) :
    toMathlibIsometryEquiv (fromMathlibIsometryEquiv g) = g :=
  rfl

/-- The action of `O(L)` on the lattice carrier. -/
def actOnVector (g : OrthogonalGroup L) (x : L.obj.carrier) :
    L.obj.carrier :=
  g.1 x

/-- The image of a submodule under an orthogonal-group element. -/
def actOnSubmodule (g : OrthogonalGroup L)
    (P : Submodule R L.obj.carrier) : Submodule R L.obj.carrier :=
  P.map g.1.toLinearMap

@[simp]
theorem actOnSubmodule_one (P : Submodule R L.obj.carrier) :
    actOnSubmodule (1 : OrthogonalGroup L) P = P := by
  simp [actOnSubmodule]

theorem actOnSubmodule_mul (g h : OrthogonalGroup L)
    (P : Submodule R L.obj.carrier) :
    actOnSubmodule (g * h) P =
      actOnSubmodule g (actOnSubmodule h P) := by
  exact Submodule.map_comp h.1.toLinearMap g.1.toLinearMap P

end OrthogonalGroup

end LeanCategories.Lattices.Valued
