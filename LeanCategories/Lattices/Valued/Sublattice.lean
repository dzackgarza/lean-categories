/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Lattices.Valued.Arithmetic
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal

@[expose] public section

open CategoryTheory
open LeanCategories.Modules.Bilinear.Valued

namespace LeanCategories.Modules.Bilinear.Valued.BilinModuleCat

universe u

variable {R : Type u} [CommRing R]
variable {W : Type u} [AddCommGroup W] [Module R W]

/-- Restrict a formed module to a submodule. -/
def restrict (L : BilinModuleCat R W) (P : Submodule R L.carrier) :
    BilinModuleCat R W :=
  ofBilinMap (LinearMap.domRestrict₁₂ L.bilinMap P P)

@[simp]
theorem restrict_pairing (L : BilinModuleCat R W) (P : Submodule R L.carrier)
    (x y : P) :
    (L.restrict P).pairing x y = L.pairing x y :=
  rfl

/-- The inclusion of a restricted formed module. -/
def restrictInclusion (L : BilinModuleCat R W) (P : Submodule R L.carrier) :
    L.restrict P ⟶ L :=
  homMk P.subtype fun _ _ ↦ rfl

@[simp]
theorem underlyingMap_restrictInclusion
    (L : BilinModuleCat R W) (P : Submodule R L.carrier) :
    underlyingMap (L.restrictInclusion P) = P.subtype :=
  rfl

/-- A formed embedding is primitive when it is injective and has torsion-free cokernel. -/
def IsPrimitiveEmbedding {L M : BilinModuleCat R W} (f : L ⟶ M) : Prop :=
  Function.Injective (underlyingMap f) ∧
    Module.IsTorsionFree R
      (M.carrier ⧸ LinearMap.range (underlyingMap f))

end LeanCategories.Modules.Bilinear.Valued.BilinModuleCat

namespace LeanCategories.Lattices.Valued

universe u

variable {R : Type u} [CommRing R]
variable {W : Type u} [AddCommGroup W] [Module R W]

/-- A submodule is primitive when its quotient is torsion-free. -/
def IsPrimitiveSubmodule {M : Type u} [AddCommGroup M] [Module R M]
    (P : Submodule R M) : Prop :=
  Module.IsTorsionFree R (M ⧸ P)

/-- A projective submodule with the restricted form. -/
def formedSublattice (L : LatticeCat R W) (P : Submodule R L.obj.carrier)
    [Module.Projective R P] : LatticeCat R W := by
  refine ⟨L.obj.restrict P, ?_, ?_⟩
  · change Module.Projective R P
    infer_instance
  · intro x y
    change P at x y
    exact L.property.2 x y

/-- The inclusion of a formed sublattice. -/
def formedSublatticeInclusion (L : LatticeCat R W)
    (P : Submodule R L.obj.carrier) [Module.Projective R P] :
    formedSublattice L P ⟶ L :=
  ObjectProperty.homMk (L.obj.restrictInclusion P)

/-- The submodule orthogonal to `P` inside an integral lattice. -/
def orthogonalSubmodule (L : IntegralLatticeCat R)
    (P : Submodule R L.obj.carrier) : Submodule R L.obj.carrier :=
  LinearMap.BilinForm.orthogonal L.obj.bilinMap P

@[simp]
theorem mem_orthogonalSubmodule_iff (L : IntegralLatticeCat R)
    (P : Submodule R L.obj.carrier) (x : L.obj.carrier) :
    x ∈ orthogonalSubmodule L P ↔ ∀ p ∈ P, L.obj.pairing p x = 0 :=
  Iff.rfl

/-- The orthogonal complement with its restricted form. -/
def orthogonalComplement (L : IntegralLatticeCat R)
    (P : Submodule R L.obj.carrier)
    [Module.Projective R (orthogonalSubmodule L P)] : IntegralLatticeCat R :=
  formedSublattice L (orthogonalSubmodule L P)

/-- The inclusion of an orthogonal complement. -/
def orthogonalComplementInclusion (L : IntegralLatticeCat R)
    (P : Submodule R L.obj.carrier)
    [Module.Projective R (orthogonalSubmodule L P)] :
    orthogonalComplement L P ⟶ L :=
  formedSublatticeInclusion L (orthogonalSubmodule L P)

end LeanCategories.Lattices.Valued
