/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Lattices.Valued.OrthogonalGroup
public import LeanCategories.Lattices.Valued.Sublattice
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

@[expose] public section

open CategoryTheory
open LeanCategories.Modules.Bilinear.Valued

namespace LeanCategories.Lattices.Valued

universe u

variable {R : Type u} [CommRing R]

/-- An element of `O(L)` with square one. -/
structure Involution (L : IntegralLatticeCat R) where
  element : OrthogonalGroup L
  involutive : element * element = 1

/-- The fixed submodule of an involution. -/
def fixedSubmodule (L : IntegralLatticeCat R) (J : Involution L) :
    Submodule R L.obj.carrier :=
  LinearMap.ker (J.element.1.toLinearMap - LinearMap.id)

/-- The anti-fixed submodule of an involution. -/
def antiFixedSubmodule (L : IntegralLatticeCat R) (J : Involution L) :
    Submodule R L.obj.carrier :=
  LinearMap.ker (J.element.1.toLinearMap + LinearMap.id)

/-- The cyclic order-two representation determined by an involution. -/
noncomputable def Involution.cyclicActionHom (L : IntegralLatticeCat R)
    (J : Involution L) : Multiplicative (ZMod 2) →* OrthogonalGroup L := by
  let f : ℤ →+ Additive (OrthogonalGroup L) :=
    zmultiplesHom (Additive (OrthogonalGroup L)) (Additive.ofMul J.element)
  have hf : f 2 = 0 := by
    change Additive.ofMul (J.element ^ (2 : ℤ)) = 0
    rw [zpow_ofNat, pow_two, J.involutive]
    rfl
  exact AddMonoidHom.toMultiplicativeLeft (ZMod.lift 2 ⟨f, hf⟩)

@[simp]
theorem Involution.cyclicActionHom_generator (L : IntegralLatticeCat R)
    (J : Involution L) :
    J.cyclicActionHom L (Multiplicative.ofAdd (1 : ZMod 2)) = J.element := by
  change Additive.toMul ((ZMod.lift 2 _) ((1 : ℤ) : ZMod 2)) = J.element
  rw [ZMod.lift_coe]
  change J.element ^ (1 : ℤ) = J.element
  simp

/-- The cyclic order-two action on the lattice carrier. -/
@[reducible]
noncomputable def Involution.cyclicAction (L : IntegralLatticeCat R)
    (J : Involution L) : MulAction (Multiplicative (ZMod 2)) L.obj.carrier :=
  MulAction.compHom L.obj.carrier (J.cyclicActionHom L)

section PID

variable [IsDomain R] [IsPrincipalIdealRing R]

/-- The fixed submodule of a finite projective lattice is projective. -/
theorem fixedSubmodule_projective (L : IntegralLatticeCat R)
    [Module.Finite R L.obj.carrier] (J : Involution L) :
    Module.Projective R (fixedSubmodule L J) := by
  letI : Module.Projective R L.obj.carrier := L.property.1
  letI : Module.Free R L.obj.carrier := by infer_instance
  let b := Module.Free.chooseBasis R L.obj.carrier
  exact Module.Projective.of_basis ((fixedSubmodule L J).basisOfPid b).2

/-- The fixed vectors with their restricted form. -/
noncomputable def invariantLattice (L : IntegralLatticeCat R)
    [Module.Finite R L.obj.carrier] (J : Involution L) :
    IntegralLatticeCat R := by
  letI : Module.Projective R (fixedSubmodule L J) :=
    fixedSubmodule_projective L J
  exact formedSublattice L (fixedSubmodule L J)

/-- The inclusion of the invariant lattice. -/
noncomputable def invariantLatticeInclusion (L : IntegralLatticeCat R)
    [Module.Finite R L.obj.carrier] (J : Involution L) :
    invariantLattice L J ⟶ L := by
  letI : Module.Projective R (fixedSubmodule L J) :=
    fixedSubmodule_projective L J
  exact formedSublatticeInclusion L (fixedSubmodule L J)

/-- The orthogonal complement of the invariant lattice carrier. -/
def coinvariantSubmodule (L : IntegralLatticeCat R) (J : Involution L) :
    Submodule R L.obj.carrier :=
  orthogonalSubmodule L (fixedSubmodule L J)

/-- The coinvariant submodule of a finite projective lattice is projective. -/
theorem coinvariantSubmodule_projective (L : IntegralLatticeCat R)
    [Module.Finite R L.obj.carrier] (J : Involution L) :
    Module.Projective R (coinvariantSubmodule L J) := by
  letI : Module.Projective R L.obj.carrier := L.property.1
  letI : Module.Free R L.obj.carrier := by infer_instance
  let b := Module.Free.chooseBasis R L.obj.carrier
  exact Module.Projective.of_basis ((coinvariantSubmodule L J).basisOfPid b).2

/-- The coinvariant vectors with their restricted form. -/
noncomputable def coinvariantLattice (L : IntegralLatticeCat R)
    [Module.Finite R L.obj.carrier] (J : Involution L) :
    IntegralLatticeCat R := by
  letI : Module.Projective R (coinvariantSubmodule L J) :=
    coinvariantSubmodule_projective L J
  exact formedSublattice L (coinvariantSubmodule L J)

/-- The inclusion of the coinvariant lattice. -/
noncomputable def coinvariantLatticeInclusion (L : IntegralLatticeCat R)
    [Module.Finite R L.obj.carrier] (J : Involution L) :
    coinvariantLattice L J ⟶ L := by
  letI : Module.Projective R (coinvariantSubmodule L J) :=
    coinvariantSubmodule_projective L J
  exact formedSublatticeInclusion L (coinvariantSubmodule L J)

end PID

end LeanCategories.Lattices.Valued
