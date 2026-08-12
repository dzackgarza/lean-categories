/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Lattices.Valued.Arithmetic
public import Mathlib.Algebra.Category.ModuleCat.ExteriorPower

/-!
# Determinant lines of finite projective lattices

The determinant line is the top exterior power of the carrier. Over a domain, the rank is
the rank at the generic point of the prime spectrum. This definition does not choose a basis.
-/

@[expose] public section

open CategoryTheory

namespace LeanCategories.Lattices.Valued

universe u

variable {R W : Type u} [CommRing R] [IsDomain R]
variable [AddCommGroup W] [Module R W]

namespace FiniteProjectiveLatticeCat

/-- The rank of a finite projective lattice at the generic point of an integral spectrum. -/
noncomputable def genericRank (L : FiniteProjectiveLatticeCat R W) : ℕ :=
  L.localRank ⊥

/-- A finite projective lattice over a domain has its generic rank at every prime. -/
theorem localRank_eq_genericRank (L : FiniteProjectiveLatticeCat R W)
    (p : PrimeSpectrum R) : L.localRank p = L.genericRank := by
  letI : Module.Finite R L.obj.obj.carrier := L.property
  letI : Module.Projective R L.obj.obj.carrier := L.obj.property.1
  exact (Module.rankAtStalk_eq_of_le_of_finite_of_flat
    L.obj.obj.carrier bot_le).symm

/-- The determinant line of a finite projective lattice is its top exterior power. -/
noncomputable def determinantLine (L : FiniteProjectiveLatticeCat R W) : ModuleCat R :=
  ((finiteProjectiveForget R W).obj L).exteriorPower L.genericRank

/-- An isomorphism of lattices induces an isomorphism of their determinant lines. -/
noncomputable def determinantLineIso {L M : FiniteProjectiveLatticeCat R W}
    (e : L ≅ M) : L.determinantLine ≅ M.determinantLine := by
  have hr : L.genericRank = M.genericRank := by
    unfold genericRank
    exact congrFun (Module.rankAtStalk_eq_of_equiv
      ((finiteProjectiveForget R W).mapIso e).toLinearEquiv) ⊥
  rw [determinantLine, determinantLine, hr]
  exact (ModuleCat.exteriorPower.functor R M.genericRank).mapIso
      ((finiteProjectiveForget R W).mapIso e)

end FiniteProjectiveLatticeCat

end LeanCategories.Lattices.Valued
