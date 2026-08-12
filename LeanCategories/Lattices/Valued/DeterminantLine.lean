/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Lattices.Valued.Arithmetic
public import Mathlib.Algebra.Category.ModuleCat.ExteriorPower
public import Mathlib.RingTheory.PicardGroup

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

/-- The top exterior power of the value dual, in the rank of the lattice carrier. -/
noncomputable def determinantDualLine (L : FiniteProjectiveLatticeCat R R) : ModuleCat R :=
  (ModuleCat.of R L.obj.obj.valueDual).exteriorPower L.genericRank

/-- The determinant of the adjoint map. This is intrinsic and uses no basis. -/
noncomputable def determinantAdjoint (L : FiniteProjectiveLatticeCat R R) :
    L.determinantLine ⟶ L.determinantDualLine :=
  (ModuleCat.exteriorPower.functor R L.genericRank).map
    (ModuleCat.ofHom L.obj.obj.adjoint)

/-- The determinant-level cokernel of the adjoint map. -/
abbrev discriminantLineCokernel (L : FiniteProjectiveLatticeCat R R) :=
  L.determinantDualLine ⧸ LinearMap.range L.determinantAdjoint.hom

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

/-- The Steinitz class is the Picard class of the determinant line. -/
noncomputable def steinitzClass (L : FiniteProjectiveLatticeCat R W)
    [Module.Invertible R L.determinantLine] : CommRing.Pic R :=
  CommRing.Pic.mk R L.determinantLine

/-- The Steinitz class is invariant under lattice isomorphism. -/
theorem steinitzClass_eq_of_iso {L M : FiniteProjectiveLatticeCat R W}
    [Module.Invertible R L.determinantLine]
    [Module.Invertible R M.determinantLine]
    (e : L ≅ M) : L.steinitzClass = M.steinitzClass := by
  rw [steinitzClass, steinitzClass, CommRing.Pic.mk_eq_mk_iff]
  exact ⟨(determinantLineIso e).toLinearEquiv⟩

end FiniteProjectiveLatticeCat

end LeanCategories.Lattices.Valued
