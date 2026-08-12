/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Lattices.Valued.Arithmetic
public import LeanCategories.Lattices.Valued.DiscriminantFunctor
public import Mathlib.Algebra.Category.ModuleCat.ExteriorPower
public import Mathlib.RingTheory.PicardGroup
public import Mathlib.RingTheory.Ideal.Maps

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

/-- The intrinsic discriminant ideal is the annihilator of the determinant-line cokernel. -/
noncomputable def intrinsicDiscriminantIdeal
    (L : FiniteProjectiveLatticeCat R R) : Ideal R :=
  Module.annihilator R L.discriminantLineCokernel

/-- The intrinsic discriminant ideal is trivial exactly when the determinant adjoint is
surjective. -/
theorem intrinsicDiscriminantIdeal_eq_top_iff
    (L : FiniteProjectiveLatticeCat R R) :
    L.intrinsicDiscriminantIdeal = ⊤ ↔
      Function.Surjective L.determinantAdjoint.hom := by
  rw [intrinsicDiscriminantIdeal, Module.annihilator_eq_top_iff]
  constructor
  · intro h y
    have hy : (Submodule.Quotient.mk y : L.discriminantLineCokernel) = 0 :=
      Subsingleton.elim _ _
    exact LinearMap.mem_range.mp <| (Submodule.Quotient.mk_eq_zero _).mp hy
  · intro h
    have hz (x : L.discriminantLineCokernel) : x = 0 := by
      refine Quotient.inductionOn' x fun y => ?_
      exact (Submodule.Quotient.mk_eq_zero _).mpr <|
        LinearMap.mem_range.mpr (h y)
    exact ⟨fun x y => (hz x).trans (hz y).symm⟩

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

/-- Forget the finite-projective property on an isomorphism of lattices. -/
private noncomputable def integralLatticeIso
    {L M : FiniteProjectiveLatticeCat R R} (e : L ≅ M) : L.obj ≅ M.obj :=
  (ObjectProperty.ι (isFiniteProjectiveLattice R R)).mapIso e

omit [IsDomain R] in
/-- The carrier and contragredient maps commute with the adjoint maps. -/
private theorem adjoint_naturality
    {L M : FiniteProjectiveLatticeCat R R} (e : L ≅ M) :
    ModuleCat.ofHom L.obj.obj.adjoint ≫
        (discriminantValueDualEquiv (integralLatticeIso e)).toModuleIso.hom =
      ((finiteProjectiveForget R R).mapIso e).hom ≫
        ModuleCat.ofHom M.obj.obj.adjoint := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact discriminantValueDualEquiv_adjoint (integralLatticeIso e) x

/-- The intrinsic discriminant ideal is invariant under lattice isomorphism. -/
theorem intrinsicDiscriminantIdeal_eq_of_iso
    {L M : FiniteProjectiveLatticeCat R R} (e : L ≅ M) :
    L.intrinsicDiscriminantIdeal = M.intrinsicDiscriminantIdeal := by
  unfold intrinsicDiscriminantIdeal discriminantLineCokernel
  unfold determinantDualLine determinantAdjoint determinantLine
  have hr : M.genericRank = L.genericRank := by
    unfold genericRank
    exact (congrFun (Module.rankAtStalk_eq_of_equiv
      ((finiteProjectiveForget R R).mapIso e).toLinearEquiv) ⊥).symm
  rw [hr]
  let F := ModuleCat.exteriorPower.functor R L.genericRank
  let carrierE := F.mapIso ((finiteProjectiveForget R R).mapIso e)
  let dualE := F.mapIso
    (discriminantValueDualEquiv (integralLatticeIso e)).toModuleIso
  have hsquare :
      F.map (ModuleCat.ofHom L.obj.obj.adjoint) ≫ dualE.hom =
        carrierE.hom ≫ F.map (ModuleCat.ofHom M.obj.obj.adjoint) := by
    change F.map (ModuleCat.ofHom L.obj.obj.adjoint) ≫
        F.map (discriminantValueDualEquiv (integralLatticeIso e)).toModuleIso.hom =
      F.map ((finiteProjectiveForget R R).mapIso e).hom ≫
        F.map (ModuleCat.ofHom M.obj.obj.adjoint)
    rw [← F.map_comp, ← F.map_comp]
    exact congrArg F.map (adjoint_naturality e)
  have hrange :
      (LinearMap.range (F.map (ModuleCat.ofHom L.obj.obj.adjoint)).hom).map
          dualE.toLinearEquiv.toLinearMap =
        LinearMap.range (F.map (ModuleCat.ofHom M.obj.obj.adjoint)).hom := by
    ext y
    constructor
    · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
      refine ⟨carrierE.toLinearEquiv x, ?_⟩
      exact (ConcreteCategory.congr_hom hsquare x).symm
    · rintro ⟨y, rfl⟩
      refine ⟨(F.map (ModuleCat.ofHom L.obj.obj.adjoint)).hom
          (carrierE.toLinearEquiv.symm y), ⟨carrierE.toLinearEquiv.symm y, rfl⟩, ?_⟩
      calc
        dualE.toLinearEquiv
            ((F.map (ModuleCat.ofHom L.obj.obj.adjoint)).hom
              (carrierE.toLinearEquiv.symm y)) =
            (F.map (ModuleCat.ofHom M.obj.obj.adjoint)).hom
              (carrierE.toLinearEquiv (carrierE.toLinearEquiv.symm y)) :=
          ConcreteCategory.congr_hom hsquare
            (carrierE.toLinearEquiv.symm y)
        _ = (F.map (ModuleCat.ofHom M.obj.obj.adjoint)).hom y := by simp
  exact (Submodule.Quotient.equiv _ _ dualE.toLinearEquiv hrange).annihilator_eq

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
