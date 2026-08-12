/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Lattices.Valued.Arithmetic

/-!
# Transport of integral lattices along ring equivalences

This file lifts Mathlib's restriction-of-scalars equivalence for module categories to
integral formed lattices. The carrier does not change. The scalar action and form values
move through the ring equivalence.
-/

@[expose] public section

open CategoryTheory
open LeanCategories.Modules.Bilinear.Valued

namespace LeanCategories.Lattices.Valued

universe u

variable {R S : Type u} [CommRing R] [CommRing S]

local instance ringEquivInvPair (e : R ≃+* S) :
    RingHomInvPair e.toRingHom e.symm.toRingHom :=
  ⟨by ext; simp, by ext; simp⟩

/-- A module is semilinearly equivalent to its transport along a ring equivalence. -/
def moduleTransportSemilinearEquiv (e : R ≃+* S)
    (M : Type u) [AddCommGroup M] [Module R M] :
    letI : Module S M := Module.compHom M e.symm.toRingHom
    M ≃ₛₗ[e.toRingHom] M := by
  letI : Module S M := Module.compHom M e.symm.toRingHom
  exact
    { Equiv.refl M with
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun r x ↦ by
        change r • x = e.symm (e r) • x
        exact congrArg (fun q : R ↦ q • x) (e.symm_apply_apply r).symm }

/-- Transport an integral formed module along a ring equivalence. -/
def transportIntegralBilin (e : R ≃+* S) (L : BilinModuleCat R R) :
    BilinModuleCat S S := by
  letI : Module S L.carrier := Module.compHom L.carrier e.symm.toRingHom
  let B : LinearMap.BilinMap S L.carrier S :=
    { toFun := fun x ↦
        { toFun := fun y ↦ e (L.pairing x y)
          map_add' := fun y z ↦ by simp
          map_smul' := fun s y ↦ by
            change e (L.pairing x (e.symm s • y)) = s * e (L.pairing x y)
            simp [BilinModuleCat.pairing_smul_right] }
      map_add' := fun x y ↦ by
        ext z
        simp
      map_smul' := fun s x ↦ by
        ext y
        change e (L.pairing (e.symm s • x) y) = s * e (L.pairing x y)
        simp [BilinModuleCat.pairing_smul_left] }
  exact BilinModuleCat.ofBilinMap B

@[simp]
theorem transportIntegralBilin_pairing (e : R ≃+* S) (L : BilinModuleCat R R)
    (x y : (transportIntegralBilin e L).carrier) :
    (transportIntegralBilin e L).pairing x y = e (L.pairing x y) := by
  rfl

/-- Transport a formed-module morphism along a ring equivalence. -/
def transportIntegralBilinMap (e : R ≃+* S) {L M : BilinModuleCat R R}
    (f : L ⟶ M) : transportIntegralBilin e L ⟶ transportIntegralBilin e M := by
  let map : (transportIntegralBilin e L).carrier →ₗ[S]
      (transportIntegralBilin e M).carrier :=
    { toFun := fun x ↦ BilinModuleCat.underlyingMap f x
      map_add' := fun x y ↦ map_add (BilinModuleCat.underlyingMap f) x y
      map_smul' := fun s x ↦ by
        change BilinModuleCat.underlyingMap f
            (e.symm s • (show L.carrier from x)) =
          e.symm s • BilinModuleCat.underlyingMap f (show L.carrier from x)
        exact (BilinModuleCat.underlyingMap f).map_smul (e.symm s) x }
  exact BilinModuleCat.homMk map fun x y ↦ by
    simp only [transportIntegralBilin_pairing]
    change e (M.pairing
      (BilinModuleCat.underlyingMap f (x : L.carrier))
      (BilinModuleCat.underlyingMap f (y : L.carrier))) = e (L.pairing x y)
    rw [BilinModuleCat.map_pairing]

/-- Transport integral formed modules along a ring equivalence. -/
def transportIntegralBilinFunctor (e : R ≃+* S) :
    BilinModuleCat R R ⥤ BilinModuleCat S S where
  obj := transportIntegralBilin e
  map := transportIntegralBilinMap e
  map_id L := by
    apply Quiver.Hom.unop_inj
    apply CategoryOfElements.ext
    apply Quiver.Hom.unop_inj
    apply ModuleCat.hom_ext
    ext x
    rfl
  map_comp f g := by
    apply Quiver.Hom.unop_inj
    apply CategoryOfElements.ext
    apply Quiver.Hom.unop_inj
    apply ModuleCat.hom_ext
    ext x
    rfl

/-- Transport integral lattices along a ring equivalence. -/
noncomputable def transportIntegralLattice (e : R ≃+* S) :
    IntegralLatticeCat R ⥤ IntegralLatticeCat S where
  obj L := by
    letI : Module.Projective R L.obj.carrier := L.property.1
    letI : Module S L.obj.carrier := Module.compHom L.obj.carrier e.symm.toRingHom
    letI : Module.Projective S L.obj.carrier :=
      Module.Projective.of_equiv
        (R := R) (S := S) (M := L.obj.carrier) (N := L.obj.carrier)
        (moduleTransportSemilinearEquiv e L.obj.carrier)
    refine ⟨transportIntegralBilin e L.obj, ?_⟩
    constructor
    · change Module.Projective S L.obj.carrier
      infer_instance
    · intro x y
      simp [L.property.2 x y]
  map f := ObjectProperty.homMk (transportIntegralBilinMap e f.hom)
  map_id L := by
    apply ObjectProperty.hom_ext
    exact (transportIntegralBilinFunctor e).map_id L.obj
  map_comp f g := by
    apply ObjectProperty.hom_ext
    exact (transportIntegralBilinFunctor e).map_comp f.hom g.hom

/-- Transport finite projective integral lattices along a ring equivalence. -/
noncomputable def transportFiniteProjectiveLattice (e : R ≃+* S) :
    FiniteProjectiveLatticeCat R R ⥤ FiniteProjectiveLatticeCat S S where
  obj L := by
    letI : Module.Finite R L.obj.obj.carrier := L.property
    letI : Module S L.obj.obj.carrier := Module.compHom L.obj.obj.carrier e.symm.toRingHom
    let se := moduleTransportSemilinearEquiv e L.obj.obj.carrier
    letI : Module.Finite S L.obj.obj.carrier :=
      Module.Finite.of_surjective
        (R := R) (S := S) (M := L.obj.obj.carrier) (P := L.obj.obj.carrier)
        (σ := e.toRingHom)
        (moduleTransportSemilinearEquiv e L.obj.obj.carrier)
        (moduleTransportSemilinearEquiv e L.obj.obj.carrier).surjective
    refine ⟨(transportIntegralLattice e).obj L.obj, ?_⟩
    change Module.Finite S L.obj.obj.carrier
    infer_instance
  map f := ObjectProperty.homMk ((transportIntegralLattice e).map f.hom)
  map_id L := by
    apply ObjectProperty.hom_ext
    exact (transportIntegralLattice e).map_id L.obj
  map_comp f g := by
    apply ObjectProperty.hom_ext
    exact (transportIntegralLattice e).map_comp f.hom g.hom

end LeanCategories.Lattices.Valued
