/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Lattices.Valued.Arithmetic
public import LeanCategories.Lattices.Valued.BaseChange

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

/-- Isometry in the lattice subcategory is equivalent to isometry of the formed modules. -/
theorem isIsomorphic_integralLattice_iff_bilin (L M : IntegralLatticeCat R) :
    IsIsomorphic L M ↔ IsIsomorphic L.obj M.obj := by
  constructor
  · rintro ⟨i⟩
    exact ⟨(isLattice R R).ι.mapIso i⟩
  · rintro ⟨i⟩
    exact ⟨ObjectProperty.isoMk (P := isLattice R R) i⟩

local instance ringEquivInvPair (e : R ≃+* S) :
    RingHomInvPair e.toRingHom e.symm.toRingHom :=
  ⟨by ext; simp, by ext; simp⟩

/-- A compatible equivalence of coefficient algebras as a semilinear equivalence. -/
def compatibleAlgebraSemilinearEquiv
    {A B : Type u} [CommRing A] [CommRing B] [Algebra R A] [Algebra S B]
    (e : R ≃+* S) (f : A ≃+* B)
    (h : ∀ r, f (algebraMap R A r) = algebraMap S B (e r)) :
    A ≃ₛₗ[e.toRingHom] B where
  __ := f.toEquiv
  map_add' := f.map_add
  map_smul' r a := by
    simp only [Algebra.smul_def]
    exact (f.map_mul _ _).trans (congrArg (· * f a) (h r))

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

/-- Tensor products commute with compatible semilinear equivalences. -/
noncomputable def tensorProductSemilinearEquiv
    {A B : Type u} [CommRing A] [CommRing B] [Algebra R A] [Algebra S B]
    (e : R ≃+* S) (f : A ≃+* B)
    (h : ∀ r, f (algebraMap R A r) = algebraMap S B (e r))
    {M N : Type u} [AddCommGroup M] [AddCommGroup N] [Module R M] [Module S N]
    (g : M ≃ₛₗ[e.toRingHom] N) :
    letI : Module B (TensorProduct R A M) := Module.compHom _ f.symm.toRingHom
    TensorProduct R A M ≃ₗ[B] TensorProduct S B N := by
  letI : Module B (TensorProduct R A M) := Module.compHom _ f.symm.toRingHom
  let t := TensorProduct.congr (compatibleAlgebraSemilinearEquiv e f h) g
  exact LinearEquiv.ofBijective
    { toFun := t
      map_add' := t.map_add
      map_smul' := by
        intro b x
        induction x using TensorProduct.induction_on with
        | zero => simp
        | tmul a m =>
            change t ((f.symm b * a) ⊗ₜ[R] m) = b • t (a ⊗ₜ[R] m)
            rw [show t ((f.symm b * a) ⊗ₜ[R] m) =
                f (f.symm b * a) ⊗ₜ[S] g m from rfl,
              show t (a ⊗ₜ[R] m) = f a ⊗ₜ[S] g m from rfl,
              f.map_mul, f.apply_symm_apply, TensorProduct.smul_tmul']
            rfl
        | add x y hx hy => simp only [smul_add, map_add, hx, hy] }
    t.bijective

@[simp]
theorem tensorProductSemilinearEquiv_tmul
    {A B : Type u} [CommRing A] [CommRing B] [Algebra R A] [Algebra S B]
    (e : R ≃+* S) (f : A ≃+* B)
    (h : ∀ r, f (algebraMap R A r) = algebraMap S B (e r))
    {M N : Type u} [AddCommGroup M] [AddCommGroup N] [Module R M] [Module S N]
    (g : M ≃ₛₗ[e.toRingHom] N) (a : A) (m : M) :
    letI : Module B (TensorProduct R A M) := Module.compHom _ f.symm.toRingHom
    tensorProductSemilinearEquiv e f h g (a ⊗ₜ[R] m) =
      f a ⊗ₜ[S] g m :=
  rfl

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

@[simp]
theorem transportIntegralBilin_smul (e : R ≃+* S) (L : BilinModuleCat R R)
    (s : S) (x : L.carrier) :
    (show L.carrier from
      s • (show (transportIntegralBilin e L).carrier from x)) = e.symm s • x :=
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

/-- Transport along a ring equivalence preserves and reflects formed-module isometry. -/
theorem isIsomorphic_transportIntegralBilin_iff (e : R ≃+* S)
    (L M : BilinModuleCat R R) :
    IsIsomorphic (transportIntegralBilin e L) (transportIntegralBilin e M) ↔
      IsIsomorphic L M := by
  constructor
  · rintro ⟨i⟩
    let g := BilinModuleCat.linearEquivOfIso i
    let f : L.carrier ≃ₗ[R] M.carrier :=
      { toFun := fun x ↦ show M.carrier from g x
        invFun := fun x ↦ show L.carrier from g.symm x
        left_inv := fun x ↦ g.symm_apply_apply x
        right_inv := fun x ↦ g.apply_symm_apply x
        map_add' := g.map_add
        map_smul' := fun r x ↦ by
          change (show M.carrier from
              g (show (transportIntegralBilin e L).carrier from r • x)) =
            r • (show M.carrier from
              g (show (transportIntegralBilin e L).carrier from x))
          have hx : (show (transportIntegralBilin e L).carrier from r • x) =
              e r • (show (transportIntegralBilin e L).carrier from x) := by
            change r • x = e.symm (e r) • x
            simp
          rw [hx]
          rw [g.map_smul]
          change e.symm (e r) • (show M.carrier from g x) =
            r • (show M.carrier from g x)
          simp }
    exact ⟨BilinModuleCat.isoMk f fun x y ↦ by
      apply e.injective
      change e (M.pairing (g x) (g y)) = e (L.pairing x y)
      simpa only [transportIntegralBilin_pairing] using
        BilinModuleCat.linearEquivOfIso_pairing i x y⟩
  · rintro ⟨i⟩
    exact ⟨(transportIntegralBilinFunctor e).mapIso i⟩

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

/-- The carrier of a transported lattice is semilinearly equivalent to the original carrier. -/
noncomputable def transportIntegralLatticeSemilinearEquiv (e : R ≃+* S)
    (L : IntegralLatticeCat R) :
    L.obj.carrier ≃ₛₗ[e.toRingHom] ((transportIntegralLattice e).obj L).obj.carrier := by
  change L.obj.carrier ≃ₛₗ[e.toRingHom] (transportIntegralBilin e L.obj).carrier
  exact moduleTransportSemilinearEquiv e L.obj.carrier

/-- Base change commutes with transport along compatible ring equivalences. -/
noncomputable def baseChangeTransportLinearEquiv
    {A B : Type u} [CommRing A] [CommRing B] [Algebra R A] [Algebra S B]
    (e : R ≃+* S) (f : A ≃+* B)
    (h : ∀ r, f (algebraMap R A r) = algebraMap S B (e r))
    (L : IntegralLatticeCat R) :
    letI : Module B (TensorProduct R A L.obj.carrier) :=
      Module.compHom _ f.symm.toRingHom
    TensorProduct R A L.obj.carrier ≃ₗ[B]
      TensorProduct S B ((transportIntegralLattice e).obj L).obj.carrier :=
  tensorProductSemilinearEquiv e f h (transportIntegralLatticeSemilinearEquiv e L)

@[simp]
theorem baseChangeTransportLinearEquiv_tmul
    {A B : Type u} [CommRing A] [CommRing B] [Algebra R A] [Algebra S B]
    (e : R ≃+* S) (f : A ≃+* B)
    (h : ∀ r, f (algebraMap R A r) = algebraMap S B (e r))
    (L : IntegralLatticeCat R) (a : A) (x : L.obj.carrier) :
    letI : Module B (TensorProduct R A L.obj.carrier) :=
      Module.compHom _ f.symm.toRingHom
    baseChangeTransportLinearEquiv e f h L (a ⊗ₜ[R] x) =
      f a ⊗ₜ[S] (transportIntegralLatticeSemilinearEquiv e L x) :=
  rfl

/-- The tensor comparison preserves a scalar-extended integral form. -/
theorem baseChangeTransportLinearEquiv_pairing
    {A B : Type u} [CommRing A] [CommRing B] [Algebra R A] [Algebra S B]
    (e : R ≃+* S) (f : A ≃+* B)
    (h : ∀ r, f (algebraMap R A r) = algebraMap S B (e r))
    (L : IntegralLatticeCat R) :
    letI : Module B (TensorProduct R A L.obj.carrier) :=
      Module.compHom _ f.symm.toRingHom
    ∀ x y : TensorProduct R A L.obj.carrier,
    ((baseChangeIntegral S B).obj ((transportIntegralLattice e).obj L)).obj.pairing
        (baseChangeTransportLinearEquiv e f h L x)
        (baseChangeTransportLinearEquiv e f h L y) =
      f (baseChangeIntegralBilinMap R A L x y) := by
  letI : Module B (TensorProduct R A L.obj.carrier) :=
    Module.compHom _ f.symm.toRingHom
  intro x y
  rw [← baseChangeIntegralBilinMap_apply]
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul b y =>
          rw [baseChangeTransportLinearEquiv_tmul, baseChangeTransportLinearEquiv_tmul,
            baseChangeIntegralBilinMap_tmul, baseChangeIntegralBilinMap_tmul]
          change f a * f b * algebraMap S B (e (L.obj.pairing x y)) =
            f (a * b * algebraMap R A (L.obj.pairing x y))
          simp [h]
      | add y₁ y₂ hy₁ hy₂ =>
          simpa only [map_add, f.map_add] using congrArg₂ (· + ·) hy₁ hy₂
  | add x₁ x₂ hx₁ hx₂ =>
      rw [map_add, map_add]
      change
        baseChangeIntegralBilinMap S B ((transportIntegralLattice e).obj L)
              (baseChangeTransportLinearEquiv e f h L x₁)
              (baseChangeTransportLinearEquiv e f h L y) +
            baseChangeIntegralBilinMap S B ((transportIntegralLattice e).obj L)
              (baseChangeTransportLinearEquiv e f h L x₂)
              (baseChangeTransportLinearEquiv e f h L y) =
          f (baseChangeIntegralBilinMap R A L (x₁ + x₂) y)
      rw [map_add]
      change _ = f (baseChangeIntegralBilinMap R A L x₁ y +
        baseChangeIntegralBilinMap R A L x₂ y)
      rw [hx₁, hx₂, f.map_add]

/-- Scalar extension of a transported lattice agrees with transport of scalar extension. -/
noncomputable def baseChangeTransportBilinIso
    {A B : Type u} [CommRing A] [CommRing B] [Algebra R A] [Algebra S B]
    (e : R ≃+* S) (f : A ≃+* B)
    (h : ∀ r, f (algebraMap R A r) = algebraMap S B (e r))
    (L : IntegralLatticeCat R) :
    transportIntegralBilin f ((baseChangeIntegral R A).obj L).obj ≅
      ((baseChangeIntegral S B).obj ((transportIntegralLattice e).obj L)).obj :=
  BilinModuleCat.isoMk (baseChangeTransportLinearEquiv e f h L)
    (baseChangeTransportLinearEquiv_pairing e f h L)

/-- Compatible changes of the base ring and coefficient ring preserve and reflect isometry. -/
theorem isIsomorphic_baseChange_transport_iff
    {A B : Type u} [CommRing A] [CommRing B] [Algebra R A] [Algebra S B]
    (e : R ≃+* S) (f : A ≃+* B)
    (h : ∀ r, f (algebraMap R A r) = algebraMap S B (e r))
    (L M : IntegralLatticeCat R) :
    IsIsomorphic ((baseChangeIntegral R A).obj L)
        ((baseChangeIntegral R A).obj M) ↔
      IsIsomorphic ((baseChangeIntegral S B).obj ((transportIntegralLattice e).obj L))
        ((baseChangeIntegral S B).obj ((transportIntegralLattice e).obj M)) := by
  let cL : (transportIntegralLattice f).obj ((baseChangeIntegral R A).obj L) ≅
      (baseChangeIntegral S B).obj ((transportIntegralLattice e).obj L) :=
    ObjectProperty.isoMk (P := isLattice B B) (baseChangeTransportBilinIso e f h L)
  let cM : (transportIntegralLattice f).obj ((baseChangeIntegral R A).obj M) ≅
      (baseChangeIntegral S B).obj ((transportIntegralLattice e).obj M) :=
    ObjectProperty.isoMk (P := isLattice B B) (baseChangeTransportBilinIso e f h M)
  constructor
  · rintro ⟨i⟩
    exact ⟨cL.symm ≪≫ (transportIntegralLattice f).mapIso i ≪≫ cM⟩
  · rintro ⟨i⟩
    have transported : IsIsomorphic
        (transportIntegralBilin f ((baseChangeIntegral R A).obj L).obj)
          (transportIntegralBilin f ((baseChangeIntegral R A).obj M).obj) :=
      ⟨((isLattice B B).ι.mapIso (cL ≪≫ i ≪≫ cM.symm))⟩
    have source := (isIsomorphic_transportIntegralBilin_iff f
      ((baseChangeIntegral R A).obj L).obj
      ((baseChangeIntegral R A).obj M).obj).mp transported
    obtain ⟨sourceIso⟩ := source
    exact ⟨ObjectProperty.isoMk (P := isLattice A A) sourceIso⟩

end LeanCategories.Lattices.Valued
