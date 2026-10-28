/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Catalogue.Semantics.Modules.LinearMaps
public import LeanCategories.Catalogue.Semantics.Modules.IntegerResidueModules
public import LeanCategories.Catalogue.Semantics.Modules.Operations
public meta import LeanCategories.Catalogue.Semantics.Modules.LinearMaps

@[expose] public section

open CategoryTheory
open CasCatalogue.Modules.CatalogueRegistration
open CasCatalogue.Modules.LinearMaps

namespace CasCatalogue.Modules.LinearMapsTests

universe u v

/-- Forgetting commutativity keeps the original scalar action and its whole
linearity law, at any chosen module and scalar. -/
example (K : CommRingCat.{u})
    (M : ModuleCat.{v} ((forget₂ CommRingCat RingCat).obj K)) (a : K) :
    IsLinearMap ((forget₂ CommRingCat RingCat).obj K)
      (M := M) (M₂ := M) (fun x : M => (M.smul a).hom x) := by
  run_tac linearEvidence

/-- The published reindexing family and uncurried scalar-action map retain the
same selected module, even when the scalar ring is a forgotten commutative ring. -/
example (K : CommRingCat.{0}) (S : RingCat.{0})
    (q : (forget₂ CommRingCat RingCat).obj K ⟶ S) (N : ModuleCat.{0} S) (a : K) :
    let R := (forget₂ CommRingCat RingCat).obj K
    let M : ModuleCat.{0} R := (modulesFamilyRealization.reindex q).obj N
    IsLinearMap R (M := M) (M₂ := M) (fun x : M =>
      ConcreteCategory.hom (C := Type) (Operations.scalarAction R M) (a, x)) := by
  run_tac linearEvidence

/-- For every modulus, including zero, the named coefficient map gives the
actual integer action on the restricted regular module. No scalar or element
is fixed to a sample value. -/
example (n : ℕ) (a : ℤ) :
    let R := (forget₂ CommRingCat RingCat).obj Algebra.NamedCommutativeRings.integers
    let S := (forget₂ CommRingCat RingCat).obj (Algebra.NamedCommutativeRings.integersMod n)
    let q : R ⟶ S := (forget₂ CommRingCat RingCat).map
      (Algebra.NamedCommutativeRings.integerCoefficients
        (Algebra.NamedCommutativeRings.integersMod n))
    let M : ModuleCat.{0} R := (modulesFamilyRealization.reindex q).obj (regularModule S)
    IsLinearMap R (M := M) (M₂ := M) (fun x : M =>
      ConcreteCategory.hom (C := Type) (Operations.scalarAction R M) (a, x)) := by
  run_tac linearEvidence

/-- The regular action itself is linear over the selected commutative residue
ring, uniformly in the modulus and scalar. -/
example (n : ℕ) (a : ZMod n) :
    let S := (forget₂ CommRingCat RingCat).obj (Algebra.NamedCommutativeRings.integersMod n)
    let N := regularModule S
    IsLinearMap S (M := N) (M₂ := N) (fun x : N => (N.smul a).hom x) := by
  run_tac linearEvidence

/-- An arbitrary reindexed morphism keeps its full laws when presented through
the ordinary forgetful functor to sets and its underlying function. -/
example (R S : RingCat.{u}) (q : R ⟶ S) (N P : ModuleCat.{v} S) (f : N ⟶ P) :
    let M : ModuleCat.{v} R := (modulesFamilyRealization.reindex q).obj N
    let M' : ModuleCat.{v} R := (modulesFamilyRealization.reindex q).obj P
    let g : M ⟶ M' := (modulesFamilyRealization.reindex q).map f
    IsLinearMap R (M := M) (M₂ := M') (fun x : M =>
      ConcreteCategory.hom (C := Type v) ((forget (ModuleCat R)).map g) x) := by
  run_tac linearEvidence

/-- The named coefficient presentation also preserves every whole regular
module morphism under reindexing; its original scalar-linear function is kept. -/
example (n : ℕ)
    (f : regularModule (RingCat.of (ZMod n)) ⟶ regularModule (RingCat.of (ZMod n))) :
    let R := (forget₂ CommRingCat RingCat).obj Algebra.NamedCommutativeRings.integers
    let S := (forget₂ CommRingCat RingCat).obj (Algebra.NamedCommutativeRings.integersMod n)
    let q : R ⟶ S := (forget₂ CommRingCat RingCat).map
      (Algebra.NamedCommutativeRings.integerCoefficients
        (Algebra.NamedCommutativeRings.integersMod n))
    let M : ModuleCat.{0} R := (modulesFamilyRealization.reindex q).obj (regularModule S)
    IsLinearMap R (M := M) (M₂ := M)
      (fun x : M => ((modulesFamilyRealization.reindex q).map f).hom x) := by
  run_tac linearEvidence

/-- Two restrictions of the same regular module have the same carrier. Their
identity function can be linear only when the selected base maps are equal. -/
theorem different_restrictions_identity_not_linear (R S : RingCat.{u})
    (q₀ q₁ : R ⟶ S) (different : q₀ ≠ q₁) :
    let M := (ModuleCat.restrictScalars q₀.hom).obj (regularModule S)
    let N := (ModuleCat.restrictScalars q₁.hom).obj (regularModule S)
    ¬ IsLinearMap R (M := M) (M₂ := N) (fun x : M => (show N from x)) := by
  dsimp only
  intro h
  apply different
  apply RingCat.hom_ext
  apply RingHom.ext
  intro r
  have sameAction := h.map_smul r (1 : S)
  change q₀.hom r * 1 = q₁.hom r * 1 at sameAction
  simpa only [mul_one] using sameAction

/-- Definitional comparison must not equate distinct selected actions merely
because their carriers are definitionally equal. -/
example (R S : RingCat.{u}) (q₀ q₁ : R ⟶ S) (_different : q₀ ≠ q₁) : True := by
  fail_if_success
    have :
        let M := (ModuleCat.restrictScalars q₀.hom).obj (regularModule S)
        let N := (ModuleCat.restrictScalars q₁.hom).obj (regularModule S)
        IsLinearMap R (M := M) (M₂ := N) (fun x : M => (show N from x)) := by
      run_tac linearEvidence
  trivial

/-- The admission laws apply to arbitrary modules over arbitrary rings. -/
example (R : RingCat.{u}) (M : ModuleCat.{v} R) :
    IsLinearMap R (fun x : M => x + x) := by
  run_tac linearEvidence

/-- Actual morphisms retain their full linearity after forgetting to functions. -/
example (R : RingCat.{u}) (M N : ModuleCat.{v} R) (f : M ⟶ N) :
    IsLinearMap R (fun x : M => f.hom x) := by
  run_tac linearEvidence

/-- The regular-module scalar formula admits the whole nonidentity morphism. -/
theorem regular_double_linear :
    IsLinearMap (RingCat.of (ZMod 5))
      (fun x : regularModule (RingCat.of (ZMod 5)) =>
        ConcreteCategory.hom (C := Type)
          (Operations.scalarAction (RingCat.of (ZMod 5))
            (regularModule (RingCat.of (ZMod 5)))) ((2 : ZMod 5), x)) := by
  run_tac linearEvidence

/-- Admission bundles the exact familiar linear map, not merely its carrier. -/
theorem regular_double_admission :
    ConcreteCategory.hom (C := Type)
      (admitLinear (RingCat.of (ZMod 5))
        (regularModule (RingCat.of (ZMod 5))) (regularModule (RingCat.of (ZMod 5)))
        (fun x => ConcreteCategory.hom (C := Type)
          (Operations.scalarAction (RingCat.of (ZMod 5))
            (regularModule (RingCat.of (ZMod 5)))) ((2 : ZMod 5), x))
        regular_double_linear) PUnit.unit =
      ModuleCat.ofHom (X := regularModule (RingCat.of (ZMod 5)))
        (Y := regularModule (RingCat.of (ZMod 5)))
        ((2 : ZMod 5) • (LinearMap.id : ZMod 5 →ₗ[ZMod 5] ZMod 5)) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rfl

/-- Restriction of scalars uses its actual integer action on the same residues. -/
theorem restricted_double_linear :
    IsLinearMap (RingCat.of ℤ)
      (fun x : IntegerResidueModules.integerResidueModule 5 =>
        ConcreteCategory.hom (C := Type)
          (Operations.scalarAction (RingCat.of ℤ)
            (IntegerResidueModules.integerResidueModule 5)) ((2 : ℤ), x)) := by
  run_tac linearEvidence

/-- The corresponding whole map remains the previously specified restriction. -/
theorem restricted_double_admission :
    ConcreteCategory.hom (C := Type)
      (admitLinear (RingCat.of ℤ)
        (IntegerResidueModules.integerResidueModule 5)
        (IntegerResidueModules.integerResidueModule 5)
        (fun x => ConcreteCategory.hom (C := Type)
          (Operations.scalarAction (RingCat.of ℤ)
            (IntegerResidueModules.integerResidueModule 5)) ((2 : ℤ), x))
        restricted_double_linear) PUnit.unit =
      (modulesFamilyRealization.reindex
        (RingCat.ofHom (Int.castRingHom (ZMod 5)))).map
        (ModuleCat.ofHom (X := regularModule (RingCat.of (ZMod 5)))
          (Y := regularModule (RingCat.of (ZMod 5)))
          ((2 : ZMod 5) • (LinearMap.id : ZMod 5 →ₗ[ZMod 5] ZMod 5))) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rfl

/-- A nearby affine function is not admitted as a linear map. -/
theorem translation_not_linear : ¬ IsLinearMap ℤ (fun x : ℤ => x + 1) := by
  intro h
  have impossible := h.map_zero
  norm_num at impossible

/-- The registered evidence does not establish the false affine admission. -/
example : True := by
  fail_if_success
    have : IsLinearMap ℤ (fun x : ℤ => x + 1) := by
      run_tac linearEvidence
  trivial

end CasCatalogue.Modules.LinearMapsTests
