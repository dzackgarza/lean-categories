/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Catalogue.Semantics.Modules.CatalogueRegistration
public import LeanCategories.Catalogue.Semantics.Algebra.NamedCommutativeRings
public import Mathlib.Data.ZMod.Basic
public meta import LeanCategories.Catalogue.Registry.Semantic
public meta import LeanCategories.Catalogue.Semantics.Modules.Catalogue

@[expose] public section

/-!
# The integer module of residues

The family is the regular `ZMod n` module reindexed along the actual quotient
`Int.castRingHom (ZMod n) : ℤ →+* ZMod n`. This definition uses the existing
module fibration, not a new scalar-restriction operation or an inclusion of fibres.
The parameter order is the modulus `n`; both scalar rings, the quotient map and
the regular module occur in the defining reindexing expression.

Source: Mathlib `ModuleCat.restrictScalars` and the existing module family.
-/

open CategoryTheory

namespace CasCatalogue.Modules.IntegerResidueModules

open CatalogueRegistration

/-- A regular module over `S`, regarded over `R` through the selected ring morphism. -/
noncomputable def restrictedRegularModule (R S : RingCat.{0}) (q : R ⟶ S) : ModuleCat.{0} R :=
  (modulesFamilyRealization.reindex q).obj (regularModule S)

/-- The regular residue module, restricted along the canonical integer quotient. -/
noncomputable def integerResidueModule (n : ℕ) : ModuleCat.{0} ℤ :=
  restrictedRegularModule (RingCat.of ℤ) (RingCat.of (ZMod n))
    (RingCat.ofHom (Int.castRingHom (ZMod n)))

/-- This is exactly reindexing in the existing module family. -/
theorem reindex_selected_quotient (n : ℕ) :
    integerResidueModule n =
      (ModuleCat.restrictScalars (Int.castRingHom (ZMod n))).obj
        (regularModule (RingCat.of (ZMod n))) := rfl

/-- The chosen scalar action is multiplication by the image under the quotient map. -/
theorem action_formula (n : ℕ) (r : ℤ) (x : integerResidueModule n) :
    ((integerResidueModule n).smul r).hom x = (r : ZMod n) * (show ZMod n from x) := rfl

/-- The reindexed module keeps the five-element additive carrier. -/
theorem five_cardinality : Nat.card (integerResidueModule 5) = 5 := by
  change Nat.card (ZMod 5) = 5
  simp

/-- Three scalar observations distinguish restriction from a free integer module. -/
theorem five_actions :
    ((integerResidueModule 5).smul 2).hom (3 : ZMod 5) = (1 : ZMod 5) ∧
    ((integerResidueModule 5).smul 5).hom (1 : ZMod 5) = (0 : ZMod 5) ∧
    ((integerResidueModule 5).smul (-1)).hom (2 : ZMod 5) = (3 : ZMod 5) := by
  change (2 : ZMod 5) * 3 = 1 ∧ (5 : ZMod 5) * 1 = 0 ∧ (-1 : ZMod 5) * 2 = 3
  decide

/-- Reindexing an arbitrary actual regular-module map keeps its full additive function. -/
theorem reindex_map_apply (n : ℕ)
    (f : regularModule (RingCat.of (ZMod n)) ⟶ regularModule (RingCat.of (ZMod n)))
    (x : integerResidueModule n) :
    ((modulesFamilyRealization.reindex
      (RingCat.ofHom (Int.castRingHom (ZMod n)))).map f).hom x = f.hom x := rfl

/-- In particular, the nonidentity regular-module map `x ↦ 2x` retains its action. -/
theorem reindex_double_three :
    ((modulesFamilyRealization.reindex
      (RingCat.ofHom (Int.castRingHom (ZMod 5)))).map
      (ModuleCat.ofHom (X := regularModule (RingCat.of (ZMod 5)))
        (Y := regularModule (RingCat.of (ZMod 5)))
        ((2 : ZMod 5) • LinearMap.id))).hom (3 : ZMod 5) = (1 : ZMod 5) := by
  change (2 : ZMod 5) * 3 = 1
  decide

end CasCatalogue.Modules.IntegerResidueModules

namespace CasCatalogue

normalized_registry .object
  { id := ⟨"obj.modules_r.restricted_regular"⟩, category := CategoryId.modulesR
    name := "RestrictedRegularModule"
    declaration := `CasCatalogue.Modules.IntegerResidueModules.restrictedRegularModule }

end CasCatalogue
