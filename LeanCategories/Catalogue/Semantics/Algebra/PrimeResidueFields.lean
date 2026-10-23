/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Catalogue.Semantics.Algebra.Fields
public import LeanCategories.Catalogue.Semantics.Foundation.Cardinality
public import Mathlib.Algebra.Field.ZMod
public meta import LeanCategories.Catalogue.Registry.Semantic
public meta import LeanCategories.Catalogue.Semantics.Algebra.Fields

@[expose] public section

/-!
# Prime residue fields and their two ring carrier routes

The new object family uses Mathlib's field structure on `ZMod p`, under the actual
primality hypothesis. Its forgotten ring is the existing named ring, so the old
additive and multiplicative functors and their existing comparison apply unchanged.
The comparison is at sets. It does not equate the two monoid operations.

Source: Mathlib `ZMod.instField`, `ZMod.card`, and the existing
`LeanCategories.Algebra.ringCarrierComparison`.
-/

open CategoryTheory

namespace CasCatalogue.Algebra.PrimeResidueFields

/-- The prime residue field, with its primality evidence as an explicit input. -/
def primeResidues (p : ℕ) (hp : p.Prime) : LeanCategories.Algebra.FieldCat.{0} :=
  letI : Fact p.Prime := ⟨hp⟩
  ⟨NamedCommutativeRings.integersMod p, Field.toIsField (ZMod p)⟩

/-- Forgetting the new field object retains the existing selected residue ring. -/
theorem underlying_ring (p : ℕ) (hp : p.Prime) :
    (forget₂ CommRingCat RingCat).obj (Fields.ring (primeResidues p hp)) =
      NamedRings.ringIntegersMod p := rfl

/-- The supplied carrier cell acts by the identity on each actual residue. -/
theorem carrier_comparison_apply (p : ℕ) (hp : p.Prime) (x : ZMod p) :
    (LeanCategories.Algebra.ringCarrierComparison.app
      ((forget₂ CommRingCat RingCat).obj (Fields.ring (primeResidues p hp)))).hom x = x := rfl

/-- Both complete routes retain the actual function of every ring homomorphism. -/
theorem carrier_routes_map {R S : RingCat.{0}} (f : R ⟶ S) (x : R) :
    LeanCategories.Algebra.ringCarrierMultiplicative.map f x = f.hom x ∧
      LeanCategories.Algebra.ringCarrierAdditive.map f x = f.hom x := ⟨rfl, rfl⟩

/-- The multiplicative route has five elements on the selected prime residue field. -/
theorem five_multiplicative_cardinality :
    Nat.card (LeanCategories.Algebra.ringCarrierMultiplicative.obj
      ((forget₂ CommRingCat RingCat).obj (Fields.ring (primeResidues 5 (by decide))))) = 5 := by
  change Nat.card (ZMod 5) = 5
  simp

/-- The additive route also has five elements, with its actual multiplicative wrapper retained. -/
theorem five_additive_cardinality :
    Nat.card (LeanCategories.Algebra.ringCarrierAdditive.obj
      ((forget₂ CommRingCat RingCat).obj (Fields.ring (primeResidues 5 (by decide))))) = 5 := by
  change Nat.card (ZMod 5) = 5
  simp

/-- Equal carriers do not identify the selected additive and multiplicative operations. -/
theorem five_operations_separate :
    (1 + 1 : ZMod 5) = 2 ∧ (1 * 1 : ZMod 5) = 1 ∧
      (1 + 1 : ZMod 5) ≠ (1 * 1 : ZMod 5) := by decide

end CasCatalogue.Algebra.PrimeResidueFields

namespace CasCatalogue

normalized_registry .object
  { id := ⟨"obj.fields.prime_residues"⟩, category := CategoryId.fields
    name := "PrimeResidues"
    declaration := `CasCatalogue.Algebra.PrimeResidueFields.primeResidues }

end CasCatalogue
