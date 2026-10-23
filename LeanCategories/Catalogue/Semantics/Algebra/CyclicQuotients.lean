/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Catalogue.Semantics.Algebra.Automorphisms
public import LeanCategories.Catalogue.Semantics.Algebra.FiniteGroups
public import Mathlib.Data.ZMod.QuotientGroup
public import Mathlib.Data.ZMod.Aut
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Data.Nat.Totient
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.NormNum
public meta import LeanCategories.Catalogue.Registry.Semantic
public meta import LeanCategories.Catalogue.Semantics.Algebra.Catalogue.Magmas
public meta import LeanCategories.Catalogue.Semantics.Algebra.Automorphisms

@[expose] public section

/-!
# Cyclic quotient groups and their actual automorphisms

The fresh family is the additive quotient `ℤ / nℤ`, expressed as an object of
groups. It is a quotient construction, not a renamed five-element set.
Mathlib `Int.quotientZMultiplesNatEquivZMod` supplies the selected,
generator-preserving comparison with the existing residue-group family.

The already registered `Aut : Core(Groups) ⥤ Groups` is applied to this
actual group. Its group operations are inherited unchanged. The coefficient
description is Mathlib `ZMod.AddAutEquivUnits`; categorical automorphisms
and multiplicative equivalences are compared by `mulEquivIsoGroupIso`.
The resulting map from units gives the complete automorphisms, not an
automorphism-specific definition of inversion or composition.
-/

open CategoryTheory

namespace CasCatalogue.Algebra.CyclicQuotients

open CasCatalogue.Foundation.PowerSets CasCatalogue.Foundation.Objects

/-- For a natural modulus `n`, the set of integer classes in `ℤ / nℤ`, represented
by `Multiplicative (ℤ ⧸ AddSubgroup.zmultiples (n : ℤ))`. The multiplicative wrapper
retains the additive quotient's elements. Two integers represent the same element
exactly when their difference belongs to the subgroup of multiples of `n`.
The domain includes `n = 0`, where this subgroup is zero. `quotientMap` sends an
integer to its class, and the selected point `generator` is the class of one. -/
abbrev quotientCarrier (n : ℕ) : SetsCat.{0} :=
  Multiplicative (ℤ ⧸ AddSubgroup.zmultiples (n : ℤ))

/-- For `n : ℕ`, the group with carrier `ℤ / nℤ` in multiplicative notation:
`[a] * [b] = [a + b]`, identity `[0]`, and inverse `[a]⁻¹ = [-a]`.
Its carrier is exactly `quotientCarrier n`, including the unrestricted case
`n = 0`. `carrierIdentification` is the identity on quotient classes.
`residueComparison` identifies this selected group with the additive group of
`ZMod n` expressed using the same multiplicative convention. -/
abbrev cyclicQuotient (n : ℕ) : GrpCat.{0} := GrpCat.of (quotientCarrier n)

/-- The identity set isomorphism from the forgotten group `cyclicQuotient n`
to `quotientCarrier n`; both directions send each integer class to itself. -/
def carrierIdentification (n : ℕ) :
    (forget GrpCat).obj (cyclicQuotient n) ≅ quotientCarrier n := Iso.refl _

/-- For `n : ℕ`, the set map `ℤ → quotientCarrier n` sending every integer `k`
to its class `[k]` modulo the subgroup `nℤ`. The selected codomain retains its
quotient carrier. `residueComparison_quotient` states that the subsequent
comparison with `ZMod n` sends this class to the integer residue `(k : ZMod n)`. -/
def quotientMap (n : ℕ) : integers ⟶ quotientCarrier n :=
  TypeCat.ofHom fun k => Multiplicative.ofAdd (QuotientAddGroup.mk k)

/-- The point `Fin 1 → quotientCarrier n` whose constant value is the class `[1]`
of the integer one. This is the selected generator of `cyclicQuotient n` for
every natural modulus `n`, using the quotient's additive group operation. -/
def generator (n : ℕ) : fin 1 ⟶ quotientCarrier n :=
  TypeCat.ofHom fun _ => Multiplicative.ofAdd (QuotientAddGroup.mk (1 : ℤ))

/-- For `n : ℕ`, the group isomorphism from `cyclicQuotient n` to
`FiniteGroups.cyclic n`, whose latter carrier is `Multiplicative (ZMod n)`.
It sends the integer class `[k]` to `Multiplicative.ofAdd (k : ZMod n)`;
`residueComparison_quotient` gives this formula. The inverse sends a residue to
its corresponding quotient class. Both sides use addition of integer residues
as the group multiplication, and the class of one is preserved. -/
def residueComparison (n : ℕ) : cyclicQuotient n ≅ FiniteGroups.cyclic n :=
  (Int.quotientZMultiplesNatEquivZMod n).toMultiplicative.toGrpIso

theorem residueComparison_quotient (n : ℕ) (k : ℤ) :
    (residueComparison n).hom (quotientMap n k) = Multiplicative.ofAdd (k : ZMod n) := by
  rfl

/-- Categorical group automorphisms and multiplicative equivalences agree,
including their composition multiplication. -/
def categoricalAutEquiv (G : GrpCat.{0}) : Aut G ≃* MulAut G where
  toFun := Iso.groupIsoToMulEquiv
  invFun := MulEquiv.toGrpIso
  left_inv f := by apply Iso.ext; rfl
  right_inv f := rfl
  map_mul' f g := by ext x; rfl

/-- Automorphisms of the existing residue group are exactly multiplication
by units; the source category is Groups. -/
def residueAutUnits (n : ℕ) : Aut (FiniteGroups.cyclic n) ≃* (ZMod n)ˣ :=
  (categoricalAutEquiv _).trans
    ((MulAutMultiplicative (ZMod n)).trans (ZMod.AddAutEquivUnits n).toMultiplicative)

/-- Transport along the selected group comparison, followed by the unit
coefficient description. -/
def quotientAutUnits (n : ℕ) : Aut (cyclicQuotient n) ≃* (ZMod n)ˣ :=
  (Aut.autMulEquivOfIso (residueComparison n)).trans (residueAutUnits n)

instance automorphisms_finite (n : ℕ) [NeZero n] : Finite (Aut (cyclicQuotient n)) :=
  Finite.of_equiv (ZMod n)ˣ (quotientAutUnits n).symm.toEquiv

/-- The automorphism specified by a unit coefficient. -/
def byUnit (n : ℕ) (u : (ZMod n)ˣ) : Aut (cyclicQuotient n) :=
  (quotientAutUnits n).symm u

/-- For `n : ℕ`, the group morphism from the unit group `(ZMod n)ˣ` to the
categorical automorphism group of the integer quotient `ℤ / nℤ` with its
additive group law, represented as `cyclicQuotient n`. A unit `u`
is sent to the automorphism `byUnit n u`: in the coordinates of
`residueComparison n`, its action on every residue `z` is `z ↦ u * z`, and its
inverse acts by `u⁻¹`. Thus the output is a complete group automorphism of this
quotient. `byUnit_coordinate` specifies its action, while `byUnit_mul` and
`byUnit_inv` give compatibility with the automorphism group operations. -/
def byUnitMorphism (n : ℕ) : GrpCat.of (ZMod n)ˣ ⟶
    (Automorphisms.automorphisms GrpCat).obj ⟨cyclicQuotient n⟩ :=
  GrpCat.ofHom (quotientAutUnits n).symm.toMonoidHom

theorem byUnit_mul (n : ℕ) (u v : (ZMod n)ˣ) :
    byUnit n (u * v) = byUnit n u * byUnit n v :=
  (quotientAutUnits n).symm.map_mul u v

theorem byUnit_inv (n : ℕ) (u : (ZMod n)ˣ) :
    byUnit n u⁻¹ = (byUnit n u)⁻¹ :=
  (quotientAutUnits n).symm.map_inv u

/-- In the specified residue coordinates the action is `a ↦ u*a`. -/
theorem byUnit_coordinate (n : ℕ) (u : (ZMod n)ˣ) (a : cyclicQuotient n) :
    @Multiplicative.toAdd (ZMod n) ((residueComparison n).hom ((byUnit n u).hom a)) =
      (u : ZMod n) * @Multiplicative.toAdd (ZMod n) ((residueComparison n).hom a) := by
  change @Multiplicative.toAdd (ZMod n) ((residueComparison n).hom
    ((residueComparison n).inv
      (((residueAutUnits n).symm u).hom ((residueComparison n).hom a)))) = _
  rw [GrpCat.hom_inv_apply]
  rfl

def unitTwo : (ZMod 5)ˣ := ⟨2, 3, by decide, by decide⟩
def unitThree : (ZMod 5)ˣ := ⟨3, 2, by decide, by decide⟩
def unitFour : (ZMod 5)ˣ := ⟨4, 4, by decide, by decide⟩

theorem unitTwo_inv : unitTwo⁻¹ = unitThree := by apply Units.ext; rfl
theorem unitFour_inv : unitFour⁻¹ = unitFour := by apply Units.ext; rfl

theorem aut_five_card : Nat.card (Aut (cyclicQuotient 5)) = 4 := by
  rw [Nat.card_congr (quotientAutUnits 5).toEquiv, Nat.card_eq_fintype_card,
    ZMod.card_units_eq_totient]
  decide

theorem aut_five_cardinal : Cardinal.mk (Aut (cyclicQuotient 5)) = 4 := by
  let := Fintype.ofFinite (Aut (cyclicQuotient 5))
  rw [Cardinal.mk_fintype, ← Nat.card_eq_fintype_card, aut_five_card]
  norm_num

theorem byUnit_two_inverse : (byUnit 5 unitTwo)⁻¹ = byUnit 5 unitThree := by
  rw [← byUnit_inv, unitTwo_inv]

theorem byUnit_four_inverse : (byUnit 5 unitFour)⁻¹ = byUnit 5 unitFour := by
  rw [← byUnit_inv, unitFour_inv]

theorem byUnit_two_order : orderOf (byUnit 5 unitTwo) = 4 := by
  rw [byUnit, MulEquiv.orderOf_eq]
  apply (orderOf_eq_iff (by decide : 0 < 4)).mpr
  constructor
  · decide
  · intro m hm hpos
    interval_cases m <;> decide

end CasCatalogue.Algebra.CyclicQuotients

namespace CasCatalogue

normalized_registry .object
  { id := ⟨"obj.sets.cyclic_quotient"⟩, category := CategoryId.sets
    name := "CyclicQuotient", declaration := `CasCatalogue.Algebra.CyclicQuotients.quotientCarrier
    generator := some `CasCatalogue.Algebra.CyclicQuotients.generator }

normalized_registry .object
  { id := ⟨"obj.groups.cyclic_quotient"⟩, category := CategoryId.groups
    name := "CyclicQuotient", declaration := `CasCatalogue.Algebra.CyclicQuotients.cyclicQuotient
    refines := some
      { base := ⟨"obj.sets.cyclic_quotient"⟩
        route := #[.functor FunctorId.groupsMonoid, .functor FunctorId.monoidsSemigroup,
          .classifierForget ClassifierId.magmasAssociative,
          .classifierForget ClassifierId.setsBinaryOperation]
        identification := `CasCatalogue.Algebra.CyclicQuotients.carrierIdentification } }

normalized_registry .presentation
  { id := ⟨"cmp.groups.cyclic_quotient_residue"⟩, name := "cyclic_quotient_residue"
    source := ⟨"obj.groups.cyclic_quotient"⟩, target := ⟨"obj.groups.cyclic"⟩
    declaration := `CasCatalogue.Algebra.CyclicQuotients.residueComparison }

normalized_registry .morphism
  { id := ⟨"mor.sets.cyclic_quotient_map"⟩, category := CategoryId.sets
    name := "cyclic_quotient_map", declaration := `CasCatalogue.Algebra.CyclicQuotients.quotientMap }

normalized_registry .morphism
  { id := ⟨"mor.groups.cyclic_quotient_aut_by_unit"⟩, category := CategoryId.groups
    name := "cyclic_quotient_aut_by_unit"
    declaration := `CasCatalogue.Algebra.CyclicQuotients.byUnitMorphism }

end CasCatalogue
