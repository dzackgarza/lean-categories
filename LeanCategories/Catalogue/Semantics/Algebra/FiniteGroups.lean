/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Catalogue.Semantics.Algebra.Subgroups
public import LeanCategories.Catalogue.Semantics.Algebra.Ports
public import LeanCategories.Catalogue.Semantics.Algebra.NamedRings
public import LeanCategories.Catalogue.Semantics.Foundation.PowerSets
public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.Algebra.Ring.Int.Units
public import Mathlib.Tactic.NormNum
public meta import LeanCategories.Catalogue.Semantics.Algebra.Subgroups
public meta import LeanCategories.Catalogue.Registry.Semantic
public meta import LeanCategories.Catalogue.Semantics.Algebra.Catalogue.Magmas
public meta import LeanCategories.Catalogue.Semantics.Algebra.Ports

@[expose] public section

/-!
# Symmetric groups, alternating subgroups, and parity

`Sₙ` is the permutation group of the ordinal `n`; `Aₙ` is the kernel of sign.
A subgroup and a group kernel retain their inclusion as a monomorphism of
chosen groups. The groups and subgroups acquire their interfaces solely from
their categories. Sources: Mathlib `Equiv.Perm.sign`, `alternatingGroup`,
`MonoidHom.ker`, and the subgroup inclusion `Subgroup.subtype`.
-/

open CategoryTheory

namespace CasCatalogue.Algebra.FiniteGroups
open CasCatalogue.Foundation.PowerSets

/-- The chosen symmetric group of an ordinal. -/
abbrev symmetric (n : ℕ) : GrpCat.{0} := GrpCat.of (Equiv.Perm (Fin n))

/-- Its named underlying set. -/
abbrev permutations (n : ℕ) : SetsCat.{0} := Equiv.Perm (Fin n)

def symmetricIdentification (n : ℕ) : (forget GrpCat).obj (symmetric n) ≅ permutations n :=
  Iso.refl _

/-- The additive cyclic group, expressed multiplicatively as an object of groups. -/
abbrev cyclic (n : ℕ) : GrpCat.{0} := GrpCat.of (Multiplicative (ZMod n))

/-- Its underlying set remains the named residue set. -/
def cyclicIdentification (n : ℕ) : (forget GrpCat).obj (cyclic n) ≅
    CasCatalogue.Foundation.Objects.integersMod n := Iso.refl _

/-- A subgroup as a complete monomorphism, retaining its chosen ambient group. -/
def subgroup (G : GrpCat.{0}) (H : Subgroup G) : Subgroups.subobjectsGroupsCategory.{0} :=
  Subgroups.subgroup G H

/-- The alternating subgroup, including its defining inclusion into `Sₙ`. -/
def alternating (n : ℕ) : Subgroups.subobjectsGroupsCategory.{0} :=
  subgroup (symmetric n) (alternatingGroup (Fin n))

/-- The kernel subgroup of the actual selected group homomorphism. -/
def kernel (G H : GrpCat.{0}) (f : G ⟶ H) : Subgroups.subobjectsGroupsCategory.{0} :=
  subgroup G f.hom.ker

/-- Sign values `±1` expressed as parity in the additive group `ℤ/2`. -/
def unitsParity : ℤˣ →* Multiplicative (ZMod 2) where
  toFun u := if u = 1 then 1 else Multiplicative.ofAdd 1
  map_one' := by decide
  map_mul' a b := by
    rcases Int.units_eq_one_or a with rfl | rfl <;>
      rcases Int.units_eq_one_or b with rfl | rfl <;> decide

/-- The parity map `Sₙ → ℤ/2`. -/
def sign (n : ℕ) : symmetric n ⟶ cyclic 2 :=
  GrpCat.ofHom (unitsParity.comp Equiv.Perm.sign)

/-- The identity map in any chosen group. -/
def identity (G : GrpCat.{0}) : G ⟶ G := 𝟙 G

/-- The trivial homomorphism between chosen groups. -/
def trivial (G H : GrpCat.{0}) : G ⟶ H := GrpCat.ofHom 1

/-- Parity is zero precisely at the positive sign. -/
@[simp] theorem unitsParity_eq_one (u : ℤˣ) : unitsParity u = 1 ↔ u = 1 := by
  rcases Int.units_eq_one_or u with rfl | rfl <;> decide

/-- The parity kernel is the alternating subgroup, with its original ambient group. -/
theorem sign_kernel (n : ℕ) : (sign n).hom.ker = alternatingGroup (Fin n) := by
  ext g
  simp [sign, alternatingGroup, MonoidHom.mem_ker]

/-- The trivial map has the complete source group as kernel. -/
theorem trivial_kernel (G H : GrpCat.{0}) : (trivial G H).hom.ker = ⊤ := by
  ext g
  simp [trivial, MonoidHom.mem_ker]

/-- The identity map has the trivial subgroup as kernel. -/
theorem identity_kernel (G : GrpCat.{0}) : (identity G).hom.ker = ⊥ := by
  ext g
  simp [identity, MonoidHom.mem_ker]

/-- The inclusion of a subgroup is exactly its defining element inclusion. -/
@[simp] theorem subgroup_inclusion_apply (G : GrpCat.{0}) (H : Subgroup G) (h : H) :
    ConcreteCategory.hom (C := GrpCat) (subgroup G H).obj.hom h = h.1 := rfl

/-- The alternating subgroup in the required three-letter case has order three. -/
theorem alternating_three_card : Fintype.card (alternatingGroup (Fin 3)) = 3 := by
  rw [card_alternatingGroup]
  norm_num [Nat.factorial]

end CasCatalogue.Algebra.FiniteGroups

namespace CasCatalogue

normalized_registry .object
  { id := ⟨"obj.sets.permutations"⟩, category := CategoryId.sets, name := "Sym"
    declaration := `CasCatalogue.Algebra.FiniteGroups.permutations }
normalized_registry .object
  { id := ⟨"obj.groups.symmetric"⟩, category := CategoryId.groups, name := "Sym"
    declaration := `CasCatalogue.Algebra.FiniteGroups.symmetric
    refines := some
      { base := ⟨"obj.sets.permutations"⟩
        route := #[.functor FunctorId.groupsMonoid, .functor FunctorId.monoidsSemigroup,
          .classifierForget ClassifierId.magmasAssociative,
          .classifierForget ClassifierId.setsBinaryOperation]
        identification := `CasCatalogue.Algebra.FiniteGroups.symmetricIdentification } }
normalized_registry .object
  { id := ⟨"obj.groups.cyclic"⟩, category := CategoryId.groups, name := "ZMod"
    declaration := `CasCatalogue.Algebra.FiniteGroups.cyclic
    refines := some
      { base := ⟨"obj.sets.integers_mod"⟩
        route := #[.functor FunctorId.groupsMonoid, .functor FunctorId.monoidsSemigroup,
          .classifierForget ClassifierId.magmasAssociative,
          .classifierForget ClassifierId.setsBinaryOperation]
        identification := `CasCatalogue.Algebra.FiniteGroups.cyclicIdentification } }
normalized_registry .object
  { id := ⟨"obj.subgroups.subgroup"⟩, category := CategoryId.subobjectsGroups, name := "Subgroup"
    declaration := `CasCatalogue.Algebra.FiniteGroups.subgroup }
normalized_registry .object
  { id := ⟨"obj.subgroups.alternating"⟩, category := CategoryId.subobjectsGroups, name := "Alt"
    declaration := `CasCatalogue.Algebra.FiniteGroups.alternating }
normalized_registry .object
  { id := ⟨"obj.subgroups.kernel"⟩, category := CategoryId.subobjectsGroups, name := "GroupKernel"
    declaration := `CasCatalogue.Algebra.FiniteGroups.kernel }
normalized_registry .morphism
  { id := ⟨"mor.groups.sign"⟩, category := CategoryId.groups, name := "sign"
    declaration := `CasCatalogue.Algebra.FiniteGroups.sign }
normalized_registry .morphism
  { id := ⟨"mor.groups.identity"⟩, category := CategoryId.groups, name := "id"
    declaration := `CasCatalogue.Algebra.FiniteGroups.identity }
normalized_registry .morphism
  { id := ⟨"mor.groups.trivial"⟩, category := CategoryId.groups, name := "trivial"
    declaration := `CasCatalogue.Algebra.FiniteGroups.trivial }

end CasCatalogue
