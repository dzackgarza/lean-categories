/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Catalogue.Semantics.Algebra.CatalogueRegistration
public import LeanCategories.Catalogue.Semantics.Foundation.Objects
public meta import LeanCategories.Catalogue.Registry.Semantic

@[expose] public section

/-!
# The multiplication and identity of a selected monoid

`FOUNDATIONS.md`, Example 11.1, specifies multiplication `M × M → M` and the
nullary unit `1 → M`, with associativity and the two unit laws. Mathlib's
`MonCat` retains precisely this chosen `Monoid` structure. These declarations
expose its existing operations as set maps, natural in monoid homomorphisms.
There is no additional algebraic structure or choice of a carrier presentation.

A group inherits the same operations through its existing forgetful functor
to monoids. In particular, a categorical automorphism group inherits its
actual composition law and identity automorphism. The token `1` denotes only
this nullary unit; arbitrary numeric literals require additional structure.

Reuse provenance: Mathlib `Algebra/Category/MonCat/Basic.lean` (`MonCat.str`)
and `Algebra/Group/Defs.lean` (`Monoid`, `MulOneClass`), at
`db584cd6d46c92f209a44c0f1c829460d327499d`, Apache-2.0, Lean 4.33.0.
The 2026-10-24 public formalization-corpus searches `MonCat` and `class Monoid`
were followed by inspection of these pinned declarations. This is an interface
to their multiplication and unit, not a new monoid formalization.
-/

open CategoryTheory

namespace CasCatalogue.Algebra.MonoidOperations

open CasCatalogue.Foundation.Objects

/-- The multiplication of the selected monoid, with its entire binary domain. -/
def mul (M : MonCat.{0}) :
    (M × M : Type) ⟶ (M : Type) :=
  TypeCat.ofHom fun p => p.1 * p.2

/-- The selected monoid's identity, as a point with terminal source. -/
def one (M : MonCat.{0}) : fin 1 ⟶ (M : Type) :=
  TypeCat.ofHom fun _ => (1 : M)

/-- A monoid homomorphism preserves the selected multiplication. -/
theorem mul_natural {M N : MonCat.{0}}
    (f : M ⟶ N) (a b : M) : f (mul M (a, b)) = mul N (f a, f b) :=
  map_mul f.hom a b

/-- A monoid homomorphism preserves the selected nullary operation. -/
theorem one_natural {M N : MonCat.{0}}
    (f : M ⟶ N) (p : fin 1) : f (one M p) = one N p :=
  map_one f.hom

end CasCatalogue.Algebra.MonoidOperations

namespace CasCatalogue

normalized_registry .operation
  { id := ⟨"op.monoids.mul"⟩, category := CategoryId.monoids, name := "·", arity := 2
    declaration := `CasCatalogue.Algebra.MonoidOperations.mul }

normalized_registry .operation
  { id := ⟨"op.monoids.one"⟩, category := CategoryId.monoids, name := "1", arity := 0
    declaration := `CasCatalogue.Algebra.MonoidOperations.one }

end CasCatalogue
