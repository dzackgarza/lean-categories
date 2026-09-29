/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Catalogue.Semantics.Foundation.CatalogueRegistration
public import Mathlib.Data.ZMod.Defs
public meta import LeanCategories.Catalogue.Registry.Semantic

@[expose] public section

/-!
# Named sets

Object constructors of `Sets` (`cat.sets`), with typed parameters:

* `obj.sets.fin`: `n ↦ Fin n = {0, …, n - 1}`;
* `obj.sets.integers_mod`: `n ↦ ℤ/n` (`ZMod n`; `ℤ` for `n = 0`);
* `obj.sets.integers_mod_power`: `(n, k) ↦ (ℤ/n)^k`, the functions `Fin k → ℤ/n`.

Products of sets are the registered limit `lim.sets.product`
(`CasCatalogue.Limits.Registration.setsProduct`).
-/

namespace CasCatalogue.Foundation.Objects

/-- `Fin n`. -/
def fin (n : ℕ) : LeanCategories.Foundation.Mathlib.Sets.{0} := Fin n

/-- `ℤ/n`. -/
def integersMod (n : ℕ) : LeanCategories.Foundation.Mathlib.Sets.{0} := ZMod n

/-- `(ℤ/n)^k`. -/
def integersModPower (n k : ℕ) : LeanCategories.Foundation.Mathlib.Sets.{0} := Fin k → ZMod n

end CasCatalogue.Foundation.Objects

namespace CasCatalogue

normalized_registry .object
  { id := ⟨"obj.sets.fin"⟩, category := CategoryId.sets
    declaration := `CasCatalogue.Foundation.Objects.fin }

normalized_registry .object
  { id := ⟨"obj.sets.integers_mod"⟩, category := CategoryId.sets
    declaration := `CasCatalogue.Foundation.Objects.integersMod }

normalized_registry .object
  { id := ⟨"obj.sets.integers_mod_power"⟩, category := CategoryId.sets
    declaration := `CasCatalogue.Foundation.Objects.integersModPower }

end CasCatalogue
