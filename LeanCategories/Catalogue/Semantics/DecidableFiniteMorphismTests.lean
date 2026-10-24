/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Catalogue.Semantics.Foundation.FiniteObjects

@[expose] public section

/-!
# Decidable equality of morphisms of named finite sets

A morphism `Fin m ⟶ Fin n` of `FiniteSets` is determined by its function `Fin m → Fin n`
(`FintypeCat` is a full subcategory of types), so an equation between two such morphisms is decided
by `decide`, with a kernel-checked proof, through `CategoryTheory.ConcreteCategory.decidableEqHom`
and Mathlib's decidable equality of functions out of the finite type `Fin m`.

The morphisms are formed as the catalogue forms them: graph literals `graph.finite_sets`
(`finiteOfGraph`) between the named objects `obj.finite_sets.fin` (`finiteFin`), and composition.
-/

namespace CasCatalogue.DecidableFiniteMorphismTests

open CategoryTheory
open CasCatalogue.Foundation.FiniteObjects

/-- The swap `{0 ↦ 1, 1 ↦ 0} : Fin 2 → Fin 2` of finite sets. -/
def swap : finiteFin 2 ⟶ finiteFin 2 :=
  finiteOfGraph [(0, 1), (1, 0)] (by decide) (by decide)

/-- The constant map `{0 ↦ 0, 1 ↦ 0} : Fin 2 → Fin 2` of finite sets. -/
def const0 : finiteFin 2 ⟶ finiteFin 2 :=
  finiteOfGraph [(0, 0), (1, 0)] (by decide) (by decide)

/-- The swap is an involution: `swap ≫ swap = 𝟙`. -/
example : swap ≫ swap = 𝟙 (finiteFin 2) := by
  decide

/-- The swap is not the identity. -/
example : swap ≠ 𝟙 (finiteFin 2) := by
  decide

/-- The constant map absorbs the swap on the left: `swap ≫ const0 = const0`. -/
example : swap ≫ const0 = const0 := by
  decide

/-- The constant map is not the swap. -/
example : const0 ≠ swap := by
  decide

end CasCatalogue.DecidableFiniteMorphismTests
