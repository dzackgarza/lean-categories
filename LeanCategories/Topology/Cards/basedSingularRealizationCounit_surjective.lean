/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Topology.SingularRealization

/-! # Card: `LeanCategories.Topology.basedSingularRealizationCounit_surjective`

source: Hatcher, *Algebraic Topology*, §2.C and May, *A Concise Course in Algebraic Topology*, ch. 16 (the singular-realization adjunction `|Sing X| ⊣ Sing`), realized formally as Mathlib's `SSet.toTop ⊣ TopCat.toSSet` (`Mathlib.AlgebraicTopology.SimplicialSet.TopAdj`) at the pinned revision; the point and counit equation proved here are those of the adjunction's counit.

Published copy of a result of `LeanCategories.Topology.SingularRealization`. The definition module keeps the original declaration; this file states it and delegates the proof, and the platform submission replaces that proof term with `by sorry`.
-/

namespace LeanCategories.Cards

open LeanCategories.Topology

open CategoryTheory
open scoped Simplicial
universe u

/-- The based counit is surjective on points. -/
theorem LeanCategories_Topology_basedSingularRealizationCounit_surjective : ∀ (X : BasedTop.{u}),
    Function.Surjective (basedSingularRealizationCounit X).right.hom :=
  LeanCategories.Topology.basedSingularRealizationCounit_surjective

end LeanCategories.Cards
