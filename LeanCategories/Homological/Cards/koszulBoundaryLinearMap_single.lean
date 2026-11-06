/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Homological.KoszulComplex

/-! # Card: `LeanCategories.Homological.koszulBoundaryLinearMap_single`

source: Weibel, *An Introduction to Homological Algebra* (1994), §4.5, pp. 111--114 (FC05-C04-U068).

Published copy of a result from `LeanCategories.Homological.KoszulComplex`; the definition module keeps the original declaration, this file restates it, and the platform submission replaces the delegated proof with `by sorry`.
-/

@[expose] public section

namespace LeanCategories.Cards

open LeanCategories.Homological

namespace LeanCategories.Homological
open CategoryTheory
open scoped BigOperators
universe u
variable (R : Type u) [Ring R]

/-- A published result of `LeanCategories.Homological`, restated here under its platform card name with the proof delegated to the original declaration. -/
theorem LeanCategories_Homological_koszulBoundaryLinearMap_single {n p : ℕ} (x : Fin n → R)
    (s : KoszulBasisIndex n (p + 1)) (r : R) :
    koszulBoundaryLinearMap R x (Finsupp.single s r) = r • koszulBoundaryData R x s := by
  simp [koszulBoundaryLinearMap]

end LeanCategories.Homological
end LeanCategories.Cards
