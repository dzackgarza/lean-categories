/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Homological.GroupCohomologyCrossProductTransport

/-!
# Comparison-stage group-cohomology cross products

The first transport stage in Weibel Construction 6.1.14 (FC05-C06-U016):
compare resolution-independent cohomology with the chosen resolutions and then
apply the cross product constructed from the tensor-total cochain pairing.
-/

@[expose] public section

noncomputable section

namespace LeanCategories.Homological

open CategoryTheory
open CategoryTheory.MonoidalCategory
open scoped TensorProduct
variable (G : Type) [Group G]
variable (H : Type) [Group H]

/- Match Mathlib's generic `CommRing` specialization of the integral
coefficient structures at the syntax level, avoiding dependent-type instance
diamonds between specialized `Int.inst*` constants and parent projections. -/
attribute [-instance] Int.instRing Int.instSemiring Int.instCommSemiring Int.instAddCommGroup

namespace GroupCohomologyCrossProduct

variable (X : GroupCohomologyCrossProduct G H)

set_option backward.isDefEq.respectTransparency false in
/-- Cross product after comparing the two source group-cohomology objects with
the cohomology of the chosen projective resolutions. -/
noncomputable def sourceToResolutionMap (p q : ℕ) :
    groupCohomology (Rep.trivial ℤ G ℤ) p ⊗
        groupCohomology (Rep.trivial ℤ H ℤ) q ⟶
      X.cochainsGH.homology (p + q) :=
  sourceComparison G H X p q ≫ resolutionMap G H X p q

end GroupCohomologyCrossProduct

end LeanCategories.Homological
