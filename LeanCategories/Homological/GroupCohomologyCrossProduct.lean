/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Homological.GroupCohomologyCrossProductComparison

/-!
# Cohomological cross products for groups

Public resolution-independent API for Weibel, *An Introduction to Homological
Algebra* (1994), Construction 6.1.14, pp. 160--166 (FC05-C06-U016).

The resolution-level tensor-total construction and homology descent are in
`GroupCohomologyCrossProductCore`; chosen resolution data and the individual
comparison morphisms are cached in `GroupCohomologyCrossProductTransport`, and
the source-side comparison composite in `GroupCohomologyCrossProductComparison`.
This module contains only the final comparison back to group cohomology.
-/

@[expose] public section

noncomputable section

namespace LeanCategories.Homological

open CategoryTheory
variable (G : Type) [Group G]
variable (H : Type) [Group H]

attribute [-instance] Int.instRing Int.instSemiring Int.instCommSemiring Int.instAddCommGroup

namespace GroupCohomologyCrossProduct

variable (X : GroupCohomologyCrossProduct G H)

/-- The constructed cross product transported through the canonical
resolution comparisons, as a morphism in `ModuleCat ℤ`. -/
noncomputable def map (p q : ℕ) :=
  ModuleCat.ofHom <|
    (targetComparisonInv G H X (p + q)).hom.comp
      (sourceToResolutionMap G H X p q).hom

@[reassoc (attr := simp)]
lemma map_groupCohomologyIso_hom (p q : ℕ) :
    map G H X p q ≫
        (groupCohomologyIso (Rep.trivial ℤ (G × H) ℤ) (p + q)
          X.tensorResolution.toProjectiveResolution).hom =
      sourceComparison G H X p q ≫ resolutionMap G H X p q := by
  change
    (sourceComparison G H X p q ≫ resolutionMap G H X p q ≫
      targetComparisonInv G H X (p + q)) ≫
        (groupCohomologyIso (Rep.trivial ℤ (G × H) ℤ) (p + q)
          X.tensorResolution.toProjectiveResolution).hom = _
  simp only [Category.assoc, targetComparisonInv,
    groupCohomologyResolutionComparisonInv_comp_hom, Category.comp_id]

end GroupCohomologyCrossProduct

end LeanCategories.Homological
