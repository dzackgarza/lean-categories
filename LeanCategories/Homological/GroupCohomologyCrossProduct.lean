/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Basic
public import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Cohomological cross products for groups

Weibel, *An Introduction to Homological Algebra* (1994), Construction 6.1.14,
pp. 160--166 (FC05-C06-U016).

Projective resolutions for `G`, `H`, and `G × H` produce graded bilinear maps
`H^p(G;ℤ) ⊗ H^q(H;ℤ) → H^{p+q}(G×H;ℤ)`.  This file records the
definition-layer realization data at the resulting cohomology objects.

Construction of these maps from tensor-product total complexes, naturality,
and the comparison theorem are result-level content.
-/

@[expose] public section

noncomputable section

namespace LeanCategories.Homological

open CategoryTheory
open scoped TensorProduct

variable (G : Type) [Group G]
variable (H : Type) [Group H]

/-- Definition-layer realization of Weibel's cohomological cross product. -/
structure GroupCohomologyCrossProduct where
  /-- Chosen projective resolution of the trivial integral `G`-module. -/
  resolutionG : ProjectiveResolution (Rep.trivial ℤ G ℤ)
  /-- Chosen projective resolution of the trivial integral `H`-module. -/
  resolutionH : ProjectiveResolution (Rep.trivial ℤ H ℤ)
  /-- Chosen projective resolution of the trivial integral `(G×H)`-module. -/
  resolutionProd : ProjectiveResolution (Rep.trivial ℤ (G × H) ℤ)
  /-- The graded cross-product maps. -/
  map : ∀ p q : ℕ,
    TensorProduct ℤ
        (groupCohomology (Rep.trivial ℤ G ℤ) p)
        (groupCohomology (Rep.trivial ℤ H ℤ) q) →ₗ[ℤ]
      groupCohomology (Rep.trivial ℤ (G × H) ℤ) (p + q)

end LeanCategories.Homological
