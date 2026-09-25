/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Homological.GroupCohomologyCrossProductCore

/-!
# Resolution transport for group-cohomology cross products

Resolution and comparison data for Weibel, *An Introduction to Homological
Algebra* (1994), Construction 6.1.14, pp. 160--166 (FC05-C06-U016).

The tensor-total construction and homology descent live in
`GroupCohomologyCrossProductCore`.  This module packages chosen resolutions and
the three component morphisms used to transport that construction to Mathlib's
resolution-independent group cohomology.
-/

@[expose] public section

noncomputable section

namespace LeanCategories.Homological

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open scoped TensorProduct

variable (G : Type) [Group G]
variable (H : Type) [Group H]

/- Match Mathlib's generic `CommRing` specialization of the integral
coefficient structures at the syntax level, avoiding dependent-type instance
diamonds between specialized `Int.inst*` constants and parent projections. -/
attribute [-instance] Int.instRing Int.instSemiring Int.instCommSemiring Int.instAddCommGroup

/-- Resolution data used in Weibel's Construction 6.1.14.  The tensor-total
resolution is the construction of Proposition 6.1.13; the cochain pairing and
all maps induced from it are definitions, not additional structure fields. -/
structure GroupCohomologyCrossProduct where
  /-- Chosen projective resolution of the trivial integral `G`-module. -/
  resolutionG : ProjectiveResolution (Rep.trivial ℤ G ℤ)
  /-- Chosen projective resolution of the trivial integral `H`-module. -/
  resolutionH : ProjectiveResolution (Rep.trivial ℤ H ℤ)
  /-- The actual tensor-total resolution of the trivial `(G × H)`-module. -/
  tensorResolution : GroupExternalTensorResolution G H resolutionG resolutionH

namespace GroupCohomologyCrossProduct

variable (X : GroupCohomologyCrossProduct G H)

/-- The cochain complexes `Hom_G(P,ℤ)`, `Hom_H(Q,ℤ)`, and
`Hom_{G×H}(P⊗Q,ℤ)` attached to the chosen resolution data. -/
noncomputable abbrev cochainsG :=
  X.resolutionG.complex.linearYonedaObj ℤ (Rep.trivial ℤ G ℤ)
noncomputable abbrev cochainsH :=
  X.resolutionH.complex.linearYonedaObj ℤ (Rep.trivial ℤ H ℤ)
noncomputable abbrev cochainsGH :=
  X.tensorResolution.toProjectiveResolution.complex.linearYonedaObj ℤ
    (Rep.trivial ℤ (G × H) ℤ)

/-- The `(p,q)` component of Weibel's natural cochain pairing.  This is the
constructed map `μ(f⊗g)(x⊗y)=f(x)g(y)`, not supplied data. -/
noncomputable def μ (p q : ℕ) :
    X.cochainsG.X p ⊗ X.cochainsH.X q ⟶ X.cochainsGH.X (p + q) :=
  groupCochainPairing G H X.resolutionG X.resolutionH p q

/-- Weibel's natural cochain morphism on the whole tensor-total complex. -/
noncomputable def μTotal :
    groupCochainTensorComplex G H X.resolutionG X.resolutionH ⟶ X.cochainsGH :=
  groupCochainTotalPairing G H X.resolutionG X.resolutionH

/-- The cross product on the cohomology of the chosen resolutions.  This is
the canonical tensor-homology map followed by the map induced by `μTotal`. -/
noncomputable def resolutionMap (p q : ℕ) :
    (X.cochainsG.homology p) ⊗ (X.cochainsH.homology q) ⟶
      X.cochainsGH.homology (p + q) :=
  groupResolutionCohomologyCrossProduct G H X.resolutionG X.resolutionH p q

/-- Cached canonical comparison from Mathlib group cohomology to the cohomology
of a chosen projective resolution.  Irreducibility prevents consumers from
re-elaborating the Ext-based implementation of `groupCohomologyIso`. -/
noncomputable irreducible_def resolutionComparisonHom
    (lemma := resolutionComparisonHom_def)
    (K : Type) [Group K]
    (P : ProjectiveResolution (Rep.trivial ℤ K ℤ)) (n : ℕ) :=
  groupCohomologyResolutionComparisonHom K P n

/-- Cached inverse canonical comparison for a chosen projective resolution. -/
noncomputable irreducible_def resolutionComparisonInv
    (lemma := resolutionComparisonInv_def)
    (K : Type) [Group K]
    (P : ProjectiveResolution (Rep.trivial ℤ K ℤ)) (n : ℕ) :=
  groupCohomologyResolutionComparisonInv K P n

set_option backward.isDefEq.respectTransparency false in
/-- Comparison from resolution-independent group cohomology to the chosen
resolution cohomologies in both factors. -/
noncomputable def sourceComparison (p q : ℕ) :=
  resolutionComparisonHom G X.resolutionG p ⊗ₘ
    resolutionComparisonHom H X.resolutionH q

set_option backward.isDefEq.respectTransparency false in
/-- The inverse comparison from the cohomology of the tensor-total resolution
to resolution-independent group cohomology. -/
noncomputable def targetComparisonInv (n : ℕ) :=
  resolutionComparisonInv (G × H)
    X.tensorResolution.toProjectiveResolution n

end GroupCohomologyCrossProduct

end LeanCategories.Homological
