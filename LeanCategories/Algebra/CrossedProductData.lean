/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BrauerGroup.CrossProductAlgebra

/-!
# Crossed-product algebra data

Dummit--Foote, *Abstract Algebra*, Section 17.4 (FC01-C17-U076).

The pinned BrauerGroup package defines the crossed-product carrier, its
`K`-basis indexed by `Gal(K/F)`, and the raw twisted multiplication before it
assumes the two-cocycle law used to prove the monoid/ring/central-simple
structure. This file gives that pre-law construction source-facing names.
-/

@[expose] public noncomputable section

namespace LeanCategories.Algebra

open groupCohomology

universe u

variable {F K : Type u} [Field F] [Field K] [Algebra F K]

/-- Dummit--Foote's crossed-product vector-space carrier attached to raw
factor-set values `f`. -/
abbrev CrossedProductCarrier (f : Gal(K/F) × Gal(K/F) → Kˣ) : Type u :=
  CrossProductAlgebra f

/-- The distinguished `K`-basis `(u_σ)` of the crossed-product carrier. -/
noncomputable def crossedProductBasis (f : Gal(K/F) × Gal(K/F) → Kˣ) :
    Basis Gal(K/F) K (CrossedProductCarrier f) :=
  CrossProductAlgebra.basis

/-- The raw twisted multiplication data on the crossed-product carrier.
The pinned owner defines this before requiring the cocycle law. -/
def crossedProductMul (f : Gal(K/F) × Gal(K/F) → Kˣ)
    (x y : CrossedProductCarrier f) : CrossedProductCarrier f :=
  x * y

end LeanCategories.Algebra
