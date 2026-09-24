/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.RingTheory.Localization.FractionRing

/-!
# Total quotient sheaf data

Definition-level realization of Hartshorne FC06-C02-U181.

For a commutative ring `R`, its total quotient ring is the localization at
the submonoid of non-zero-divisors.  Hartshorne obtains the sheaf `K_X` on an
arbitrary scheme by applying this construction on affine opens and sheafifying.

A direct Lean presheaf `U ↦ Localization (nonZeroDivisors Γ(U, O_X))` would
force restriction-compatibility proofs into the constructor.  Sweep III must
not prove those propositions.  This file therefore records the exact affine
local specification as a predicate on a sheaf together with its canonical map
from `O_X`, then names the selected sheaf datum.  The existence, compatibility,
and uniqueness/sheafification statements remain result-layer work.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite
open AlgebraicGeometry

namespace LeanCategories.Schemes

universe u

/-- The total quotient ring of a commutative ring: localization at all
non-zero-divisors. -/
abbrev totalQuotientRingData (R : Type u) [CommRing R] : Type u :=
  Localization (nonZeroDivisors R)

/-- Candidate data underlying Hartshorne's total quotient sheaf: a sheaf of
commutative rings together with the canonical candidate morphism `O_X → K_X`.

No affine-local comparison proof is bundled into the structure. -/
structure TotalQuotientSheafCandidateData (X : Scheme.{u}) where
  sheaf : TopCat.Sheaf CommRingCat X
  toSheaf : X.sheaf ⟶ sheaf

/-- There is always ambient candidate data, so the source-specified datum can
be selected without asking a caller for an existence proof. -/
instance (X : Scheme.{u}) : Nonempty (TotalQuotientSheafCandidateData X) :=
  ⟨⟨X.sheaf, 𝟙 _⟩⟩

/-- Affine-local specification of Hartshorne's total quotient sheaf.

On each affine open `U`, sections are identified with the total quotient ring
of `Γ(U, O_X)`, and the structure map becomes the canonical localization map.
The comparison is kept propositionally rather than proved in Sweep III. -/
def IsTotalQuotientSheafData (X : Scheme.{u})
    (K : TotalQuotientSheafCandidateData X) : Prop :=
  ∀ (U : X.Opens) (_hU : IsAffineOpen U),
    ∃ e : K.sheaf.presheaf.obj (op U) ≅
        CommRingCat.of (totalQuotientRingData Γ(X, U)),
      K.toSheaf.hom.app (op U) ≫ e.hom =
        CommRingCat.ofHom
          (algebraMap Γ(X, U) (totalQuotientRingData Γ(X, U)))

/-- Hartshorne's sheaf of total quotient rings, selected by its exact affine
local specification.  The later existence/specification theorem establishes
that this selected datum satisfies `IsTotalQuotientSheafData`. -/
def totalQuotientSheafData (X : Scheme.{u}) :
    TotalQuotientSheafCandidateData X :=
  Classical.epsilon (IsTotalQuotientSheafData X)

/-- The selected total quotient sheaf `K_X`. -/
abbrev totalQuotientRingSheafData (X : Scheme.{u}) :
    TopCat.Sheaf CommRingCat X :=
  (totalQuotientSheafData X).sheaf

/-- The selected canonical morphism `O_X → K_X`. -/
def toTotalQuotientSheafData (X : Scheme.{u}) :
    X.sheaf ⟶ totalQuotientRingSheafData X :=
  (totalQuotientSheafData X).toSheaf

/-- Hartshorne's `K_X^*` notation on an open `U`: the unit group of the
selected total quotient ring sections. -/
abbrev TotalQuotientUnitSectionsData (X : Scheme.{u}) (U : X.Opens) : Type u :=
  ((totalQuotientRingSheafData X).presheaf.obj (op U) : Type u)ˣ

/-- Hartshorne's `O_X^*` notation on an open `U`: the unit group of regular
sections. -/
abbrev RegularUnitSectionsData (X : Scheme.{u}) (U : X.Opens) : Type u :=
  ((X.sheaf.presheaf.obj (op U) : CommRingCat) : Type u)ˣ

end LeanCategories.Schemes
