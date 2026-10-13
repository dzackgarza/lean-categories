/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.Topology.Sheaves.CommRingCat

/-!
# Total quotient sheaf data

Definition-level realization of Hartshorne FC06-C02-U181.

For a commutative ring `R`, its total quotient ring is the localization at
the submonoid of non-zero-divisors.  Mathlib already provides the corresponding
presheaf construction for a sheaf of commutative rings: it localizes at the
sections whose germs are non-zero-divisors in every stalk.  This choice is
restriction-stable by construction.  Sheafifying that native presheaf gives
Hartshorne's total quotient sheaf `K_X` without importing any affine
comparison theorem into Sweep III.

The candidate/specification layer below is retained separately: later result
work may identify the canonical sheaf on an affine open with the total quotient
ring of its section ring.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace
open AlgebraicGeometry

namespace LeanCategories.Schemes

universe u

/-- The total quotient ring of a commutative ring: localization at all
non-zero-divisors. -/
abbrev totalQuotientRingData (R : Type u) [CommRing R] : Type u :=
  Localization (nonZeroDivisors R)

/-- The native total-quotient presheaf of the structure sheaf.

A section is inverted precisely when all of its germs are non-zero-divisors,
so the denominator system is stable under restriction by construction. -/
abbrev totalQuotientPresheafData (X : Scheme.{u}) :
    TopCat.Presheaf CommRingCat X :=
  X.presheaf.totalQuotientPresheaf

/-- Hartshorne's total quotient sheaf `K_X`: the sheafification of the
total-quotient presheaf of `O_X`. -/
noncomputable def totalQuotientSheafData (X : Scheme.{u}) :
    TopCat.Sheaf CommRingCat X :=
  let J := Opens.grothendieckTopology X
  ⟨J.sheafify (totalQuotientPresheafData X),
    J.sheafify_isSheaf (totalQuotientPresheafData X)⟩

/-- The canonical morphism `O_X → K_X`, obtained from the localization map
into the total-quotient presheaf followed by sheafification. -/
noncomputable def toCanonicalTotalQuotientSheafData (X : Scheme.{u}) :
    X.sheaf ⟶ totalQuotientSheafData X :=
  ⟨X.presheaf.toTotalQuotientPresheaf ≫
    (Opens.grothendieckTopology X).toSheafify
      (totalQuotientPresheafData X)⟩

/-- Units of the canonical total quotient sheaf on an open set. -/
abbrev TotalQuotientUnitSections (X : Scheme.{u}) (U : X.Opens) : Type u :=
  ((totalQuotientSheafData X).presheaf.obj (op U) : Type u)ˣ

/-- Candidate data underlying Hartshorne's total quotient sheaf: a sheaf of
commutative rings together with the canonical candidate morphism `O_X → K_X`.

No affine-local comparison proof is bundled into the structure. -/
structure TotalQuotientSheafCandidateData (X : Scheme.{u}) where
  sheaf : TopCat.Sheaf CommRingCat X
  toSheaf : X.sheaf ⟶ sheaf

/-- The canonical total-quotient construction, packaged in the candidate
interface used by the affine-local comparison predicate below. -/
noncomputable def canonicalTotalQuotientSheafCandidateData (X : Scheme.{u}) :
    TotalQuotientSheafCandidateData X where
  sheaf := totalQuotientSheafData X
  toSheaf := toCanonicalTotalQuotientSheafData X

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

/-- The sheaf component of supplied total-quotient-sheaf candidate data. -/
abbrev totalQuotientRingSheafData {X : Scheme.{u}}
    (K : TotalQuotientSheafCandidateData X) :
    TopCat.Sheaf CommRingCat X :=
  K.sheaf

/-- The structure morphism `O_X → K_X` of supplied candidate data. -/
def toTotalQuotientSheafData {X : Scheme.{u}}
    (K : TotalQuotientSheafCandidateData X) :
    X.sheaf ⟶ totalQuotientRingSheafData K :=
  K.toSheaf

/-- `K_X^*` notation for supplied candidate data on an open `U`. -/
abbrev TotalQuotientUnitSectionsData {X : Scheme.{u}}
    (K : TotalQuotientSheafCandidateData X) (U : X.Opens) : Type u :=
  ((totalQuotientRingSheafData K).presheaf.obj (op U) : Type u)ˣ

/-- Hartshorne's `O_X^*` notation on an open `U`: the unit group of regular
sections. -/
abbrev RegularUnitSectionsData (X : Scheme.{u}) (U : X.Opens) : Type u :=
  ((X.sheaf.presheaf.obj (op U) : CommRingCat) : Type u)ˣ

end LeanCategories.Schemes
