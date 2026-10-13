/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Algebra.ValuationRamificationData

/-!
# Local Galois restriction data

Definition-level realization of Neukirch FC09-C02-U110.

For a local extension `L_w / K_v`, Neukirch writes the decomposition group
simply as the full local Galois group `G(L_w / K_v)` and uses the same local
notation for inertia and ramification.  The map to the global Galois group is
the restriction `σ ↦ σ|_L`.

Sweep III records only those data-level conventions.  The inertia and
ramification objects are kept as raw congruence loci in the full local
automorphism group, so no subgroup-closure or unique-valuation theorem is
required.  Likewise the restriction data are the subtype of ordinary
functions characterized by their action on the embedded global field.  That
this subtype is inhabited by a unique function, that the function is a group
homomorphism, and that its image is the global decomposition group are
result-layer statements.
-/

@[expose] public noncomputable section

namespace LeanCategories.Algebra

universe uK uL uKv uLw

/-- Neukirch's local notation `G(L_w / K_v)`: the full group of
`K_v`-algebra automorphisms of `L_w`. -/
abbrev localGaloisGroupData
    (Kv : Type uKv) (Lw : Type uLw)
    [Field Kv] [Field Lw] [Algebra Kv Lw] : Type _ :=
  Lw ≃ₐ[Kv] Lw

variable
  {Kv : Type uKv} {Lw : Type uLw}
  [Field Kv] [Field Lw] [Algebra Kv Lw]

/-- Raw local inertia locus in `G(L_w / K_v)`.

The congruence is expressed in the ambient field using the literal image of
the valuation ring's maximal ideal.  Proving that the locus is a subgroup,
or identifying it with the native inertia subgroup after uniqueness of the
extended valuation is known, is result content. -/
def localInertiaSetData (A : ValuationSubring Lw) :
    Set (localGaloisGroupData Kv Lw) :=
  {σ | ∀ x : A,
    σ (x : Lw) - (x : Lw) ∈ valuationMaximalIdealImage A}

/-- Raw local ramification locus in `G(L_w / K_v)`.

This is Neukirch's multiplicative congruence
`σx/x ≡ 1 (mod m)`, stated without a subgroup-closure proof. -/
def localRamificationSetData (A : ValuationSubring Lw) :
    Set (localGaloisGroupData Kv Lw) :=
  {σ | ∀ x : Lwˣ,
    σ (x : Lw) / (x : Lw) - 1 ∈ valuationMaximalIdealImage A}

variable
  {K : Type uK} {L : Type uL}
  [Field K] [Field L] [Algebra K L]
  [Algebra K Kv] [Algebra K Lw] [IsScalarTower K Kv Lw]

/-- Characterizing equation for Neukirch's local-to-global restriction
`σ ↦ σ|_L`, relative to the supplied embedding `ι : L → L_w`.

The equation says exactly that applying the selected global automorphism and
then embedding into `L_w` agrees with the local automorphism on the embedded
copy of `L`. -/
def IsLocalToGlobalRestrictionData
    (ι : L →ₐ[K] Lw)
    (restrict :
      localGaloisGroupData Kv Lw → (L ≃ₐ[K] L)) : Prop :=
  ∀ σ x, ι (restrict σ x) = σ (ι x)

/-- The carrier of all raw restriction functions
`G(L_w/K_v) → G(L/K)` satisfying the source action equation on the embedded
copy of `L`.  No unwitnessed restriction function is selected. -/
def LocalToGlobalRestrictionData
    (ι : L →ₐ[K] Lw) :=
  {restrict : localGaloisGroupData Kv Lw → (L ≃ₐ[K] L) //
    IsLocalToGlobalRestrictionData ι restrict}

end LeanCategories.Algebra
