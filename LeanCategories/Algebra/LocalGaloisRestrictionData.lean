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
required.  Likewise the restriction is selected as an ordinary function
characterized by its action on the embedded dense/global field.  That it is a
group homomorphism, that the characterizing function exists and is unique,
and that it identifies the local group with the global decomposition group
are result-layer statements.
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

/-- Neukirch's raw restriction function
`G(L_w/K_v) → G(L/K)`, selected by its action on the embedded copy of
`L`.

The local/global completion comparison later proves existence, uniqueness,
the homomorphism law, and that the image is the global decomposition group.
None of those propositions is bundled into this Sweep-III construction. -/
def localToGlobalRestrictionData
    (ι : L →ₐ[K] Lw) :
    localGaloisGroupData Kv Lw → (L ≃ₐ[K] L) := by
  classical
  letI : Nonempty
      (localGaloisGroupData Kv Lw → (L ≃ₐ[K] L)) :=
    ⟨fun _ => AlgEquiv.refl⟩
  exact Classical.epsilon (IsLocalToGlobalRestrictionData ι)

end LeanCategories.Algebra
