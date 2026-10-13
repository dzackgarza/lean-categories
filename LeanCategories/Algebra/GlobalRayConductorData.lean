/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Algebra.IdeleGroup
public import Mathlib.Order.Lattice.Nat

/-!
# Global ray-modulus and conductor data

Definition-level realization of Neukirch FC09-C06-U060, following the checked
Atlas conductor construction while separating its proof layer.

Neukirch's conductor of a finite abelian extension is the gcd of all moduli
`m` whose idèle-class congruence subgroup `C_K^m` is contained in the norm
subgroup.  A modulus is represented here by its exponent function on finite
and infinite places.  Finite support and the restrictions at infinite places
are stated separately, so constructing the gcd does not require proving those
properties in Sweep III.
-/

@[expose] public noncomputable section

open IsDedekindDomain NumberField

namespace LeanCategories

universe u

/-- A finite or infinite place of a number field, for global ray moduli. -/
inductive GlobalRayPlaceData
    (K : Type u) [Field K] [NumberField K] where
  | finite : HeightOneSpectrum (𝓞 K) → GlobalRayPlaceData K
  | infinite : InfinitePlace K → GlobalRayPlaceData K

/-- Raw exponent data of a global ray modulus. -/
abbrev GlobalRayModulusData
    (K : Type u) [Field K] [NumberField K] :=
  GlobalRayPlaceData K → ℕ

/-- The source conditions on raw global ray-modulus exponent data:
finite support, exponent at most one at infinity, and exponent zero at complex
places. -/
def IsGlobalRayModulusData
    (K : Type u) [Field K] [NumberField K]
    (m : GlobalRayModulusData K) : Prop :=
  Set.Finite {v | m v ≠ 0} ∧
    (∀ v : InfinitePlace K, m (.infinite v) ≤ 1) ∧
      ∀ v : InfinitePlace K, v.IsComplex → m (.infinite v) = 0

/-- Divisibility of global ray moduli, written on exponent data. -/
def GlobalRayModulusDvdData
    (K : Type u) [Field K] [NumberField K]
    (m n : GlobalRayModulusData K) : Prop :=
  ∀ v, m v ≤ n v

/-- The pointwise gcd of a set of raw ray moduli.

For each place this takes the infimum of the natural-number exponents.  The
statement that the resulting exponent function again satisfies the modulus
conditions, when the family is nonempty, is result content. -/
def globalRayModulusGcdData
    (K : Type u) [Field K] [NumberField K]
    (S : Set (GlobalRayModulusData K)) :
    GlobalRayModulusData K :=
  fun v => sInf {n : ℕ | ∃ m ∈ S, m v = n}

/-- The set of defining moduli for a supplied norm subgroup:
`{m | C_K^m ≤ N_L}`.

The congruence subgroups and norm subgroup are supplied by their mathematical
owners; no class-field existence or reciprocity theorem is used here. -/
def extensionDefiningModuliData
    (K : Type u) [Field K] [NumberField K]
    (congruenceSubgroup :
      GlobalRayModulusData K → Subgroup (IdeleClassGroup K))
    (normSubgroup : Subgroup (IdeleClassGroup K)) :
    Set (GlobalRayModulusData K) :=
  {m | congruenceSubgroup m ≤ normSubgroup}

/-- Neukirch Definition 6.4: the conductor is the gcd of all moduli `m`
such that `C_K^m ≤ N_L`.

Existence of a defining modulus, validity/minimality of the resulting modulus,
and its comparison with local conductors are later propositions. -/
def extensionConductorData
    (K : Type u) [Field K] [NumberField K]
    (congruenceSubgroup :
      GlobalRayModulusData K → Subgroup (IdeleClassGroup K))
    (normSubgroup : Subgroup (IdeleClassGroup K)) :
    GlobalRayModulusData K :=
  globalRayModulusGcdData K
    (extensionDefiningModuliData K congruenceSubgroup normSubgroup)

end LeanCategories
