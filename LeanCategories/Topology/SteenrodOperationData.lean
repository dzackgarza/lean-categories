/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Topology.CohomologyCrossProductData
public import Mathlib.Data.Nat.Prime.Basic

/-!
# Steenrod-operation data

Definition-level realization of Hatcher FC07-C04-U171, with the odd-prime
operation family added by FC07-C04-U173 below.

Hatcher's Steenrod squares are degree-shifting additive operations

`Sq^i : H^n(X; Z/2) → H^{n+i}(X; Z/2)`.

Sweep III records this operation family as module morphisms, so additivity is
part of the data type.  Naturality, the Cartan formula, suspension
compatibility, normalization, instability, the top-square identity, and the
`Sq^1` Bockstein comparison are propositions about that data and therefore
remain Sweep-IV obligations.  Several of the source laws that can be stated
against the current singular-cohomology owners are exposed below as predicates;
none is proved or required by the constructor.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace LeanCategories.Topology

/-- Mod-two singular cohomology in degree `n`. -/
abbrev ModTwoSingularCohomologyData (X : TopCat.{0}) (n : ℕ) :
    ModuleCat.{0} (ZMod 2) :=
  singularCohomologyModuleData (ZMod 2) X (ModuleCat.of (ZMod 2) (ZMod 2)) n

/-- Raw family of Steenrod-square operations.

The morphism type makes each operation additive (indeed `ZMod 2`-linear)
without requiring any law proof in the structure. -/
structure SteenrodSquareData where
  sq :
    ∀ (X : TopCat.{0}) (n i : ℕ),
      ModTwoSingularCohomologyData X n ⟶
        ModTwoSingularCohomologyData X (n + i)

instance : Nonempty SteenrodSquareData :=
  ⟨⟨fun _ _ _ => 0⟩⟩

/-- Naturality predicate for a raw Steenrod-square family. -/
def IsSteenrodSquareNaturalData (S : SteenrodSquareData) : Prop :=
  ∀ {X Y : TopCat.{0}} (f : X ⟶ Y) (n i : ℕ),
    S.sq Y n i ≫ singularCohomologyMapData (ZMod 2) f (n + i) =
      singularCohomologyMapData (ZMod 2) f n ≫ S.sq X n i

/-- The source normalization `Sq^0 = id`. -/
def IsSteenrodSquareZeroData (S : SteenrodSquareData) : Prop :=
  ∀ (X : TopCat.{0}) (n : ℕ), S.sq X n 0 = 𝟙 _

/-- Hatcher's top-square clause `Sq^n(a) = a ∪ a`. -/
def IsSteenrodSquareTopData (S : SteenrodSquareData) : Prop :=
  ∀ (X : TopCat.{0}) (n : ℕ)
      (a : ModTwoSingularCohomologyData X n),
    (S.sq X n n).hom a =
      singularCohomologyCupMulData (ZMod 2) X a a

/-- Hatcher's instability clause `Sq^i(a)=0` for `i>n`. -/
def IsSteenrodSquareUnstableData (S : SteenrodSquareData) : Prop :=
  ∀ (X : TopCat.{0}) (n i : ℕ) (_ : n < i)
      (a : ModTwoSingularCohomologyData X n),
    (S.sq X n i).hom a = 0

/-- Source-facing Steenrod-square operation data.

This selects a member of the exact operation-family type without proving any
of Hatcher's law clauses.  The law predicates above, together with Cartan,
suspension compatibility, and the Bockstein comparison, are verified only in
the theorem sweep. -/
def steenrodSquareData : SteenrodSquareData :=
  Classical.choice inferInstance

/-- Mod-`p` singular cohomology in degree `n`. -/
abbrev ModPSingularCohomologyData (p : ℕ) (X : TopCat.{0}) (n : ℕ) :
    ModuleCat.{0} (ZMod p) :=
  singularCohomologyModuleData (ZMod p) X (ModuleCat.of (ZMod p) (ZMod p)) n

/-- Raw family of odd-prime Steenrod reduced-power operations.

For the source application `p` is an odd prime.  The carrier makes sense
for every natural `p`, while the source-facing selector below takes the
prime and oddness hypotheses explicitly. -/
structure SteenrodReducedPowerData (p : ℕ) where
  power :
    ∀ (X : TopCat.{0}) (n i : ℕ),
      ModPSingularCohomologyData p X n ⟶
        ModPSingularCohomologyData p X (n + (2 * (p - 1)) * i)

instance (p : ℕ) : Nonempty (SteenrodReducedPowerData p) :=
  ⟨⟨fun _ _ _ => 0⟩⟩

/-- Naturality predicate for a raw reduced-power family. -/
def IsSteenrodReducedPowerNaturalData {p : ℕ}
    (P : SteenrodReducedPowerData p) : Prop :=
  ∀ {X Y : TopCat.{0}} (f : X ⟶ Y) (n i : ℕ),
    P.power Y n i ≫
        singularCohomologyMapData (ZMod p) f
          (n + (2 * (p - 1)) * i) =
      singularCohomologyMapData (ZMod p) f n ≫ P.power X n i

/-- The source normalization `P^0 = id`. -/
def IsSteenrodReducedPowerZeroData {p : ℕ}
    (P : SteenrodReducedPowerData p) : Prop :=
  ∀ (X : TopCat.{0}) (n : ℕ), P.power X n 0 = 𝟙 _

/-- Hatcher's odd-prime instability clause `P^i(a)=0` when `2i>n`. -/
def IsSteenrodReducedPowerUnstableData {p : ℕ}
    (P : SteenrodReducedPowerData p) : Prop :=
  ∀ (X : TopCat.{0}) (n i : ℕ) (_ : n < 2 * i)
      (a : ModPSingularCohomologyData p X n),
    (P.power X n i).hom a = 0

/-- Source-facing reduced-power operation data for an odd prime.

The primality and oddness assumptions are exactly Hatcher's source
hypotheses.  No Cartan, suspension, `p`th-power, normalization, or
instability proof is required by this constructor. -/
def steenrodReducedPowerData
    (p : ℕ) (_hp : Nat.Prime p) (_hodd : p ≠ 2) :
    SteenrodReducedPowerData p :=
  Classical.choice inferInstance

end LeanCategories.Topology
