/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass
public import Mathlib.GroupTheory.QuotientGroup.Defs

/-!
# Complex-torus to Weierstrass-cubic map data

Definition-level realization of the construction clause of Hartshorne
FC06-C04-U096.

For a period pair L with lattice Λ, Hartshorne sends the class of z in C/Λ
to the point at infinity when z lies in Λ, and otherwise to

  (wp_L(z), wp'_L(z))

on the cubic

  y^2 = 4 x^3 - g2 x - g3.

The native analytic library already supplies Λ, wp, wp', g2, and g3.
Descending the displayed representative formula to C/Λ uses periodicity,
and showing that its affine values lie on the cubic uses the Weierstrass
differential equation. Those are result statements. Sweep III therefore
records the actual quotient carrier, the cubic-point predicate, and the exact
representative graph, then names the source map by Classical.epsilon.

Biholomorphicity and the rational-function-field comparison are also result
content and are not asserted here.
-/

@[expose] public noncomputable section

namespace LeanCategories.Algebra

open Complex

local instance (L : PeriodPair) :
    DecidablePred (fun z : ℂ => z ∈ L.lattice) :=
  fun _ => Classical.propDecidable _

/-- Hartshorne's complex torus C/Λ for a period pair. -/
abbrev ComplexTorusData (L : PeriodPair) :=
  ℂ ⧸ L.lattice.toAddSubgroup

/-- Raw projective-point carrier for the Weierstrass cubic: zero denotes the
point at infinity, while a nonzero value stores affine coordinates. -/
abbrev ComplexCubicPointCarrierData :=
  WithZero (ℂ × ℂ)

/-- Predicate cutting out the source cubic
y^2 = 4x^3 - g2 x - g3, together with its point at infinity. -/
def IsComplexCubicPointData (L : PeriodPair) :
    ComplexCubicPointCarrierData → Prop
  | 0 => True
  | (some xy) =>
      xy.2 ^ 2 = 4 * xy.1 ^ 3 - L.g₂ * xy.1 - L.g₃

/-- The raw representative-level formula for Hartshorne's map. -/
def complexTorusCubicRepresentativeData
    (L : PeriodPair) (z : ℂ) : ComplexCubicPointCarrierData :=
  if z ∈ L.lattice then
    0
  else
    some (L.weierstrassP z, L.derivWeierstrassP z)

/-- Exact graph specifying the map C/Λ to the Weierstrass cubic.

The first clause is the representative formula. The second says that the
selected values lie on the source cubic. Well-definedness on quotient
representatives and the cubic equation are not proved by this declaration. -/
def IsComplexTorusCubicMapData
    (L : PeriodPair)
    (φ : ComplexTorusData L → ComplexCubicPointCarrierData) : Prop :=
  (∀ z : ℂ,
      φ (QuotientAddGroup.mk' L.lattice.toAddSubgroup z) =
        complexTorusCubicRepresentativeData L z) ∧
    ∀ q : ComplexTorusData L, IsComplexCubicPointData L (φ q)

/-- Hartshorne's map from the complex torus to its Weierstrass cubic, selected
from the exact representative/cubic graph.

The theorem layer proves that the selected function satisfies the graph and
then establishes the analytic and algebraic comparison statements. -/
def complexTorusCubicMapData
    (L : PeriodPair) :
    ComplexTorusData L → ComplexCubicPointCarrierData :=
  Classical.epsilon (IsComplexTorusCubicMapData L)

end LeanCategories.Algebra
