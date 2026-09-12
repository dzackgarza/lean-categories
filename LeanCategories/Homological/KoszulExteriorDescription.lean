/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Homological.KoszulComplex

/-!
# Exterior description of the Koszul complex

Weibel, *An Introduction to Homological Algebra* (1994), §4.5, pp. 111--114
(FC05-C04-U070).

For a central sequence in an arbitrary associative ring, the exterior-power
description is represented combinatorially by ordered wedge symbols indexed by
finite subsets.  This is the source-general free-module model underlying
`Λ^p R^n`; it does not replace the ring by a commutative one merely to reuse a
commutative exterior-algebra implementation.
-/

@[expose] public section

namespace LeanCategories.Homological

universe u

variable (R : Type u) [Ring R]

/-- Ordered wedge-basis symbols `e_{i₁}∧⋯∧e_{i_p}` for the degree-`p`
exterior model of `R^n`. -/
abbrev KoszulWedgeIndex (n p : ℕ) := KoszulBasisIndex n p

/-- The source-general combinatorial model of `Λ^p R^n`. -/
abbrev KoszulExteriorDegree (n p : ℕ) := KoszulDegree R n p

/-- The basis wedge symbol attached to a `p`-element subset. -/
noncomputable def koszulWedgeSymbol {n p : ℕ} (s : KoszulWedgeIndex n p) :
    KoszulExteriorDegree R n p :=
  Finsupp.single s 1

/-- Contraction by the central sequence on a wedge-basis symbol. -/
noncomputable def koszulContraction {n p : ℕ} (x : Fin n → R)
    (s : KoszulWedgeIndex n (p + 1)) : KoszulExteriorDegree R n p :=
  koszulBoundaryData R x s

/-- The two-element sequence used in Weibel's displayed complex `K(x,y)`. -/
def twoElementKoszulSequence (x y : R) : Fin 2 → R
  | 0 => x
  | 1 => y

/-- The degree-`p` identification and differential formula of a Koszul
realization, restated in exterior/wedge notation. -/
structure KoszulExteriorDescription {n : ℕ} (x : Fin n → R)
    (hx : IsCentralSequence R x) (K : KoszulComplexRealization R x hx) where
  /-- Identification with the combinatorial exterior degree. -/
  degreeIso : ∀ p : ℕ,
    K.complex.X p ≅ ModuleCat.of R (KoszulExteriorDegree R n p)
  /-- The differential is contraction by `x` on wedge symbols. -/
  differential_wedge : ∀ (p : ℕ) (s : KoszulWedgeIndex n (p + 1)),
    (degreeIso p).hom
        (K.complex.d (p + 1) p ((degreeIso (p + 1)).inv (koszulWedgeSymbol R s))) =
      koszulContraction R x s

end LeanCategories.Homological
