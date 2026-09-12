/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.Data.Finsupp.Defs

/-!
# Koszul complexes for central sequences

Weibel, *An Introduction to Homological Algebra* (1994), §4.5, pp. 111--114
(FC05-C04-U068).

For a finite central sequence `x₁,…,xₙ` in an associative ring, the degree-`p`
Koszul module is free on `p`-element subsets.  On the basis symbol `e_I` the
differential is the alternating sum obtained by deleting one index and
multiplying by the corresponding `x_i`.

This file records an actual chain-complex realization together with those exact
degree and differential formulas.  Existence from the formulas (in particular
`d²=0`) is result-level content.
-/

@[expose] public section

namespace LeanCategories.Homological

open CategoryTheory
open scoped BigOperators

universe u

variable (R : Type u) [Ring R]

/-- A finite sequence consists of central elements of `R`. -/
def IsCentralSequence {n : ℕ} (x : Fin n → R) : Prop :=
  ∀ (i : Fin n) (r : R), x i * r = r * x i

/-- Basis indices for the degree-`p` Koszul module on `n` generators. -/
abbrev KoszulBasisIndex (n p : ℕ) :=
  {s : Finset (Fin n) // s.card = p}

/-- The free left `R`-module in degree `p` of the combinatorial Koszul complex. -/
abbrev KoszulDegree (n p : ℕ) :=
  KoszulBasisIndex n p →₀ R

/-- Position of `j` in the increasing wedge symbol represented by `s`. -/
def koszulPosition {n p : ℕ} (s : KoszulBasisIndex n p) (j : Fin n) : ℕ :=
  (s.1.filter fun i => i < j).card

/-- Delete an index from a Koszul wedge-basis symbol. -/
def koszulEraseIndex {n p : ℕ} (s : KoszulBasisIndex n (p + 1))
    (j : Fin n) (hj : j ∈ s.1) : KoszulBasisIndex n p :=
  ⟨s.1.erase j, by
    rw [Finset.card_erase_of_mem hj, s.2]
    simp⟩

/-- The alternating boundary of a degree-`p+1` basis symbol. -/
noncomputable def koszulBoundaryData {n p : ℕ} (x : Fin n → R)
    (s : KoszulBasisIndex n (p + 1)) : KoszulDegree R n p :=
  ∑ j : s.1,
    Finsupp.single (koszulEraseIndex s j.1 j.2)
      (((-1 : R) ^ koszulPosition s j.1) * x j.1)

/-- Source-faithful realization of the Koszul complex of a finite central sequence. -/
structure KoszulComplexRealization {n : ℕ} (x : Fin n → R)
    (hx : IsCentralSequence R x) where
  /-- The realized chain complex. -/
  complex : ChainComplex (ModuleCat R) ℕ
  /-- Degree `p` is the free module on `p`-element wedge symbols. -/
  degreeIso : ∀ p : ℕ,
    complex.X p ≅ ModuleCat.of R (KoszulDegree R n p)
  /-- Differential on a basis symbol is the alternating deletion formula. -/
  differential_basis : ∀ (p : ℕ) (s : KoszulBasisIndex n (p + 1)),
    (degreeIso p).hom
        (complex.d (p + 1) p
          ((degreeIso (p + 1)).inv (Finsupp.single s 1))) =
      koszulBoundaryData R x s

/-- The one-element sequence used for `K(x) : 0 → R → R → 0`. -/
def oneElementKoszulSequence (x : R) : Fin 1 → R :=
  fun _ => x

end LeanCategories.Homological
