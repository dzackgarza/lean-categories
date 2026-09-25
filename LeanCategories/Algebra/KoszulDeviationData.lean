/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Homological.KoszulHomology
public import Mathlib.RingTheory.RegularLocalRing.Defs

/-!
# Koszul deviation data

Definition-level realization of Matsumura, *Commutative Ring Theory*, §21,
pp. 169--171 (`FC13-C07-U046`, `FC13-C07-U049`).

For a Noetherian local ring `A`, Matsumura chooses a minimal generating
system `x` of the maximal ideal and defines

  ε_p(A) = dim_k H_p(x; A),  k = A / m.

The residue-field action on Koszul homology follows from the result that the
maximal ideal annihilates that homology. Sweep III does not prove that
result. Instead, the candidate package below records a residue-field module
together with the exact comparison graph to the already-realized
`A`-module Koszul homology, and `Classical.epsilon` selects the
source-prescribed package. Existence, basis-independence, and the regularity
criterion remain result-layer statements.
-/

@[expose] public noncomputable section

open IsLocalRing
open LeanCategories.Homological

namespace LeanCategories.Algebra

universe u

variable (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]

/-- Candidate data for Matsumura's Koszul deviations.

`x` is intended to be a minimal generating system of the maximal ideal.
`homology p` is a candidate residue-field module structure on the actual
Koszul homology in degree `p`. -/
structure KoszulDeviationCandidateData where
  n : ℕ
  x : Fin n → A
  homology : ℕ → ModuleCat.{u} (ResidueField A)

instance : Nonempty (KoszulDeviationCandidateData A) :=
  ⟨{
    n := 0
    x := Fin.elim0
    homology := fun _ => ModuleCat.of (ResidueField A) (ResidueField A)
  }⟩

/-- Exact source graph for a Koszul-deviation candidate.

The first two clauses say that `x` is a generating system of minimal
cardinality for the maximal ideal. The final clause identifies each proposed
residue-field homology module with the already-realized `A`-module
`H_p(x;A)`, with scalar multiplication agreeing through
`A → A/m`. No existence of such comparisons is proved here. -/
def IsKoszulDeviationCandidateData (D : KoszulDeviationCandidateData A) : Prop :=
  Ideal.span (Set.range D.x) = maximalIdeal A ∧
    D.n = (maximalIdeal A).spanFinrank ∧
    ∀ p : ℕ,
      ∃ e :
          (D.homology p : Type u) ≃+
            (LeanCategories.Homological.koszulCoefficientHomology
              A D.x (ModuleCat.of A A) p : Type u),
        ∀ (a : A) (h : D.homology p),
          e ((IsLocalRing.residue A a) • h) = a • e h

/-- Matsumura's selected minimal-basis/residue-homology presentation.

The theorem layer proves that this selected candidate satisfies
`IsKoszulDeviationCandidateData`. -/
def koszulDeviationCandidateData : KoszulDeviationCandidateData A :=
  Classical.epsilon (IsKoszulDeviationCandidateData A)

/-- Matsumura's Koszul deviation
`ε_p(A) = dim_{A/m} H_p(x;A)`. -/
def koszulDeviation (p : ℕ) : ℕ :=
  Module.finrank (ResidueField A) ((koszulDeviationCandidateData A).homology p)

/-- Matsumura's definition of a complete-intersection local ring:
`ε₁(A) + dim A = embdim A`.

The embedding dimension is the minimal number of generators of the maximal
ideal, represented by `spanFinrank`. -/
def IsCompleteIntersectionLocalRingData : Prop :=
  (koszulDeviation A 1 : WithBot ℕ∞) + ringKrullDim A =
    ((maximalIdeal A).spanFinrank : WithBot ℕ∞)

end LeanCategories.Algebra
