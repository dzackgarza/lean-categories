/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicTopology.SingularSet

/-!
# Singular cup-product formula data

Definition-level transcription of Hatcher FC07-C03-U013.

At the cochain level, the cup product evaluates the first cochain on the front
face of a singular simplex and the second cochain on the back face, then
multiplies the two values.  Sweep III records precisely that formula.  The
Leibniz identity, preservation of cocycles, independence of representatives,
and descent to singular cohomology are result content.
-/

@[expose] public section

noncomputable section

namespace LeanCategories.Topology

universe u v

/-- Raw degree-`n` singular cochain data with values in `R`, represented by its
values on singular `n`-simplices.  Such functions are the basis-level data of
homomorphisms out of the free singular chain group. -/
abbrev RawSingularCochain (X : Type u) [TopologicalSpace X] (R : Type v) (n : ℕ) :=
  C(stdSimplex ℝ (Fin (n + 1)), X) → R

/-- Inclusion of the front `p`-face into the standard `(p+q)`-simplex. -/
def singularCupFrontFace (p q : ℕ) :
    C(stdSimplex ℝ (Fin (p + 1)), stdSimplex ℝ (Fin (p + q + 1))) :=
  ⟨stdSimplex.map (fun i => Fin.castLE (by omega) i), stdSimplex.continuous_map _⟩

/-- Inclusion of the back `q`-face into the standard `(p+q)`-simplex. -/
def singularCupBackFace (p q : ℕ) :
    C(stdSimplex ℝ (Fin (q + 1)), stdSimplex ℝ (Fin (p + q + 1))) :=
  ⟨stdSimplex.map (fun i => ⟨p + i, by omega⟩), stdSimplex.continuous_map _⟩

/-- Hatcher's front-face/back-face formula for the cup product of raw singular
cochains.  No assertion that this operation descends to cohomology is included
at the definition layer. -/
def singularCupCochain {X : Type u} [TopologicalSpace X]
    {R : Type v} [Mul R] (p q : ℕ)
    (φ : RawSingularCochain X R p) (ψ : RawSingularCochain X R q) :
    RawSingularCochain X R (p + q) :=
  fun σ =>
    φ (σ.comp (singularCupFrontFace p q)) *
      ψ (σ.comp (singularCupBackFace p q))

end LeanCategories.Topology
