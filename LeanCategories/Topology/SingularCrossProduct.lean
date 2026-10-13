/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import LeanCategories.Homological.AlexanderWhitney
public import Mathlib.AlgebraicTopology.TopologicalSimplex
public import Mathlib.Data.Finsupp.Basic

/-!
# Singular-chain shuffle product

Definition-level realization of Hatcher `FC07-C03-U089`.

Hatcher triangulates `Δ^m × Δ^n` by monotone lattice paths.  Such paths are
equivalently `(m,n)`-shuffles.  The two coordinate maps of the path simplex are
the same shuffle maps already used by the Alexander--Whitney construction in
`LeanCategories.Homological.AlexanderWhitney`.

This file records the signed simplex formula and its finite-support bilinear
extension to raw singular chains.  It does **not** assert the Leibniz boundary
identity, naturality, or descent to homology; those are result-layer content.
-/

@[expose] public noncomputable section

namespace LeanCategories.Topology

open scoped BigOperators

open LeanCategories.Homological

universe u v w

/-- Raw degree-`n` singular chains with coefficients in `R`: the free
`R`-module coordinates on continuous singular `n`-simplices. -/
abbrev RawSingularChain (R : Type w) [Zero R]
    (X : Type u) [TopologicalSpace X] (n : ℕ) :=
  C(stdSimplex ℝ (Fin (n + 1)), X) →₀ R

/-- First coordinate of the simplex indexed by an `(m,n)`-shuffle. -/
def singularShuffleHorizontalMap (m n : ℕ) (σ : Equiv.Perm (Fin (m + n))) :
    C(stdSimplex ℝ (Fin (m + n + 1)), stdSimplex ℝ (Fin (m + 1))) :=
  let h := (alexanderWhitneyShuffleHorizontalMap m n σ).toOrderHom
  ⟨stdSimplex.map h, stdSimplex.continuous_map h⟩

/-- Second coordinate of the simplex indexed by an `(m,n)`-shuffle. -/
def singularShuffleVerticalMap (m n : ℕ) (σ : Equiv.Perm (Fin (m + n))) :
    C(stdSimplex ℝ (Fin (m + n + 1)), stdSimplex ℝ (Fin (n + 1))) :=
  let h := (alexanderWhitneyShuffleVerticalMap m n σ).toOrderHom
  ⟨stdSimplex.map h, stdSimplex.continuous_map h⟩

/-- The monotone-path simplex `ℓ_σ : Δ^{m+n} → Δ^m × Δ^n` attached to a
shuffle `σ`. -/
def singularShufflePath (m n : ℕ) (σ : Equiv.Perm (Fin (m + n))) :
    C(stdSimplex ℝ (Fin (m + n + 1)),
      stdSimplex ℝ (Fin (m + 1)) × stdSimplex ℝ (Fin (n + 1))) :=
  (singularShuffleHorizontalMap m n σ).prodMk
    (singularShuffleVerticalMap m n σ)

/-- The singular `(m+n)`-simplex `(f × g) ℓ_σ` attached to singular simplices
`f`, `g` and a shuffle `σ`. -/
def singularShuffleSimplex {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y]
    {m n : ℕ}
    (f : C(stdSimplex ℝ (Fin (m + 1)), X))
    (g : C(stdSimplex ℝ (Fin (n + 1)), Y))
    (σ : Equiv.Perm (Fin (m + n))) :
    C(stdSimplex ℝ (Fin (m + n + 1)), X × Y) :=
  (f.prodMap g).comp (singularShufflePath m n σ)

/-- Hatcher's signed shuffle formula on a pair of singular simplex generators.

Only `(m,n)`-shuffles contribute.  Their permutation sign is used as the
coefficient of the corresponding path simplex. -/
noncomputable def singularCrossProductGenerator
    (R : Type w) [CommRing R]
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    {m n : ℕ}
    (f : C(stdSimplex ℝ (Fin (m + 1)), X))
    (g : C(stdSimplex ℝ (Fin (n + 1)), Y)) :
    RawSingularChain R (X × Y) (m + n) := by
  classical
  exact ∑ σ : Equiv.Perm (Fin (m + n)),
    if alexanderWhitneyIsShuffle m n σ then
      Finsupp.single (singularShuffleSimplex f g σ)
        ((((Equiv.Perm.sign σ : ℤˣ) : ℤ) : R))
    else 0

/-- Bilinear extension of Hatcher's signed shuffle formula from singular
simplex generators to raw singular chains.

This is only the underlying chain-level operation.  No claim that it commutes
with the singular differential is bundled into the definition. -/
noncomputable def singularCrossProduct
    (R : Type w) [CommRing R]
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    {m n : ℕ}
    (a : RawSingularChain R X m) (b : RawSingularChain R Y n) :
    RawSingularChain R (X × Y) (m + n) := by
  classical
  exact a.sum fun f af =>
    b.sum fun g bg =>
      (af * bg) • singularCrossProductGenerator R f g

end LeanCategories.Topology
