/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.GroupTheory.Coxeter.Matrix
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.LinearAlgebra.Pi

/-!
# Root-rescaling lattices for crystallographic Coxeter groups

Definition-level realization of Humphreys FC15-C06-U012.

For a crystallographic Coxeter system, Humphreys chooses positive scalars
`c_s` so that `λ_s = c_s α_s` span an integral lattice.  Along Coxeter edges
of labels `3,4,6,∞` the allowed ratios are respectively

* `1`,
* `√2` or `1/√2`,
* `√3` or `1/√3`, and
* `1`.

Mathlib uses the value `0` for the Coxeter label `∞`.  The preceding source
result FC15-C06-U011 supplies exactly the circuit-parity condition ensuring
that these local ratios admit a globally coherent positive assignment.

Sweep III records the exact ratio graph, constructs the subtype of all scalar
assignments satisfying it, and takes the `ℤ`-span of the rescaled simple roots
for each such assignment.  Existence of an admissible assignment and
`W`-stability / full-lattice properties of the resulting span are
result-layer obligations.
-/

@[expose] public noncomputable section

namespace LeanCategories.Algebra

universe u

/-- Exact local ratio constraints from Humphreys §6.6.

No condition is imposed on label `2` (there is no Coxeter-graph edge), and
labels outside `{2,3,4,6,∞}` are left unconstrained because U011 proves that
they do not occur under the crystallographic hypotheses. -/
def IsCoxeterRootRescalingData {S : Type u}
    (M : CoxeterMatrix S) (c : S → ℝ) : Prop :=
  (∀ s : S, 0 < c s) ∧
    ∀ s t : S, s ≠ t →
      match M s t with
      | 3 => c s = c t
      | 4 => c s = Real.sqrt 2 * c t ∨ c t = Real.sqrt 2 * c s
      | 6 => c s = Real.sqrt 3 * c t ∨ c t = Real.sqrt 3 * c s
      | 0 => c s = c t
      | _ => True

/-- The carrier of all source-faithful coherent rescaling assignments.  No
unwitnessed assignment is selected. -/
def CoxeterRootRescalingData {S : Type u} (M : CoxeterMatrix S) :=
  {c : S → ℝ // IsCoxeterRootRescalingData M c}

/-- The rescaled simple root `λ_s = c_s α_s` in the free geometric coordinate
space with simple-root basis indexed by `S`. -/
def coxeterRescaledSimpleRootData {S : Type u}
    {M : CoxeterMatrix S} (c : CoxeterRootRescalingData M) (s : S) : S → ℝ := by
  classical
  exact c.1 s • Pi.single s (1 : ℝ)

/-- Humphreys' integral root-rescaling lattice: the `ℤ`-span of the rescaled
simple roots `λ_s`.

That this span is a full lattice and is stable under the geometric Coxeter
representation is result content. -/
def coxeterRootRescalingLatticeData {S : Type u}
    {M : CoxeterMatrix S} (c : CoxeterRootRescalingData M) : Submodule ℤ (S → ℝ) :=
  Submodule.span ℤ (Set.range (coxeterRescaledSimpleRootData c))

/-- The family of all integral spans obtained from admissible source
rescalings.  Under Humphreys' crystallographic hypotheses U011 proves this
family is inhabited. -/
def coxeterRootRescalingLatticeFamilyData {S : Type u}
    (M : CoxeterMatrix S) : Set (Submodule ℤ (S → ℝ)) :=
  {L | ∃ c : CoxeterRootRescalingData M, L = coxeterRootRescalingLatticeData c}

end LeanCategories.Algebra
