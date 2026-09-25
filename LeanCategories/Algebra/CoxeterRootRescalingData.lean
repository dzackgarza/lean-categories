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

Sweep III records the exact ratio graph, selects a scalar assignment by that
graph, and takes the `ℤ`-span of the rescaled simple roots.  Existence and
coherence of the selected assignment, and `W`-stability / full-lattice
properties of the resulting span, are result-layer obligations.
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

/-- A source-faithful chosen coherent rescaling assignment.

FC15-C06-U011 later proves that the exact ratio graph is inhabited under the
source crystallographic hypotheses. -/
def coxeterRootRescalingData {S : Type u} (M : CoxeterMatrix S) : S → ℝ :=
  Classical.epsilon (IsCoxeterRootRescalingData M)

/-- The rescaled simple root `λ_s = c_s α_s` in the free geometric coordinate
space with simple-root basis indexed by `S`. -/
def coxeterRescaledSimpleRootData {S : Type u}
    (M : CoxeterMatrix S) (s : S) : S → ℝ := by
  classical
  exact coxeterRootRescalingData M s • Pi.single s (1 : ℝ)

/-- Humphreys' integral root-rescaling lattice: the `ℤ`-span of the rescaled
simple roots `λ_s`.

That this span is a full lattice and is stable under the geometric Coxeter
representation is result content. -/
def coxeterRootRescalingLatticeData {S : Type u}
    (M : CoxeterMatrix S) : Submodule ℤ (S → ℝ) :=
  Submodule.span ℤ (Set.range (coxeterRescaledSimpleRootData M))

end LeanCategories.Algebra
