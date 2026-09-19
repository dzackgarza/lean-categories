/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Convex.StdSimplex

/-!
# Delta-complex structures

This file formalizes Hatcher's definition of a Delta-complex structure from *Algebraic
Topology*, Section 2.1, p. 103 (`FC07-C02-U001`). A structure on a topological space `X`
consists of characteristic maps from standard simplices such that their open-simplex
restrictions partition `X`, each codimension-one face restriction is another characteristic
map, and the topology on `X` is the final topology for the characteristic maps.
-/

@[expose] public section

noncomputable section

namespace LeanCategories.Topology

open Set

universe u v

/-- The relative interior of the standard `n`-simplex: all barycentric coordinates are
strictly positive. -/
def IsStdSimplexInterior {n : ℕ} (x : stdSimplex ℝ (Fin (n + 1))) : Prop :=
  ∀ i, 0 < x i

/-- The inclusion of the `i`th codimension-one face of the standard `(n+1)`-simplex.

The native simplex map induced by `Fin.succAbove i` inserts the missing vertex with
barycentric coordinate zero. -/
def stdSimplexFaceInclusion {n : ℕ} (i : Fin (n + 2)) :
    C(stdSimplex ℝ (Fin (n + 1)), stdSimplex ℝ (Fin (n + 2))) :=
  ⟨stdSimplex.map (Fin.succAbove i), stdSimplex.continuous_map _⟩

/-- A Delta-complex structure on a supplied topological space, in the sense of Hatcher,
Section 2.1.

`Simplex n` indexes the `n`-simplices. The unique dependent pair in `interior_partition`
expresses simultaneously that every point lies in an open simplex, that distinct open
simplices are disjoint, and that every characteristic map is injective on its open simplex.
The last field says that a subset of `X` is open exactly when its preimage under every
characteristic map is open. -/
structure DeltaComplex (X : Type u) [TopologicalSpace X] where
  Simplex : ℕ → Type v
  characteristic : ∀ n, Simplex n → C(stdSimplex ℝ (Fin (n + 1)), X)
  interior_partition : ∀ x : X,
    ∃! p : Σ n : ℕ, Σ s : Simplex n,
      {y : stdSimplex ℝ (Fin (n + 1)) // IsStdSimplexInterior y},
      characteristic p.1 p.2.1 p.2.2 = x
  face : ∀ (n : ℕ) (s : Simplex (n + 1)) (i : Fin (n + 2)),
    ∃ t : Simplex n,
      (characteristic (n + 1) s).comp (stdSimplexFaceInclusion i) = characteristic n t
  topology_eq :
    (⋁ n : ℕ, ⋁ s : Simplex n,
      TopologicalSpace.coinduced (characteristic n s) inferInstance) =
      inferInstanceAs (TopologicalSpace X)

end LeanCategories.Topology
