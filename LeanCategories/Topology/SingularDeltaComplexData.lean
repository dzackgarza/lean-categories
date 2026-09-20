/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Topology.DeltaComplex
public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.Topology.CWComplex.Classical.Basic

/-!
# Singular Delta-complex characteristic-map data

Definition-level realization of Hatcher FC07-CA-U026.

A singular Delta-complex is a CW complex equipped with distinguished
standard-simplex characteristic maps. Unlike an ordinary Delta-complex, a
face is allowed to collapse: restricting a characteristic map to a
codimension-one face factors through a lower-dimensional characteristic map
via an order-preserving vertex-surjection.

Sweep III records the characteristic maps and the two source predicates:
their open interiors are the chosen CW open cells, and their face
restrictions have the required collapsed-simplex form. Existence of such
structures on quotients, mapping cylinders/cones, and product subdivision
comparisons are result/construction theorems and are not asserted here.
-/

@[expose] public section

noncomputable section

namespace LeanCategories.Topology

open Set
open _root_.Topology

universe u

/-- The affine map of standard simplices induced by an order-preserving map
of their ordered vertex sets. -/
def stdSimplexOrderMap {m k : ℕ} (q : Fin (m + 1) →o Fin (k + 1)) :
    C(stdSimplex ℝ (Fin (m + 1)), stdSimplex ℝ (Fin (k + 1))) :=
  ⟨stdSimplex.map q, stdSimplex.continuous_map _⟩

/-- Distinguished simplex characteristic maps on an already supplied CW
complex. No face or compatibility proof is stored in the data carrier. -/
structure SingularDeltaComplexData
    (X : Type u) [TopologicalSpace X] [CWComplex (Set.univ : Set X)] where
  characteristic : ∀ n : ℕ,
    _root_.Topology.CWComplex.cell (Set.univ : Set X) n →
      C(stdSimplex ℝ (Fin (n + 1)), X)

/-- Hatcher's singular-Delta-complex conditions on the raw characteristic
maps.

The first clause identifies each simplex interior with its chosen CW open
cell. The second says every codimension-one face restriction factors through
some lower-dimensional characteristic map by a surjective ordered vertex
map; this is precisely the allowed face collapse. -/
def IsSingularDeltaComplexData
    {X : Type u} [TopologicalSpace X] [CWComplex (Set.univ : Set X)]
    (D : SingularDeltaComplexData X) : Prop :=
  (∀ (n : ℕ) (e : _root_.Topology.CWComplex.cell (Set.univ : Set X) n),
      D.characteristic n e ''
          {x : stdSimplex ℝ (Fin (n + 1)) | IsStdSimplexInterior x} =
        _root_.Topology.RelCWComplex.openCell (C := (Set.univ : Set X)) n e) ∧
    ∀ (n : ℕ)
      (e : _root_.Topology.CWComplex.cell (Set.univ : Set X) (n + 1))
      (i : Fin (n + 2)),
      ∃ (k : ℕ)
        (t : _root_.Topology.CWComplex.cell (Set.univ : Set X) k)
        (q : Fin (n + 1) →o Fin (k + 1)),
        Function.Surjective q ∧
          (D.characteristic (n + 1) e).comp (stdSimplexFaceInclusion i) =
            (D.characteristic k t).comp (stdSimplexOrderMap q)

end LeanCategories.Topology
