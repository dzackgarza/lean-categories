/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Convex.StdSimplex

/-!
# Barycentric subdivision data

Definition-level realization of Hatcher FC07-C02-U035.

An `r`-simplex in the barycentric subdivision of the standard `n`-simplex is
represented by a strict flag of `r + 1` nonempty faces.  Its vertices are the
barycenters of those faces, with barycentric coordinate `1 / |F|` on a face
`F` and zero off `F`.

Sweep III keeps the raw face flags and coordinate formulas as data.  Facts that
these coordinates lie in the standard simplex, and comparisons with the
inductive cone construction or the singular-chain subdivision operator, are
result content.
-/

@[expose] public section

noncomputable section

namespace LeanCategories.Topology

/-- Raw face-flag data for an `r`-simplex in the barycentric subdivision of the
standard `n`-simplex. -/
abbrev BarycentricFaceFlag (n r : ℕ) :=
  Fin (r + 1) → Finset (Fin (n + 1))

/-- The source condition for a barycentric-subdivision simplex: every face is
nonempty and the faces form a strict increasing flag. -/
def IsBarycentricFaceFlag {n r : ℕ} (F : BarycentricFaceFlag n r) : Prop :=
  (∀ i, (F i).Nonempty) ∧
    ∀ i j, i < j → F i ⊂ F j

/-- Barycentric coordinates of the barycenter of a face of the standard
`n`-simplex.  The empty face is sent to the zero coordinate vector; valid
barycentric-subdivision flags exclude it. -/
def faceBarycenterCoordinates {n : ℕ} (F : Finset (Fin (n + 1))) :
    Fin (n + 1) → ℝ :=
  fun i => if i ∈ F then (F.card : ℝ)⁻¹ else 0

/-- The ordered vertices of the geometric simplex associated to a face flag,
written in barycentric coordinates of the original standard simplex. -/
def barycentricSubdivisionVertices {n r : ℕ} (F : BarycentricFaceFlag n r) :
    Fin (r + 1) → (Fin (n + 1) → ℝ) :=
  fun i => faceBarycenterCoordinates (F i)

/-- The collection of raw face flags that are simplices of the barycentric
subdivision. -/
def barycentricSubdivision (n r : ℕ) : Set (BarycentricFaceFlag n r) :=
  {F | IsBarycentricFaceFlag F}

end LeanCategories.Topology
