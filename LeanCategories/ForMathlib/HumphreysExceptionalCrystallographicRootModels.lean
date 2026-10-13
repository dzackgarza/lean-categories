/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.ForMathlib.HumphreysF4RootModel
public import LeanCategories.ForMathlib.HumphreysE8RootModel

/-!
# Humphreys' exceptional crystallographic root models

Definition-level completion of Humphreys, *Reflection Groups and Coxeter
Groups*, §2.10, pp. 42--43 (FC15-C02-U028).

The already-existing HumphreysF4 and HumphreysE8 owners give the
source's Euclidean/lattice carriers and displayed simple systems for
F₄, E₈, and the canonical E₇/E₆ subsystems. This file adds the
remaining G₂ Euclidean model and the displayed highest-root data from
the same source.

No claim that these carriers satisfy the root-system axioms, that the
displayed vectors are highest, or that the carriers have the named
Dynkin types is made here; those are result clauses.
-/

@[expose] public noncomputable section

open scoped BigOperators

namespace LeanCategories

namespace HumphreysG2

/-- The ambient coordinate space for the source's G₂ model. -/
abbrev Space := Fin 3 → ℝ

/-- The hyperplane x₁+x₂+x₃=0 used as the real root space. -/
def hyperplane : Set Space :=
  {x | ∑ i, x i = 0}

/-- The intersection of the standard integer lattice with the G₂
root hyperplane. -/
def lattice : Set Space :=
  {x | x ∈ hyperplane ∧ ∃ z : Fin 3 → ℤ, x = fun i => (z i : ℝ)}

/-- Squared Euclidean length in the coordinate model. -/
def squaredLength (x : Space) : ℝ :=
  ∑ i, x i * x i

/-- Humphreys' G₂ root carrier: lattice vectors of squared length
2 or 6. -/
def roots : Set Space :=
  {x | x ∈ lattice ∧ (squaredLength x = 2 ∨ squaredLength x = 6)}

/-- The displayed simple system (ε₁-ε₂, -2ε₁+ε₂+ε₃). -/
def simpleRoot : Fin 2 → Space := ![
  ![1, -1, 0],
  ![-2, 1, 1]]

/-- The set underlying the displayed G₂ simple system. -/
def simpleRoots : Set Space :=
  Set.range simpleRoot

/-- The source's displayed highest root 2ε₃-ε₁-ε₂. -/
def highestRoot : Space :=
  ![-1, -1, 2]

end HumphreysG2

namespace HumphreysF4

/-- The source's displayed highest F₄ root ε₁+ε₂. -/
def highestRoot : Space :=
  ![1, 1, 0, 0]

end HumphreysF4

namespace HumphreysE8

/-- The source's displayed highest E₈ root ε₇+ε₈. -/
def highestRoot : Space :=
  ![0, 0, 0, 0, 0, 0, 1, 1]

/-- The displayed simple system of the canonical E₇ subsystem:
the first seven roots of the E₈ base. -/
def e7SimpleRoot (i : Fin 7) : Space :=
  simpleRoot i.castSucc

/-- The source's displayed highest E₇ root ε₈-ε₇. -/
def e7HighestRoot : Space :=
  ![0, 0, 0, 0, 0, 0, -1, 1]

/-- The displayed simple system of the canonical E₆ subsystem:
the first six roots of the E₈ base. -/
def e6SimpleRoot (i : Fin 6) : Space :=
  simpleRoot (Fin.castAdd 2 i)

/-- The source's displayed highest E₆ root
(ε₁+ε₂+ε₃+ε₄+ε₅-ε₆-ε₇+ε₈)/2. -/
def e6HighestRoot : Space :=
  ![(1 : ℝ) / 2, (1 : ℝ) / 2, (1 : ℝ) / 2, (1 : ℝ) / 2,
    (1 : ℝ) / 2, -(1 : ℝ) / 2, -(1 : ℝ) / 2, (1 : ℝ) / 2]

end HumphreysE8

end LeanCategories
