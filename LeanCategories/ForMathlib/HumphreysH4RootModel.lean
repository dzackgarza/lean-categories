/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Quaternion
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Real.Sqrt
public import Mathlib.GroupTheory.Perm.Sign

@[expose] public section

/-!
# Humphreys' quaternionic coordinate model for H4

Humphreys, *Reflection Groups and Coxeter Groups*, Section 2.13, pp. 47--48
(FC15-C02-U032), defines the 120 roots from three quaternion coordinate vectors by arbitrary
sign changes and even coordinate permutations. He then displays four simple roots.

This file records exactly that finite-coordinate carrier and displayed base. The claims that the
carrier has 120 elements, is a multiplicative group, satisfies the root-system axioms, and has type
`H4` are results about these data and are not included here.
-/

namespace LeanCategories.HumphreysH4

/-- Humphreys' constant `a = cos (pi / 5) = (1 + sqrt 5) / 4`. -/
noncomputable def a : ℝ :=
  (1 + Real.sqrt 5) / 4

/-- Humphreys' constant `b = cos (2 * pi / 5) = (-1 + sqrt 5) / 4`. -/
noncomputable def b : ℝ :=
  (-1 + Real.sqrt 5) / 4

/-- Coordinatewise choices of arbitrary signs. -/
def IsSignChoice (epsilon : Fin 4 → ℝ) : Prop :=
  ∀ i, epsilon i = 1 ∨ epsilon i = -1

/-- The vectors obtained from `v` by an even coordinate permutation and arbitrary sign changes. -/
def signedEvenOrbit (v : Fin 4 → ℝ) : Set (Fin 4 → ℝ) :=
  {x | ∃ sigma : Equiv.Perm (Fin 4), Equiv.Perm.sign sigma = 1 ∧
    ∃ epsilon : Fin 4 → ℝ, IsSignChoice epsilon ∧
      x = fun i => epsilon i * v (sigma i)}

/-- The coordinate vector of the quaternion `1`. -/
def seedOne : Fin 4 → ℝ :=
  ![1, 0, 0, 0]

/-- The coordinate vector of `(1 + i + j + k) / 2`. -/
def seedHalf : Fin 4 → ℝ :=
  ![1 / 2, 1 / 2, 1 / 2, 1 / 2]

/-- The coordinate vector of `a + i / 2 + b * j`. -/
noncomputable def seedGolden : Fin 4 → ℝ :=
  ![a, 1 / 2, b, 0]

/-- The literal 120-root coordinate carrier displayed by Humphreys. -/
noncomputable def rootCoordinates : Set (Fin 4 → ℝ) :=
  signedEvenOrbit seedOne ∪ signedEvenOrbit seedHalf ∪ signedEvenOrbit seedGolden

/-- Humphreys' coordinate carrier, regarded as a set of real quaternions. -/
noncomputable def rootCarrier : Set (Quaternion ℝ) :=
  (Quaternion.equivTuple ℝ).symm '' rootCoordinates

/-- The four displayed simple-root coordinate vectors, in source order. -/
noncomputable def simpleRootCoordinates : Fin 4 → Fin 4 → ℝ :=
  ![![a, -1 / 2, b, 0],
    ![-a, 1 / 2, b, 0],
    ![1 / 2, b, -a, 0],
    ![-1 / 2, -a, 0, b]]

/-- The four displayed simple roots, regarded as real quaternions. -/
noncomputable def simpleRoot (i : Fin 4) : Quaternion ℝ :=
  (Quaternion.equivTuple ℝ).symm (simpleRootCoordinates i)

end LeanCategories.HumphreysH4
