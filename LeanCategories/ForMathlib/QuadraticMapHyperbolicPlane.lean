/-
Copyright (c) 2026 Nirvana Coppola, María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nirvana Coppola, María Inés de Frutos-Fernández, Chi-Yun Hsu
-/
module

public import Mathlib.LinearAlgebra.QuadraticForm.IsometryEquiv
public import Mathlib.Tactic

/-!
# The hyperbolic plane as a quadratic form

This ports the hyperbolic-plane construction from
`mariainesdff/HassePrinciple@47df8f51939b364e678893d54e8a3faf6ec52302`,
`HassePrinciple/QuadraticForm/Basic.lean`. The reference is released under Apache-2.0.

The construction realizes the split binary quadratic form called the hyperbolic plane in
Peters--Sterk, *Symmetric and Quadratic Forms* (June 2024), Chapter 3 (`FC11-C03-U003`).
Over the source's fields of characteristic different from two, the associated symmetric
bilinear form uses half the polarization. The reference formula itself works over any
commutative ring; this does not assert nondegeneracy for arbitrary coefficient modules.
-/

@[expose] public section

namespace QuadraticMap

open Module

variable {R V W : Type*} [CommRing R]
  [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]

/-- The split binary quadratic form `XY` in coordinates supplied by `b`. -/
noncomputable abbrev XY (b : Basis (Fin 2) R V) : QuadraticForm R V where
  toFun v := b.repr v 0 * b.repr v 1
  toFun_smul r v := by
    simp
    ring
  exists_companion' := by
    let B : LinearMap.BilinMap R V R :=
      { toFun v :=
          { toFun w := b.repr v 0 * b.repr w 1 + b.repr w 0 * b.repr v 1
            map_add' w z := by simp; ring
            map_smul' r w := by simp; ring }
        map_add' w z := by ext; simp; ring
        map_smul' r w := by ext; simp; ring }
    exact ⟨B, fun v w ↦ by simp [B]; ring⟩

/-- A quadratic form is hyperbolic when it is equivalent to the split binary form `XY`. -/
def IsHyperbolic (Q : QuadraticForm R V) : Prop :=
  Q.Equivalent (XY (Pi.basisFun R (Fin 2)))

/-- Every coordinate presentation of `XY` is hyperbolic. -/
lemma XY_isHyperbolic (b : Basis (Fin 2) R V) : IsHyperbolic (XY b) :=
  ⟨{ toLinearEquiv := b.equivFun
     map_app' v := by simp }⟩

/-- Hyperbolicity is preserved under equivalence of quadratic forms. -/
lemma Equivalent.isHyperbolic {Q : QuadraticForm R V} {Q' : QuadraticForm R W}
    (hQ : Q.IsHyperbolic) (heq : Q'.Equivalent Q) : Q'.IsHyperbolic :=
  heq.trans hQ

end QuadraticMap
