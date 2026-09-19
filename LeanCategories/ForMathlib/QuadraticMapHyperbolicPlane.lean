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

The reference construction `XY` is the split form `q(a, b) = ab`. Peters--Sterk,
*Symmetric and Quadratic Forms* (June 2024), Chapter 3 (`FC11-C03-U003`), use half the
polarization as their associated symmetric form and normalize the displayed hyperbolic basis by
`e · f = 1`. Their literal quadratic-form normalization is therefore `q(a, b) = 2ab`, provided
below as `hyperbolicPlane`. Over the source's fields of characteristic different from two, the two
forms are equivalent by rescaling one basis vector by `2`.
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

/-- The Peters--Sterk hyperbolic plane in a supplied basis: `q(a, b) = 2ab`.

With the source convention `x · y = (q (x + y) - q x - q y) / 2`, the two basis vectors
are isotropic and pair to `1`.
-/
noncomputable abbrev hyperbolicPlane (b : Basis (Fin 2) R V) : QuadraticForm R V :=
  (2 : R) • XY b

@[simp]
lemma hyperbolicPlane_apply (b : Basis (Fin 2) R V) (v : V) :
    hyperbolicPlane b v = 2 * (b.repr v 0 * b.repr v 1) := by
  simp [hyperbolicPlane, XY]

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
