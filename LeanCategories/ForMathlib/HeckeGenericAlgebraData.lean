/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.ForMathlib.HeckeEndomorphismRealizationData

/-!
# Generic Coxeter Hecke-algebra data

Definition-level realization of Humphreys FC15-C07-U004, following the
source-general interface in Atlas.

Humphreys first fixes the free module E with basis T_w and parameters
a_s,b_s, then proves in U003 that there is a unique associative
A-algebra multiplication satisfying the two simple-generator rules.
U004 only names the resulting object the generic algebra.

Accordingly, this file packages a multiplication on the already-owned
free module together with exactly the algebra and basis-rule data.
Existence and uniqueness of such data are U003 result content; no
construction of those proofs is attempted here.
-/

@[expose] public noncomputable section

namespace LeanCategories.Hecke

universe u v w

variable {B : Type u} {W : Type v} {A : Type w}
variable [Group W] [CommRing A]
variable {M : CoxeterMatrix B}

/-- The distinguished source basis vector T_w in the generic module. -/
def genericBasisVector (w : W) : GenericModule A W :=
  Finsupp.single w 1

/-- Data of Humphreys' generic algebra on the fixed free module E.

The fields are properties of the multiplication whose existence and
uniqueness are established by FC15-C07-U003. Packaging them here gives
the object named in U004 without reproving U003. -/
structure GenericAlgebraData
    (cs : CoxeterSystem M W) (a b : B → A) where
  /-- Multiplication on the free module E. -/
  mul : GenericModule A W → GenericModule A W → GenericModule A W
  /-- Associativity of the supplied multiplication. -/
  mul_assoc : ∀ x y z, mul (mul x y) z = mul x (mul y z)
  /-- T_1 is a left identity. -/
  one_mul : ∀ x, mul (genericBasisVector (A := A) (1 : W)) x = x
  /-- T_1 is a right identity. -/
  mul_one : ∀ x, mul x (genericBasisVector (A := A) (1 : W)) = x
  /-- Right additivity. -/
  mul_add : ∀ x y z, mul x (y + z) = mul x y + mul x z
  /-- Left additivity. -/
  add_mul : ∀ x y z, mul (x + y) z = mul x z + mul y z
  /-- Right A-linearity. -/
  mul_smul : ∀ (r : A) x y, mul x (r • y) = r • mul x y
  /-- Left A-linearity. -/
  smul_mul : ∀ (r : A) x y, mul (r • x) y = r • mul x y
  /-- The length-increasing simple-generator rule. -/
  length_up : ∀ (s : B) (x : W),
    cs.length (cs.simple s * x) > cs.length x →
      mul (genericBasisVector (A := A) (cs.simple s))
          (genericBasisVector (A := A) x) =
        genericBasisVector (A := A) (cs.simple s * x)
  /-- The length-decreasing simple-generator rule. -/
  length_down : ∀ (s : B) (x : W),
    cs.length (cs.simple s * x) < cs.length x →
      mul (genericBasisVector (A := A) (cs.simple s))
          (genericBasisVector (A := A) x) =
        a s • genericBasisVector (A := A) x +
          b s • genericBasisVector (A := A) (cs.simple s * x)

end LeanCategories.Hecke
