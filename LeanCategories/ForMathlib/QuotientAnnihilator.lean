/-
Copyright (c) 2026 The AlgebraicJacobian authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AlgebraicJacobian Contributors
-/
module

public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.Data.ZMod.Basic

/-!
# Faithfulness over the annihilator quotient

FC04-C02-U020: Atiyah–Macdonald, *Introduction to Commutative Algebra* (1969), p. 20,
the definition of a faithful module following the quotient action.

Reference port of `AlgebraicGeometry.annihilator_quotientAnnihilator_eq_bot` and
`AlgebraicGeometry.faithfulSMul_quotientAnnihilator` from
`AxelDlv00/LeanAlgebraicGeometry`, revision `f48ddbf1eb13625e8c41acbd549cc4522fb8b79f`,
`MainProjects/Algebraic-Jacobian-Challenge/AlgebraicJacobian/Picard/SchematicSupport.lean`.
Only the algebraic proofs are ported; the construction of the quotient action is Mathlib's.
-/

@[expose] public section

namespace Module

/-- For the canonical action of the annihilator quotient, the annihilator becomes zero. -/
theorem annihilator_quotientAnnihilator_eq_bot
    {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M] :
    letI := Module.quotientAnnihilator (R := R) (M := M)
    Module.annihilator (R ⧸ Module.annihilator R M) M = ⊥ := by
  let := Module.quotientAnnihilator (R := R) (M := M)
  rw [eq_bot_iff]
  intro q hq
  rw [Module.mem_annihilator] at hq
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective q
  rw [Submodule.mem_bot, Ideal.Quotient.eq_zero_iff_mem, Module.mem_annihilator]
  intro m
  exact hq m

/-- Every module is faithful over its annihilator quotient with the canonical quotient action.
The action remains local to this declaration, rather than a competing global instance. -/
theorem faithfulSMul_quotientAnnihilator
    {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M] :
    letI := Module.quotientAnnihilator (R := R) (M := M)
    FaithfulSMul (R ⧸ Module.annihilator R M) M :=
  letI := Module.quotientAnnihilator (R := R) (M := M)
  Module.annihilator_eq_bot.mp annihilator_quotientAnnihilator_eq_bot

-- Faithfulness over the quotient does not assert faithfulness over the original ring.
example : ¬ FaithfulSMul ℤ (ZMod 2) := by
  intro h
  have hz : Module.annihilator ℤ (ZMod 2) = ⊥ := Module.annihilator_eq_bot.mpr h
  have h2 : (2 : ℤ) ∈ Module.annihilator ℤ (ZMod 2) := by
    rw [Module.mem_annihilator]
    intro m
    simp only [zsmul_eq_mul]
    have htwo : (2 : ZMod 2) = 0 := by decide
    change (2 : ZMod 2) * m = 0
    rw [htwo, zero_mul]
  rw [hz] at h2
  norm_num at h2

example :
    letI := Module.quotientAnnihilator (R := ℤ) (M := ZMod 2)
    FaithfulSMul (ℤ ⧸ Module.annihilator ℤ (ZMod 2)) (ZMod 2) :=
  faithfulSMul_quotientAnnihilator

end Module
