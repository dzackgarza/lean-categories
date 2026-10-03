/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.Algebra.Polynomial.Taylor
public import Mathlib.Algebra.Polynomial.SpecificDegree
public import Mathlib.Tactic.FinCases
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Tactic.ComputeDegree

@[expose] public section

/-!
# Translation between polynomial quotient presentations

The substitution `X ↦ X + c` is the polynomial algebra automorphism
`Polynomial.taylorEquiv c`, with inverse `X ↦ X - c`. It carries the principal
ideal `(f)` to `(f(X + c))`, hence induces an algebra isomorphism of the quotient
presentations. This is the ordinary quotient universal property, not equality
of presentations (Atiyah–Macdonald, *Introduction to Commutative Algebra*, §1,
quotient rings; Mathlib `Ideal.quotientEquivAlg`).
-/

namespace LeanCategories.Algebra.PolynomialPresentation
open Polynomial

local instance : Fact (Nat.Prime 3) := ⟨by decide⟩

/-- Translate a polynomial quotient presentation by the selected coefficient `c`. -/
noncomputable def translate {R : Type u} [CommRing R] (f : R[X]) (c : R) :
    AdjoinRoot f ≃ₐ[R] AdjoinRoot (Polynomial.taylor c f) :=
  Ideal.quotientEquivAlg _ _ (Polynomial.taylorEquiv c) (by
    rw [Ideal.map_span]
    simp only [Set.image_singleton]
    rfl)

/-- Translation sends the distinguished root to the translated root. -/
@[simp] theorem translate_root {R : Type u} [CommRing R] (f : R[X]) (c : R) :
    translate f c (AdjoinRoot.root f) =
      AdjoinRoot.root (Polynomial.taylor c f) + algebraMap R _ c := by
  change Ideal.quotientEquivAlg _ _ _ _ (Ideal.Quotient.mk _ X) = _
  rw [Ideal.quotientEquivAlg_mk]
  change AdjoinRoot.mk _ (Polynomial.taylor c X) = _
  rw [Polynomial.taylor_X, map_add, AdjoinRoot.mk_X, AdjoinRoot.mk_C]
  rfl

/-- The first quadratic presentation over `𝔽₃`. -/
noncomputable def firstPolynomial : (ZMod 3)[X] := X ^ 2 + 1

/-- Its translated presentation: `y² + y + 2`. -/
noncomputable def secondPolynomial : (ZMod 3)[X] := X ^ 2 + X + 2

/-- The displayed substitution changes precisely the prescribed defining relation. -/
theorem translated_first : Polynomial.taylor (2 : ZMod 3) firstPolynomial =
    secondPolynomial := by
  simp only [firstPolynomial, secondPolynomial, Polynomial.taylor_apply,
    Polynomial.add_comp, Polynomial.pow_comp, Polynomial.X_comp, Polynomial.one_comp]
  norm_num [Polynomial.C_ofNat]
  ring_nf
  reduce_mod_char

/-- Equality of the defining relation gives the identity-coefficient comparison
between the translated and displayed target quotient. -/
noncomputable def translatedComparison :
    AdjoinRoot (Polynomial.taylor (2 : ZMod 3) firstPolynomial) ≃ₐ[ZMod 3]
      AdjoinRoot secondPolynomial :=
  AdjoinRoot.mapAlgEquiv (AlgEquiv.refl : ZMod 3 ≃ₐ[ZMod 3] ZMod 3) _ _ (by
    change Associated ((Polynomial.taylor (2 : ZMod 3) firstPolynomial).map
      (RingHom.id (ZMod 3))) secondPolynomial
    rw [Polynomial.map_id, translated_first])

/-- The prescribed nonidentity comparison of the two quadratic quotient presentations. -/
noncomputable def comparison : AdjoinRoot firstPolynomial ≃ₐ[ZMod 3]
    AdjoinRoot secondPolynomial :=
  (translate firstPolynomial 2).trans translatedComparison

/-- The comparison retains the prescribed generator image `x ↦ y + 2`. -/
@[simp] theorem comparison_root : comparison (AdjoinRoot.root firstPolynomial) =
    AdjoinRoot.root secondPolynomial + 2 := by
  change translatedComparison ((translate firstPolynomial 2) (AdjoinRoot.root firstPolynomial)) = _
  rw [translate_root, map_add]
  simp [translatedComparison, AdjoinRoot.coe_mapAlgEquiv, AdjoinRoot.coe_mapAlgHom,
    AdjoinRoot.map_root, AdjoinRoot.map_of, AdjoinRoot.algebraMap_eq']
  exact map_ofNat (AdjoinRoot.of secondPolynomial) 2

/-- The chosen inverse sends the target generator to `x - 2`. -/
@[simp] theorem comparison_symm_root : comparison.symm (AdjoinRoot.root secondPolynomial) =
    AdjoinRoot.root firstPolynomial - 2 := by
  apply comparison.injective
  simp only [comparison.apply_symm_apply, map_sub, comparison_root, map_ofNat, add_sub_cancel_right]

/-- The target defining relation has degree two, so constants embed in its quotient. -/
theorem degree_second : secondPolynomial.degree = 2 := by
  unfold secondPolynomial
  compute_degree <;> norm_num

/-- The comparison changes the distinguished generator; it is not a carrier identity. -/
theorem comparison_root_ne : comparison (AdjoinRoot.root firstPolynomial) ≠
    AdjoinRoot.root secondPolynomial := by
  rw [comparison_root]
  intro h
  have h2 : AdjoinRoot.of secondPolynomial (2 : ZMod 3) =
      AdjoinRoot.of secondPolynomial 0 := by
    simpa only [map_ofNat, map_zero] using (add_eq_left.mp h)
  have injective := AdjoinRoot.of.injective_of_degree_ne_zero
    (f := secondPolynomial) (by rw [degree_second]; norm_num)
  have : (2 : ZMod 3) = 0 := injective h2
  exact (by decide : (2 : ZMod 3) ≠ 0) this

/-- Neither quadratic has a root in the selected coefficient field. -/
theorem first_irreducible : Irreducible firstPolynomial := by
  apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
  · have h : firstPolynomial.natDegree = 2 := by
      unfold firstPolynomial
      compute_degree <;> norm_num
    simp [h]
  · intro x
    simp only [Polynomial.IsRoot, firstPolynomial, Polynomial.eval_add,
      Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_one]
    fin_cases x <;> decide

/-- The displayed target is also a field presentation, not merely a quotient ring. -/
theorem second_irreducible : Irreducible secondPolynomial := by
  apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
  · have h : secondPolynomial.natDegree = 2 := by
      unfold secondPolynomial
      compute_degree <;> norm_num
    simp [h]
  · intro x
    simp only [Polynomial.IsRoot, secondPolynomial, Polynomial.eval_add,
      Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_ofNat]
    fin_cases x <;> decide

end LeanCategories.Algebra.PolynomialPresentation
