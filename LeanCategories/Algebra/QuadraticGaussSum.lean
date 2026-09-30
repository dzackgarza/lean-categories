/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Topology.Instances.AddCircle.Defs

@[expose] public section

/-!
# Gauss sums of quadratic functions on finite abelian groups

Let `A` be a finite abelian group, `T` an abelian group, and `ψ : T → S¹` an additive
character. A function `q : A → T` is *quadratic with polar form `β`* when
`q (x + y) = q x + q y + β x y` and `β` is additive in its first argument. Its Gauss sum is
`G_ψ(q) = ∑ a, ψ (q a)`.

**Theorem** (`quadraticGaussSum_mul_conj`). If for every `c ≠ 0` the character
`a ↦ ψ (β a c)` of `A` is nontrivial (nondegeneracy of `β` relative to `ψ`), then
`G_ψ(q) · conj G_ψ(q) = |A|`.

This is the modulus half of Milgram's formula. The discriminant form of an even lattice takes
values in `ℚ/2ℤ`; `discriminantCharacter` is the character `ℚ/2ℤ → ℝ/2ℤ → S¹`, and
`MilgramStatement` is the argument half, `G(q) = √|A| · exp(2πiσ/8)`, as a proposition. The
argument half relates `q` to the signature of a lattice and is not proved here.

Provenance: migrated from `dzackgarza/research`,
`computations/scripts/sterk-enriques-cusps/lean/Atoms.lean` (sections `Doubling`,
`DiscriminantGaussSum`, `MilgramSteps`; Sterk graph nodes F1.15, F1.16). There the sum was
stated only for `T = ℚ/2ℤ` with the fixed character, and the theorem carried the hypotheses
`q 0 = 0`, `β 0 c = 0` and `β a 0 = 0`; these follow from the polar identity and additivity and
are dropped here.

LC-09 search: the formalization corpus returns no Gauss sum of a quadratic function on a finite
abelian group and no Milgram formula; Mathlib's `gaussSum` is the sum `∑ χ(a) ψ(a)` over a
finite *ring* for a multiplicative/additive character pair, a different object. The character
sum evaluation is Mathlib's `AddChar.sum_eq_ite`.

TODO(LC-12): the discriminant forms of `Lattices/Valued/Discriminant.lean` take values in the
fraction-value quotient, not in `ℚ/2ℤ`. Stating Milgram for `discriminantSymBilWQuadraticMap L`
needs the character of that value group; the general theorem here applies once it is chosen
(COMPLAINTS: Milgram's formula).
-/

namespace LeanCategories

open scoped ComplexConjugate

section GaussSum

variable {A T : Type*} [AddCommGroup A] [Fintype A] [AddCommGroup T]
variable (ψ : AddChar T Circle)

/-- The Gauss sum `∑ a, ψ (q a)` of a function `q : A → T`. -/
noncomputable def quadraticGaussSum (q : A → T) : ℂ :=
  ∑ a : A, (ψ (q a) : ℂ)

/-- The character `a ↦ ψ (β a c)` of `A` for a form `β` additive in its first argument. -/
noncomputable def polarCharacter (β : A → A → T)
    (hadd : ∀ x y c, β (x + y) c = β x c + β y c) (c : A) : AddChar A ℂ where
  toFun a := (ψ (β a c) : ℂ)
  map_zero_eq_one' := by
    have h0 : β 0 c = 0 := by
      have := hadd 0 0 c
      simpa using this
    simp [h0]
  map_add_eq_mul' a b := by
    simp [hadd a b c, AddChar.map_add_eq_mul]

omit [Fintype A] in
@[simp]
theorem polarCharacter_apply (β : A → A → T) (hadd) (c a : A) :
    polarCharacter ψ β hadd c a = (ψ (β a c) : ℂ) := rfl

theorem conj_addChar_circle (t : T) : conj (ψ t : ℂ) = (ψ (-t) : ℂ) := by
  rw [AddChar.map_neg_eq_inv, Circle.coe_inv_eq_conj]

/-- **Modulus of a quadratic Gauss sum.** For a quadratic function whose polar form is
nondegenerate relative to `ψ`, `|G_ψ(q)|² = |A|`. -/
theorem quadraticGaussSum_mul_conj (q : A → T) (β : A → A → T)
    (hpol : ∀ x y, q (x + y) = q x + q y + β x y)
    (hadd : ∀ x y c, β (x + y) c = β x c + β y c)
    (hnd : ∀ c : A, c ≠ 0 → polarCharacter ψ β hadd c ≠ 0) :
    quadraticGaussSum ψ q * conj (quadraticGaussSum ψ q) = (Fintype.card A : ℂ) := by
  classical
  have hq0 : q 0 = -β 0 0 := by
    have h := hpol 0 0
    simp only [add_zero] at h
    exact eq_neg_of_add_eq_zero_left (by simpa [add_assoc] using h)
  have hb00 : β 0 0 = 0 := by simpa using hadd 0 0 0
  have hβ0 : ∀ a, β a 0 = 0 := by
    intro a
    have h := hpol a 0
    simp only [add_zero, hq0, hb00, neg_zero] at h
    simpa using h.symm
  -- `∑ a ∑ b ψ(q a) conj ψ(q b) = ∑ b ∑ c ψ(q (b + c) - q b) = ∑ c ψ(q c) ∑ b ψ(β b c)`.
  have hinner : ∀ b : A, ∑ a : A, (ψ (q a) : ℂ) * conj (ψ (q b) : ℂ) =
      ∑ c : A, (ψ (q c) : ℂ) * polarCharacter ψ β hadd c b := by
    intro b
    rw [← Fintype.sum_equiv (Equiv.addLeft b)
      (fun c ↦ (ψ (q (b + c)) : ℂ) * conj (ψ (q b) : ℂ)) _ (fun _ ↦ rfl)]
    refine Finset.sum_congr rfl fun c _ ↦ ?_
    simp only [polarCharacter_apply]
    rw [conj_addChar_circle, ← Circle.coe_mul, ← Circle.coe_mul, ← AddChar.map_add_eq_mul,
      ← AddChar.map_add_eq_mul, hpol b c]
    congr 2
    abel
  calc quadraticGaussSum ψ q * conj (quadraticGaussSum ψ q)
      = ∑ b : A, ∑ a : A, (ψ (q a) : ℂ) * conj (ψ (q b) : ℂ) := by
        simp only [quadraticGaussSum, map_sum, Finset.sum_mul_sum]
        exact Finset.sum_comm
    _ = ∑ c : A, (ψ (q c) : ℂ) * ∑ b : A, polarCharacter ψ β hadd c b := by
        simp_rw [hinner, Finset.mul_sum]
        exact Finset.sum_comm
    _ = ∑ c : A, (ψ (q c) : ℂ) *
          (if polarCharacter ψ β hadd c = 0 then (Fintype.card A : ℂ) else 0) := by
        simp_rw [AddChar.sum_eq_ite]
    _ = (Fintype.card A : ℂ) := by
        rw [Finset.sum_eq_single (0 : A)]
        · have htriv : polarCharacter ψ β hadd 0 = 0 := by
            ext a
            simp [hβ0]
          simp [htriv, hq0, hb00]
        · intro c _ hc
          simp [hnd c hc]
        · simp

end GaussSum

section DiscriminantValues

/-- The doubling map `ℚ/ℤ → ℚ/2ℤ`, multiplication by two. It relates the `ℚ/ℤ`-valued bilinear
form of a discriminant form to its `ℚ/2ℤ`-valued quadratic form (Nikulin §1). -/
noncomputable def doubling : AddCircle (1 : ℚ) →+ AddCircle (2 : ℚ) :=
  QuotientAddGroup.map _ _ (AddMonoidHom.mulLeft (2 : ℚ)) <| by
    rw [AddSubgroup.zmultiples_le]
    refine AddSubgroup.mem_comap.mpr ?_
    change (2 : ℚ) * 1 ∈ AddSubgroup.zmultiples (2 : ℚ)
    simp

/-- The comparison `ℚ/2ℤ → ℝ/2ℤ` induced by `ℚ ⊆ ℝ`. -/
noncomputable def ratCircleToRealCircle : AddCircle (2 : ℚ) →+ AddCircle ((2 : ℚ) : ℝ) :=
  QuotientAddGroup.map _ _ (Rat.castHom ℝ).toAddMonoidHom <| by
    rw [AddSubgroup.zmultiples_le]
    refine AddSubgroup.mem_comap.mpr ?_
    change ((2 : ℚ) : ℝ) ∈ AddSubgroup.zmultiples ((2 : ℚ) : ℝ)
    exact AddSubgroup.mem_zmultiples _

/-- The character `ℚ/2ℤ → S¹`, `x ↦ exp(πi x)`. -/
noncomputable def discriminantCharacter : AddChar (AddCircle (2 : ℚ)) Circle :=
  AddCircle.toCircle_addChar.compAddMonoidHom ratCircleToRealCircle

variable {A : Type*} [AddCommGroup A] [Fintype A]

/-- The Gauss sum of a `ℚ/2ℤ`-valued form on a finite abelian group. -/
noncomputable abbrev discriminantGaussSum (q : A → AddCircle (2 : ℚ)) : ℂ :=
  quadraticGaussSum discriminantCharacter q

omit [AddCommGroup A] in
/-- The Gauss sum of the zero form is the order of the group. -/
theorem discriminantGaussSum_zero :
    discriminantGaussSum (fun _ : A ↦ (0 : AddCircle (2 : ℚ))) = Fintype.card A := by
  simp [quadraticGaussSum]

/-- **Milgram's formula**, as a proposition: for an even lattice with discriminant form `q` and
signature `σ`, `G(q) = √|A| · exp(2πiσ/8)`. Its modulus is `quadraticGaussSum_mul_conj`; its
argument is not proved here (COMPLAINTS: Milgram's formula). -/
def MilgramStatement (q : A → AddCircle (2 : ℚ)) (σ : ℤ) : Prop :=
  discriminantGaussSum q =
    (Real.sqrt (Fintype.card A) : ℂ) * Complex.exp (2 * Real.pi * Complex.I * (σ : ℂ) / 8)

end DiscriminantValues

end LeanCategories
