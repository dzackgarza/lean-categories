/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction
public import Mathlib.LinearAlgebra.CliffordAlgebra.Grading
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NoncommRing

@[expose] public section

open CliffordAlgebra

namespace LeanCategories.Lattices.Valued

universe u v

section CommRing

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
variable (Q : QuadraticForm R M)

/-- Twisted conjugation by `g` fixes every vector.

This is membership in the kernel of the twisted conjugation map from the Lipschitz group to the
orthogonal group, written without reference to that map. -/
def IsTwistedCentral (g : (CliffordAlgebra Q)ˣ) : Prop :=
  ∀ x : M, involute (Q := Q) (g : CliffordAlgebra Q) * ι Q x *
    ((g⁻¹ : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) = ι Q x

/-- Twisted centrality without the inverse: `involute g` moves a vector past `g`. -/
theorem isTwistedCentral_iff {g : (CliffordAlgebra Q)ˣ} :
    IsTwistedCentral Q g ↔ ∀ x : M,
      involute (Q := Q) (g : CliffordAlgebra Q) * ι Q x = ι Q x * (g : CliffordAlgebra Q) :=
  forall_congr' fun _ => Units.mul_inv_eq_iff_eq_mul g

/-- The twisted commutator of a vector with an arbitrary element is a contraction.

Contraction by a dual vector is a twisted derivation, so moving `ι v` past `z` costs exactly
the contraction of `z` by the polar form of `v` [@grinberg_clifford_2016, Theorem 6]. -/
theorem ι_mul_sub_involute_mul_ι (v : M) (z : CliffordAlgebra Q) :
    ι Q v * z - involute z * ι Q v = contractLeft (Q.polarBilin v) z := by
  induction z using CliffordAlgebra.left_induction with
  | algebraMap r =>
    rw [contractLeft_algebraMap, AlgHom.commutes, Algebra.commutes, sub_self]
  | add x y hx hy =>
    rw [mul_add, map_add, add_mul, map_add, ← hx, ← hy]
    abel
  | ι_mul x m hx =>
    rw [contractLeft_ι_mul, ← hx, map_mul, involute_ι, QuadraticMap.polarBilin_apply_apply,
      Algebra.smul_def, ← mul_assoc, ι_mul_ι_comm]
    noncomm_ring

/-- A twisted-central element is annihilated by contraction along every polar functional. -/
theorem contractLeft_polarBilin_eq_zero {g : (CliffordAlgebra Q)ˣ}
    (hg : IsTwistedCentral Q g) (v : M) :
    contractLeft (Q.polarBilin v) (g : CliffordAlgebra Q) = 0 := by
  rw [← ι_mul_sub_involute_mul_ι Q v, (isTwistedCentral_iff Q).mp hg v, sub_self]

/-! ### The even and odd parts of a twisted-central element -/

/-- Right multiplication by a vector sends the even part into the odd part. -/
theorem mul_ι_mem_evenOdd_one {a : CliffordAlgebra Q} (ha : a ∈ evenOdd Q 0) (x : M) :
    a * ι Q x ∈ evenOdd Q 1 := by
  simpa using SetLike.mul_mem_graded ha (ι_mem_evenOdd_one Q x)

/-- Left multiplication by a vector sends the even part into the odd part. -/
theorem ι_mul_mem_evenOdd_one {a : CliffordAlgebra Q} (ha : a ∈ evenOdd Q 0) (x : M) :
    ι Q x * a ∈ evenOdd Q 1 := by
  simpa using SetLike.mul_mem_graded (ι_mem_evenOdd_one Q x) ha

/-- Right multiplication by a vector sends the odd part into the even part. -/
theorem mul_ι_mem_evenOdd_zero {a : CliffordAlgebra Q} (ha : a ∈ evenOdd Q 1) (x : M) :
    a * ι Q x ∈ evenOdd Q 0 := by
  simpa only [show (1 : ZMod 2) + 1 = 0 by decide] using
    SetLike.mul_mem_graded ha (ι_mem_evenOdd_one Q x)

/-- Left multiplication by a vector sends the odd part into the even part. -/
theorem ι_mul_mem_evenOdd_zero {a : CliffordAlgebra Q} (ha : a ∈ evenOdd Q 1) (x : M) :
    ι Q x * a ∈ evenOdd Q 0 := by
  simpa only [show (1 : ZMod 2) + 1 = 0 by decide] using
    SetLike.mul_mem_graded (ι_mem_evenOdd_one Q x) ha

/-- An element lying in both graded pieces is zero. -/
theorem eq_zero_of_mem_evenOdd_zero_of_mem_evenOdd_one {a : CliffordAlgebra Q}
    (h₀ : a ∈ evenOdd Q 0) (h₁ : a ∈ evenOdd Q 1) : a = 0 := by
  have : a ∈ evenOdd Q 0 ⊓ evenOdd Q 1 := ⟨h₀, h₁⟩
  rwa [(evenOdd_isCompl Q).inf_eq_bot, Submodule.mem_bot] at this

/-- Splitting twisted centrality along the even/odd grading.

The even part commutes with every vector and the odd part anticommutes with every vector. -/
theorem even_comm_and_odd_anticomm_of_twisted {g₀ g₁ : CliffordAlgebra Q}
    (h₀ : g₀ ∈ evenOdd Q 0) (h₁ : g₁ ∈ evenOdd Q 1)
    (h : ∀ x : M, involute (g₀ + g₁) * ι Q x = ι Q x * (g₀ + g₁)) (x : M) :
    g₀ * ι Q x = ι Q x * g₀ ∧ g₁ * ι Q x = -(ι Q x * g₁) := by
  have hinv : involute (g₀ + g₁) = g₀ - g₁ := by
    rw [map_add, involute_eq_of_mem_even h₀, involute_eq_of_mem_odd h₁, ← sub_eq_add_neg]
  have hkey : g₀ * ι Q x - ι Q x * g₀ = ι Q x * g₁ + g₁ * ι Q x := by
    have := h x
    rw [hinv, sub_mul, mul_add] at this
    linear_combination (norm := abel) this
  have hmemA : g₀ * ι Q x - ι Q x * g₀ ∈ evenOdd Q 1 :=
    sub_mem (mul_ι_mem_evenOdd_one Q h₀ x) (ι_mul_mem_evenOdd_one Q h₀ x)
  have hmemB : ι Q x * g₁ + g₁ * ι Q x ∈ evenOdd Q 0 :=
    add_mem (ι_mul_mem_evenOdd_zero Q h₁ x) (mul_ι_mem_evenOdd_zero Q h₁ x)
  have hA : g₀ * ι Q x - ι Q x * g₀ = 0 :=
    eq_zero_of_mem_evenOdd_zero_of_mem_evenOdd_one Q (hkey ▸ hmemB) hmemA
  have hB : ι Q x * g₁ + g₁ * ι Q x = 0 := hkey ▸ hA
  exact ⟨sub_eq_zero.mp hA, by linear_combination (norm := abel) hB⟩

/-! ### The remaining classical input -/

/-- Contractions detect scalars: an element killed by every contraction is a scalar.

This is the only ingredient of the kernel computation that Mathlib does not supply. The classical
proof expands the element in the monomial basis attached to an orthogonal basis of `M`; every
monomial of positive length is moved by some contraction, so only the constant term survives.
Mathlib has the linear isomorphism `CliffordAlgebra.equivExterior` and the exterior monomial basis
`Module.Basis.ExteriorAlgebra`, but no lemma relating that basis to `CliffordAlgebra.contractLeft`,
which is what the expansion needs. -/
def ContractionsDetectScalars : Prop :=
  ∀ z : CliffordAlgebra Q, (∀ d : Module.Dual R M, contractLeft d z = 0) →
    ∃ r : R, z = algebraMap R (CliffordAlgebra Q) r

/-- The scalar units act trivially under twisted conjugation. -/
theorem isTwistedCentral_algebraMap (r : Rˣ) :
    IsTwistedCentral Q (Units.map (algebraMap R (CliffordAlgebra Q)).toMonoidHom r) := by
  intro x
  have hinv : ((Units.map (algebraMap R (CliffordAlgebra Q)).toMonoidHom r)⁻¹ :
      (CliffordAlgebra Q)ˣ) = algebraMap R (CliffordAlgebra Q) ((r⁻¹ : Rˣ) : R) := by
    rw [← map_inv]
    rfl
  change involute (algebraMap R (CliffordAlgebra Q) ((r : Rˣ) : R)) * ι Q x * _ = _
  rw [hinv, AlgHom.commutes, Algebra.commutes, mul_assoc, ← map_mul]
  simp

/-- The twisted-central units are exactly the scalars, given the contraction criterion.

The polar hypothesis says that every functional on `M` is `polar Q v ·` for some `v`; over a field
this is nondegeneracy of `Q` together with finite dimensionality of `M`. -/
theorem exists_algebraMap_of_isTwistedCentral (hC : ContractionsDetectScalars Q)
    (hpolar : ∀ d : Module.Dual R M, ∃ v : M, Q.polarBilin v = d)
    {g : (CliffordAlgebra Q)ˣ} (hg : IsTwistedCentral Q g) :
    ∃ r : R, (g : CliffordAlgebra Q) = algebraMap R (CliffordAlgebra Q) r := by
  refine hC _ fun d => ?_
  obtain ⟨v, rfl⟩ := hpolar d
  exact contractLeft_polarBilin_eq_zero Q hg v

end CommRing

section Field

variable {K : Type u} [Field K] {V : Type v} [AddCommGroup V] [Module K V]
variable (Q : QuadraticForm K V) [Invertible (2 : K)]

/-- The kernel of twisted conjugation is the group of scalar units.

Over a field the scalar produced by `exists_algebraMap_of_isTwistedCentral` is invertible, so the
statement upgrades to an equality of subgroups of `(CliffordAlgebra Q)ˣ`. -/
theorem isTwistedCentral_iff_mem_scalarRange (hC : ContractionsDetectScalars Q)
    (hpolar : ∀ d : Module.Dual K V, ∃ v : V, Q.polarBilin v = d)
    {g : (CliffordAlgebra Q)ˣ} :
    IsTwistedCentral Q g ↔
      g ∈ (Units.map (algebraMap K (CliffordAlgebra Q)).toMonoidHom).range := by
  refine ⟨fun hg => ?_, ?_⟩
  · obtain ⟨r, hr⟩ := exists_algebraMap_of_isTwistedCentral Q hC hpolar hg
    have hr0 : r ≠ 0 := by
      rintro rfl
      rw [map_zero] at hr
      exact one_ne_zero (α := CliffordAlgebra Q) (by rw [← g.mul_inv, hr, zero_mul])
    exact ⟨Units.mk0 r hr0, Units.ext hr.symm⟩
  · rintro ⟨r, rfl⟩
    exact isTwistedCentral_algebraMap Q r

/-- The kernel of twisted conjugation, as an equality of subgroups. -/
theorem twistedCentral_setOf_eq_scalarRange (hC : ContractionsDetectScalars Q)
    (hpolar : ∀ d : Module.Dual K V, ∃ v : V, Q.polarBilin v = d) :
    {g : (CliffordAlgebra Q)ˣ | IsTwistedCentral Q g} =
      (Units.map (algebraMap K (CliffordAlgebra Q)).toMonoidHom).range :=
  Set.ext fun _ => isTwistedCentral_iff_mem_scalarRange Q hC hpolar

end Field

end LeanCategories.Lattices.Valued
