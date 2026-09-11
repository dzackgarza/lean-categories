/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.DirectSum.Ring
public import Mathlib.Algebra.Module.GradedModule
public import Mathlib.LinearAlgebra.Quotient.Bilinear
public import Mathlib.RingTheory.Filtration

/-!
# Associated graded rings and modules of ideal filtrations

Atiyah--Macdonald, *Introduction to Commutative Algebra* (1969), printed
pp. 111--112, FC04-C10-U053--U054. For an ideal `I` and an `I`-filtration `F`,
this file constructs

`gr_I(R) = ⨁ n, I^n / I^(n+1)`

and

`gr_F(M) = ⨁ n, F.N n / F.N (n+1)`.

Multiplication and scalar multiplication are induced on representatives and
proved independent of representatives before the direct sums receive their
commutative-ring and module structures.

The construction is a reference port/adaptation of Mathlib PR #33218 at
`3c12745297b7236616f6a23d7c11a8addd85e839` (associated graded ring) and PR
#33220 at `70572cd62395e933e8f6476bcedcee366a5b5e82` (associated graded module),
both Apache-2.0. Those snapshots target an earlier filtration/direct-sum API and
do not compile against this repository's pinned Mathlib; the quotient and graded
construction is retained here while using the pinned `LinearMap.liftQ₂`,
`DirectSum.GCommRing`, and `DirectSum.Gmodule` interfaces.

This is the associated graded object itself, not a Rees-algebra proxy.
-/

@[expose] public section

open DirectSum

namespace Ideal

variable {R : Type*} [CommRing R]

/-- The copy of `I^(n+1)` inside `I^n`. -/
abbrev associatedGradedRingLower (I : Ideal R) (n : ℕ) :
    Submodule R ↥((I ^ n : Ideal R) : Submodule R R) :=
  Submodule.comap (((I ^ n : Ideal R) : Submodule R R).subtype)
    ((I ^ (n + 1) : Ideal R) : Submodule R R)

/-- Degree `n` of the associated graded ring of `I`. -/
abbrev AssociatedGradedRingPiece (I : Ideal R) (n : ℕ) :=
  ↥((I ^ n : Ideal R) : Submodule R R) ⧸ associatedGradedRingLower I n

/-- The additive direct sum `⊕ n, I^n / I^(n+1)`. -/
abbrev AssociatedGradedRing (I : Ideal R) := ⨁ n : ℕ, AssociatedGradedRingPiece I n

/-- The quotient map from the `n`th ideal power to the `n`th graded piece. -/
abbrev associatedGradedRingMk (I : Ideal R) (n : ℕ) :
    ↥((I ^ n : Ideal R) : Submodule R R) →ₗ[R] AssociatedGradedRingPiece I n :=
  (associatedGradedRingLower I n).mkQ

noncomputable def associatedGradedRingMulToPiece (I : Ideal R) (i j : ℕ) :
    ↥((I ^ i : Ideal R) : Submodule R R) →ₗ[R]
      ↥((I ^ j : Ideal R) : Submodule R R) →ₗ[R]
        AssociatedGradedRingPiece I (i + j) :=
  LinearMap.mk₂ R
    (fun x y => associatedGradedRingMk I (i + j)
      ⟨x.1 * y.1, by simpa [pow_add] using Ideal.mul_mem_mul x.2 y.2⟩)
    (fun x y z => by rw [← map_add]; congr 1; ext; exact add_mul _ _ _)
    (fun c x y => by rw [← map_smul]; congr 1; ext; simp [smul_eq_mul, mul_assoc])
    (fun x y z => by rw [← map_add]; congr 1; ext; exact mul_add _ _ _)
    (fun c x y => by rw [← map_smul]; congr 1; ext; simp [smul_eq_mul, mul_left_comm])

theorem associatedGradedRingMul_ker_left (I : Ideal R) (i j : ℕ) :
    associatedGradedRingLower I i ≤ (associatedGradedRingMulToPiece I i j).ker := by
  intro x hx
  rw [LinearMap.mem_ker]
  apply LinearMap.ext
  intro y
  change (Submodule.Quotient.mk _ : AssociatedGradedRingPiece I (i + j)) = 0
  rw [Submodule.Quotient.mk_eq_zero]
  change x.1 * y.1 ∈ I ^ (i + j + 1)
  change x.1 ∈ I ^ (i + 1) at hx
  have h := Ideal.mul_mem_mul hx y.2
  simpa [pow_succ, pow_add, mul_assoc, mul_comm, mul_left_comm,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

theorem associatedGradedRingMul_ker_right (I : Ideal R) (i j : ℕ) :
    associatedGradedRingLower I j ≤ (associatedGradedRingMulToPiece I i j).flip.ker := by
  intro y hy
  rw [LinearMap.mem_ker]
  apply LinearMap.ext
  intro x
  change (Submodule.Quotient.mk _ : AssociatedGradedRingPiece I (i + j)) = 0
  rw [Submodule.Quotient.mk_eq_zero]
  change x.1 * y.1 ∈ I ^ (i + j + 1)
  change y.1 ∈ I ^ (j + 1) at hy
  have h := Ideal.mul_mem_mul x.2 hy
  simpa [pow_succ, pow_add, mul_assoc, mul_comm, mul_left_comm,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

/-- Multiplication on homogeneous associated-graded pieces. -/
noncomputable def associatedGradedRingMul (I : Ideal R) (i j : ℕ) :
    AssociatedGradedRingPiece I i →ₗ[R]
      AssociatedGradedRingPiece I j →ₗ[R] AssociatedGradedRingPiece I (i + j) :=
  (associatedGradedRingMulToPiece I i j).liftQ₂
    (associatedGradedRingLower I i) (associatedGradedRingLower I j)
    (associatedGradedRingMul_ker_left I i j) (associatedGradedRingMul_ker_right I i j)

@[simp]
theorem associatedGradedRingMul_mk (I : Ideal R) (i j : ℕ)
    (x : ↥((I ^ i : Ideal R) : Submodule R R))
    (y : ↥((I ^ j : Ideal R) : Submodule R R)) :
    associatedGradedRingMul I i j (Submodule.Quotient.mk x)
        (Submodule.Quotient.mk y) =
      associatedGradedRingMk I (i + j)
        ⟨x.1 * y.1, by simpa [pow_add] using Ideal.mul_mem_mul x.2 y.2⟩ := rfl

/-- The representative formula in the source notation. This companion to the
`simp` lemma keeps the quotient-map abbreviations visible for structural proofs. -/
theorem associatedGradedRingMul_mk' (I : Ideal R) (i j : ℕ)
    (x : ↥((I ^ i : Ideal R) : Submodule R R))
    (y : ↥((I ^ j : Ideal R) : Submodule R R)) :
    associatedGradedRingMul I i j (associatedGradedRingMk I i x)
        (associatedGradedRingMk I j y) =
      associatedGradedRingMk I (i + j)
        ⟨x.1 * y.1, by simpa [pow_add] using Ideal.mul_mem_mul x.2 y.2⟩ := rfl

noncomputable instance (I : Ideal R) : GradedMonoid.GMul (AssociatedGradedRingPiece I) where
  mul := fun x y => associatedGradedRingMul I _ _ x y

noncomputable instance (I : Ideal R) : GradedMonoid.GOne (AssociatedGradedRingPiece I) where
  one := associatedGradedRingMk I 0 ⟨1, by simp⟩


theorem associatedGradedRingMk_heq_of_eq (I : Ideal R) {i j : ℕ} (hij : i = j)
    {r s : R} (hrs : r = s) (hi : r ∈ I ^ i) (hj : s ∈ I ^ j) :
    HEq (associatedGradedRingMk I i ⟨r, hi⟩) (associatedGradedRingMk I j ⟨s, hj⟩) := by
  subst j
  subst s
  rfl

theorem associatedGradedRing_one_mul (I : Ideal R)
    (x : GradedMonoid (AssociatedGradedRingPiece I)) : 1 * x = x := by
  rcases x with ⟨i, x⟩
  induction x using Submodule.Quotient.induction_on with
  | _ x =>
    change (⟨0 + i, associatedGradedRingMul I 0 i
      (associatedGradedRingMk I 0 ⟨1, by simp⟩)
      (associatedGradedRingMk I i x)⟩ : Sigma (AssociatedGradedRingPiece I)) =
      ⟨i, associatedGradedRingMk I i x⟩
    rw [associatedGradedRingMul_mk']
    exact Sigma.ext (zero_add i)
      (associatedGradedRingMk_heq_of_eq I (zero_add i) (one_mul x.1) _ _)

theorem associatedGradedRing_mul_one (I : Ideal R)
    (x : GradedMonoid (AssociatedGradedRingPiece I)) : x * 1 = x := by
  rcases x with ⟨i, x⟩
  induction x using Submodule.Quotient.induction_on with
  | _ x =>
    change (⟨i + 0, associatedGradedRingMul I i 0
      (associatedGradedRingMk I i x)
      (associatedGradedRingMk I 0 ⟨1, by simp⟩)⟩ : Sigma (AssociatedGradedRingPiece I)) =
      ⟨i, associatedGradedRingMk I i x⟩
    rw [associatedGradedRingMul_mk']
    exact Sigma.ext (Nat.add_zero i)
      (associatedGradedRingMk_heq_of_eq I (Nat.add_zero i) (mul_one x.1) _ _)

theorem associatedGradedRing_mul_assoc (I : Ideal R)
    (x y z : GradedMonoid (AssociatedGradedRingPiece I)) : x * y * z = x * (y * z) := by
  rcases x with ⟨i, x⟩
  rcases y with ⟨j, y⟩
  rcases z with ⟨k, z⟩
  induction x using Submodule.Quotient.induction_on with
  | _ x =>
    induction y using Submodule.Quotient.induction_on with
    | _ y =>
      induction z using Submodule.Quotient.induction_on with
      | _ z =>
        change (⟨(i + j) + k,
          associatedGradedRingMul I (i + j) k
            (associatedGradedRingMul I i j
              (associatedGradedRingMk I i x) (associatedGradedRingMk I j y))
            (associatedGradedRingMk I k z)⟩ : Sigma (AssociatedGradedRingPiece I)) =
          ⟨i + (j + k),
            associatedGradedRingMul I i (j + k) (associatedGradedRingMk I i x)
              (associatedGradedRingMul I j k
                (associatedGradedRingMk I j y) (associatedGradedRingMk I k z))⟩
        rw [associatedGradedRingMul_mk', associatedGradedRingMul_mk',
          associatedGradedRingMul_mk', associatedGradedRingMul_mk']
        exact Sigma.ext (Nat.add_assoc i j k)
          (associatedGradedRingMk_heq_of_eq I (Nat.add_assoc i j k) (mul_assoc x.1 y.1 z.1) _ _)


noncomputable instance (I : Ideal R) : GradedMonoid.GMonoid (AssociatedGradedRingPiece I) where
  one_mul := associatedGradedRing_one_mul I
  mul_one := associatedGradedRing_mul_one I
  mul_assoc := associatedGradedRing_mul_assoc I

noncomputable def associatedGradedRingNatCast (I : Ideal R) (n : ℕ) :
    AssociatedGradedRingPiece I 0 :=
  associatedGradedRingMk I 0 ⟨n, by simp⟩

theorem associatedGradedRing_mul_zero (I : Ideal R) {i j} (x : AssociatedGradedRingPiece I i) :
    GradedMonoid.GMul.mul x (0 : AssociatedGradedRingPiece I j) = 0 := by
  change associatedGradedRingMul I i j x 0 = 0
  exact (associatedGradedRingMul I i j x).map_zero

theorem associatedGradedRing_zero_mul (I : Ideal R) {i j} (y : AssociatedGradedRingPiece I j) :
    GradedMonoid.GMul.mul (0 : AssociatedGradedRingPiece I i) y = 0 := by
  change associatedGradedRingMul I i j 0 y = 0
  rw [map_zero]
  rfl

theorem associatedGradedRing_mul_add (I : Ideal R) {i j}
    (x : AssociatedGradedRingPiece I i) (y z : AssociatedGradedRingPiece I j) :
    GradedMonoid.GMul.mul x (y + z) = GradedMonoid.GMul.mul x y + GradedMonoid.GMul.mul x z := by
  change associatedGradedRingMul I i j x (y + z) = _
  exact (associatedGradedRingMul I i j x).map_add y z

theorem associatedGradedRing_add_mul (I : Ideal R) {i j}
    (x y : AssociatedGradedRingPiece I i) (z : AssociatedGradedRingPiece I j) :
    GradedMonoid.GMul.mul (x + y) z = GradedMonoid.GMul.mul x z + GradedMonoid.GMul.mul y z := by
  change associatedGradedRingMul I i j (x + y) z = _
  rw [map_add]
  rfl

theorem associatedGradedRing_natCast_zero (I : Ideal R) : associatedGradedRingNatCast I 0 = 0 := by
  simp [associatedGradedRingNatCast]

theorem associatedGradedRing_natCast_succ (I : Ideal R) (n : ℕ) :
    associatedGradedRingNatCast I (n + 1) =
      associatedGradedRingNatCast I n + GradedMonoid.GOne.one := by
  change associatedGradedRingMk I 0 ⟨(n + 1 : ℕ), by simp⟩ =
    associatedGradedRingMk I 0 ⟨n, by simp⟩ + associatedGradedRingMk I 0 ⟨1, by simp⟩
  rw [← map_add]
  congr 1
  ext
  simp

noncomputable instance (I : Ideal R) : DirectSum.GSemiring (AssociatedGradedRingPiece I) where
  mul_zero := associatedGradedRing_mul_zero I
  zero_mul := associatedGradedRing_zero_mul I
  mul_add := associatedGradedRing_mul_add I
  add_mul := associatedGradedRing_add_mul I
  natCast := associatedGradedRingNatCast I
  natCast_zero := associatedGradedRing_natCast_zero I
  natCast_succ := associatedGradedRing_natCast_succ I

noncomputable def associatedGradedRingIntCast (I : Ideal R) (z : ℤ) :
    AssociatedGradedRingPiece I 0 :=
  associatedGradedRingMk I 0 ⟨z, by simp⟩

theorem associatedGradedRing_intCast_ofNat (I : Ideal R) (n : ℕ) :
    associatedGradedRingIntCast I n = associatedGradedRingNatCast I n := by
  unfold associatedGradedRingIntCast associatedGradedRingNatCast
  congr 1
  apply Subtype.ext
  norm_num

theorem associatedGradedRing_intCast_negSucc (I : Ideal R) (n : ℕ) :
    associatedGradedRingIntCast I (Int.negSucc n) = - associatedGradedRingNatCast I (n + 1) := by
  change associatedGradedRingMk I 0 ⟨Int.negSucc n, by simp⟩ =
    - associatedGradedRingMk I 0 ⟨(n + 1 : ℕ), by simp⟩
  rw [← map_neg]
  congr 1
  ext
  simp

noncomputable instance (I : Ideal R) : DirectSum.GRing (AssociatedGradedRingPiece I) where
  intCast := associatedGradedRingIntCast I
  intCast_ofNat := associatedGradedRing_intCast_ofNat I
  intCast_negSucc_ofNat := associatedGradedRing_intCast_negSucc I

theorem associatedGradedRing_mul_comm (I : Ideal R)
    (x y : GradedMonoid (AssociatedGradedRingPiece I)) : x * y = y * x := by
  rcases x with ⟨i, x⟩
  rcases y with ⟨j, y⟩
  induction x using Submodule.Quotient.induction_on with
  | _ x =>
    induction y using Submodule.Quotient.induction_on with
    | _ y =>
      change (⟨i + j, associatedGradedRingMul I i j
        (associatedGradedRingMk I i x) (associatedGradedRingMk I j y)⟩ :
          Sigma (AssociatedGradedRingPiece I)) =
        ⟨j + i, associatedGradedRingMul I j i
          (associatedGradedRingMk I j y) (associatedGradedRingMk I i x)⟩
      rw [associatedGradedRingMul_mk', associatedGradedRingMul_mk']
      exact Sigma.ext (Nat.add_comm i j)
        (associatedGradedRingMk_heq_of_eq I (Nat.add_comm i j) (mul_comm x.1 y.1) _ _)

noncomputable instance (I : Ideal R) : DirectSum.GCommSemiring (AssociatedGradedRingPiece I) where
  mul_comm := associatedGradedRing_mul_comm I

noncomputable instance (I : Ideal R) : DirectSum.GCommRing (AssociatedGradedRingPiece I) where

noncomputable instance (I : Ideal R) : CommRing (AssociatedGradedRing I) :=
  DirectSum.commRing (AssociatedGradedRingPiece I)

/-- Intended representative behavior: homogeneous multiplication is induced by
multiplication in the original ring. -/
example (I : Ideal R) (i j : ℕ)
    (x : ↥((I ^ i : Ideal R) : Submodule R R))
    (y : ↥((I ^ j : Ideal R) : Submodule R R)) :
    associatedGradedRingMul I i j (associatedGradedRingMk I i x)
        (associatedGradedRingMk I j y) =
      associatedGradedRingMk I (i + j)
        ⟨x.1 * y.1, by simpa [pow_add] using Ideal.mul_mem_mul x.2 y.2⟩ :=
  associatedGradedRingMul_mk' I i j x y

/-- Separating boundary case: an element already in `I^(n+1)` vanishes in
the degree-`n` quotient, so the construction is not merely the direct sum of
the powers `I^n`. -/
example (I : Ideal R) (n : ℕ) (x : associatedGradedRingLower I n) :
    associatedGradedRingMk I n x.1 = 0 := by
  change (Submodule.Quotient.mk x.1 : AssociatedGradedRingPiece I n) = 0
  rw [Submodule.Quotient.mk_eq_zero]
  exact x.2



namespace Filtration

variable {M : Type*} [AddCommGroup M] [Module R M]
variable {I : Ideal R} (F : I.Filtration M)

abbrev associatedGradedModuleLower (n : ℕ) : Submodule R (F.N n) :=
  Submodule.comap (F.N n).subtype (F.N (n + 1))

abbrev AssociatedGradedModulePiece (n : ℕ) :=
  F.N n ⧸ F.associatedGradedModuleLower n

abbrev AssociatedGradedModule :=
  ⨁ n : ℕ, F.AssociatedGradedModulePiece n

abbrev associatedGradedModuleMk (n : ℕ) :
    F.N n →ₗ[R] F.AssociatedGradedModulePiece n :=
  (F.associatedGradedModuleLower n).mkQ

noncomputable def associatedGradedModuleSmulToPiece (i j : ℕ) :
    ↥((I ^ i : Ideal R) : Submodule R R) →ₗ[R]
      F.N j →ₗ[R] F.AssociatedGradedModulePiece (i + j) :=
  LinearMap.mk₂ R
    (fun a m => F.associatedGradedModuleMk (i + j)
      ⟨a.1 • m.1, F.pow_smul_le i j (Submodule.smul_mem_smul a.2 m.2)⟩)
    (fun a b m => by rw [← map_add]; congr 1; ext; exact add_smul _ _ _)
    (fun c a m => by
      rw [← map_smul]
      congr 1
      apply Subtype.ext
      exact smul_assoc c a.1 m.1)
    (fun a m n => by rw [← map_add]; congr 1; ext; exact smul_add _ _ _)
    (fun c a m => by
      rw [← map_smul]
      congr 1
      apply Subtype.ext
      exact smul_comm a.1 c m.1)

theorem associatedGradedModuleSmulToPiece_ker_left (i j : ℕ) :
    associatedGradedRingLower I i ≤ (F.associatedGradedModuleSmulToPiece i j).ker := by
  intro a ha
  rw [LinearMap.mem_ker]
  apply LinearMap.ext
  intro m
  change (Submodule.Quotient.mk _ : F.AssociatedGradedModulePiece (i + j)) = 0
  rw [Submodule.Quotient.mk_eq_zero]
  change a.1 • m.1 ∈ F.N (i + j + 1)
  change a.1 ∈ I ^ (i + 1) at ha
  have h := F.pow_smul_le (i + 1) j (Submodule.smul_mem_smul ha m.2)
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

theorem associatedGradedModuleSmulToPiece_ker_right (i j : ℕ) :
    F.associatedGradedModuleLower j ≤ (F.associatedGradedModuleSmulToPiece i j).flip.ker := by
  intro m hm
  rw [LinearMap.mem_ker]
  apply LinearMap.ext
  intro a
  change (Submodule.Quotient.mk _ : F.AssociatedGradedModulePiece (i + j)) = 0
  rw [Submodule.Quotient.mk_eq_zero]
  change a.1 • m.1 ∈ F.N (i + j + 1)
  change m.1 ∈ F.N (j + 1) at hm
  have h := F.pow_smul_le i (j + 1) (Submodule.smul_mem_smul a.2 hm)
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

noncomputable def associatedGradedModuleSMul (i j : ℕ) :
    AssociatedGradedRingPiece I i →ₗ[R]
      F.AssociatedGradedModulePiece j →ₗ[R]
        F.AssociatedGradedModulePiece (i + j) :=
  (F.associatedGradedModuleSmulToPiece i j).liftQ₂
    (associatedGradedRingLower I i) (F.associatedGradedModuleLower j)
    (F.associatedGradedModuleSmulToPiece_ker_left i j)
    (F.associatedGradedModuleSmulToPiece_ker_right i j)

@[simp]
theorem associatedGradedModuleSMul_mk (i j : ℕ)
    (a : ↥((I ^ i : Ideal R) : Submodule R R)) (m : F.N j) :
    F.associatedGradedModuleSMul i j (Submodule.Quotient.mk a)
        (Submodule.Quotient.mk m) =
      F.associatedGradedModuleMk (i + j)
        ⟨a.1 • m.1, F.pow_smul_le i j (Submodule.smul_mem_smul a.2 m.2)⟩ := rfl

/-- The representative formula in the source notation, retained separately
from the simp-normal quotient-constructor lemma. -/
theorem associatedGradedModuleSMul_mk' (i j : ℕ)
    (a : ↥((I ^ i : Ideal R) : Submodule R R)) (m : F.N j) :
    F.associatedGradedModuleSMul i j (Ideal.associatedGradedRingMk I i a)
        (F.associatedGradedModuleMk j m) =
      F.associatedGradedModuleMk (i + j)
        ⟨a.1 • m.1, F.pow_smul_le i j (Submodule.smul_mem_smul a.2 m.2)⟩ := rfl

noncomputable instance :
    GradedMonoid.GSMul (AssociatedGradedRingPiece I) F.AssociatedGradedModulePiece where
  smul := fun a m => F.associatedGradedModuleSMul _ _ a m

theorem associatedGradedModuleMk_heq_of_eq {i j : ℕ} (hij : i = j) {m n : M} (hmn : m = n)
    (hi : m ∈ F.N i) (hj : n ∈ F.N j) :
    HEq (F.associatedGradedModuleMk i ⟨m, hi⟩)
      (F.associatedGradedModuleMk j ⟨n, hj⟩) := by
  subst j
  subst n
  rfl

theorem associatedGradedModule_one_smul (x : GradedMonoid F.AssociatedGradedModulePiece) :
    (1 : GradedMonoid (AssociatedGradedRingPiece I)) • x = x := by
  rcases x with ⟨j, x⟩
  induction x using Submodule.Quotient.induction_on with
  | _ x =>
    change (⟨0 + j,
      F.associatedGradedModuleSMul 0 j (Ideal.associatedGradedRingMk I 0 ⟨1, by simp⟩)
        (F.associatedGradedModuleMk j x)⟩ : Sigma F.AssociatedGradedModulePiece) =
      ⟨j, F.associatedGradedModuleMk j x⟩
    rw [F.associatedGradedModuleSMul_mk']
    exact Sigma.ext (zero_add j)
      (F.associatedGradedModuleMk_heq_of_eq (zero_add j) (one_smul R x.1) _ _)

theorem associatedGradedModule_mul_smul
    (a b : GradedMonoid (AssociatedGradedRingPiece I))
    (x : GradedMonoid F.AssociatedGradedModulePiece) :
    (a * b) • x = a • b • x := by
  rcases a with ⟨i,a⟩; rcases b with ⟨j,b⟩; rcases x with ⟨k,x⟩
  induction a using Submodule.Quotient.induction_on with
  | _ a =>
    induction b using Submodule.Quotient.induction_on with
    | _ b =>
      induction x using Submodule.Quotient.induction_on with
      | _ x =>
        change (⟨(i + j) + k,
          F.associatedGradedModuleSMul (i + j) k
            (associatedGradedRingMul I i j
              (Ideal.associatedGradedRingMk I i a) (Ideal.associatedGradedRingMk I j b))
            (F.associatedGradedModuleMk k x)⟩ : Sigma F.AssociatedGradedModulePiece) =
          ⟨i + (j + k),
            F.associatedGradedModuleSMul i (j + k) (Ideal.associatedGradedRingMk I i a)
              (F.associatedGradedModuleSMul j k (Ideal.associatedGradedRingMk I j b)
                (F.associatedGradedModuleMk k x))⟩
        rw [associatedGradedRingMul_mk', F.associatedGradedModuleSMul_mk',
          F.associatedGradedModuleSMul_mk', F.associatedGradedModuleSMul_mk']
        exact Sigma.ext (Nat.add_assoc i j k)
          (F.associatedGradedModuleMk_heq_of_eq (Nat.add_assoc i j k) (mul_smul a.1 b.1 x.1) _ _)

theorem associatedGradedModule_smul_add {i j} (a : AssociatedGradedRingPiece I i)
    (x y : F.AssociatedGradedModulePiece j) :
    GradedMonoid.GSMul.smul a (x + y) =
      GradedMonoid.GSMul.smul a x + GradedMonoid.GSMul.smul a y := by
  change F.associatedGradedModuleSMul i j a (x + y) = _
  exact (F.associatedGradedModuleSMul i j a).map_add x y

theorem associatedGradedModule_smul_zero {i j} (a : AssociatedGradedRingPiece I i) :
    GradedMonoid.GSMul.smul a (0 : F.AssociatedGradedModulePiece j) = 0 := by
  change F.associatedGradedModuleSMul i j a 0 = 0
  exact (F.associatedGradedModuleSMul i j a).map_zero

theorem associatedGradedModule_add_smul {i j} (a b : AssociatedGradedRingPiece I i)
    (x : F.AssociatedGradedModulePiece j) :
    GradedMonoid.GSMul.smul (a + b) x =
      GradedMonoid.GSMul.smul a x + GradedMonoid.GSMul.smul b x := by
  change F.associatedGradedModuleSMul i j (a + b) x = _
  rw [map_add]
  rfl

theorem associatedGradedModule_zero_smul {i j} (x : F.AssociatedGradedModulePiece j) :
    GradedMonoid.GSMul.smul (0 : AssociatedGradedRingPiece I i) x = 0 := by
  change F.associatedGradedModuleSMul i j 0 x = 0
  rw [map_zero]
  rfl

noncomputable instance :
    DirectSum.Gmodule (AssociatedGradedRingPiece I) F.AssociatedGradedModulePiece where
  one_smul := F.associatedGradedModule_one_smul
  mul_smul := F.associatedGradedModule_mul_smul
  smul_add := F.associatedGradedModule_smul_add
  smul_zero := F.associatedGradedModule_smul_zero
  add_smul := F.associatedGradedModule_add_smul
  zero_smul := F.associatedGradedModule_zero_smul

noncomputable instance : Module (Ideal.AssociatedGradedRing I) F.AssociatedGradedModule :=
  DirectSum.Gmodule.module (AssociatedGradedRingPiece I) F.AssociatedGradedModulePiece

/-- Intended representative behavior: the graded scalar action is induced by
the original `R`-module action. -/
example (i j : ℕ) (a : ↥((I ^ i : Ideal R) : Submodule R R)) (m : F.N j) :
    F.associatedGradedModuleSMul i j (Ideal.associatedGradedRingMk I i a)
        (F.associatedGradedModuleMk j m) =
      F.associatedGradedModuleMk (i + j)
        ⟨a.1 • m.1, F.pow_smul_le i j (Submodule.smul_mem_smul a.2 m.2)⟩ :=
  F.associatedGradedModuleSMul_mk' i j a m

/-- Separating boundary case: an element of `F.N (n+1)` vanishes in the
degree-`n` associated-graded module piece. -/
example (n : ℕ) (m : F.associatedGradedModuleLower n) :
    F.associatedGradedModuleMk n m.1 = 0 := by
  change (Submodule.Quotient.mk m.1 : F.AssociatedGradedModulePiece n) = 0
  rw [Submodule.Quotient.mk_eq_zero]
  exact m.2

end Filtration

end Ideal
