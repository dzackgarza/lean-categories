/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Lattices.Valued.LocalGlobal
public import LeanCategories.Lattices.Valued.Signature
public import Mathlib.Data.Nat.Factorization.Basic

/-!
# Rank, signature and determinant are genus invariants

Two integral lattices of one genus are isometric over `ℝ` and over every `ℤ_[p]`. This file reads
the three coarse invariants off those local isometries.

Rank and signature come straight from the real isometry. The determinant is the substantial part.
A Gram determinant is not an isometry invariant over an arbitrary ring: an isometry composed with
a change of basis multiplies it by the square of a unit. Over `ℝ` that square is positive, so the
two integer determinants have the same sign; over `ℤ_[p]` that square is a `p`-adic unit, so the
two integers are divisible by exactly the same powers of `p`. Same absolute value at every prime
and same sign force equality in `ℤ`.
-/

@[expose] public section

noncomputable section

open CategoryTheory
open LeanCategories.Modules.Bilinear.Valued

namespace LeanCategories.Lattices.Valued

universe u

section Isometry

variable {R : Type u} [CommRing R]

/-- The carrier equivalence underlying an isometry of integral lattices. -/
def latticeLinearEquivOfIso {L M : IntegralLatticeCat R} (e : L ≅ M) :
    L.obj.carrier ≃ₗ[R] M.obj.carrier :=
  BilinModuleCat.linearEquivOfIso ((isLattice R R).ι.mapIso e)

/-- An isometry of integral lattices preserves the pairing. -/
theorem latticeLinearEquivOfIso_pairing {L M : IntegralLatticeCat R} (e : L ≅ M)
    (x y : L.obj.carrier) :
    M.obj.pairing (latticeLinearEquivOfIso e x) (latticeLinearEquivOfIso e y) =
      L.obj.pairing x y :=
  BilinModuleCat.linearEquivOfIso_pairing _ x y

/-- An isometry carries a basis to a basis with the same Gram matrix. -/
theorem gramMatrix_map_latticeLinearEquivOfIso {I : Type*} [Fintype I] [DecidableEq I]
    {L M : IntegralLatticeCat R} (e : L ≅ M) (b : Module.Basis I R L.obj.carrier) :
    gramMatrix M (b.map (latticeLinearEquivOfIso e)) = gramMatrix L b := by
  ext i j
  simp only [gramMatrix, LinearMap.BilinForm.toMatrix_apply, Module.Basis.map_apply,
    BilinModuleCat.bilinMap_apply]
  exact latticeLinearEquivOfIso_pairing e (b i) (b j)

/-- Gram determinants of isometric lattices differ by the square of a unit. -/
theorem exists_determinant_eq_unit_sq_mul {I : Type*} [Fintype I] [DecidableEq I]
    {L M : IntegralLatticeCat R} (e : L ≅ M)
    (b : Module.Basis I R L.obj.carrier) (c : Module.Basis I R M.obj.carrier) :
    ∃ u : Rˣ, determinant M c = (u : R) ^ 2 * determinant L b := by
  set b' := b.map (latticeLinearEquivOfIso e)
  letI := b'.invertibleToMatrix c
  have hu : IsUnit (b'.toMatrix c).det :=
    (Matrix.isUnit_iff_isUnit_det (b'.toMatrix c)).mp (isUnit_of_invertible (b'.toMatrix c))
  have hdet := congrArg Matrix.det
    (LinearMap.BilinForm.toMatrix_mul_basis_toMatrix (b := b') c M.obj.bilinMap)
  simp only [Matrix.det_mul, Matrix.det_transpose] at hdet
  refine ⟨hu.unit, ?_⟩
  have hgram : gramMatrix M b' = gramMatrix L b :=
    gramMatrix_map_latticeLinearEquivOfIso e b
  simp only [determinant, ← hdet, IsUnit.unit_spec, gramMatrix] at hgram ⊢
  rw [hgram]
  ring

end Isometry

section BaseChange

variable {R : Type u} [CommRing R] (S : Type u) [CommRing S] [Algebra R S]

/-- The basis of a scalar extension extending a basis of the lattice. -/
def baseChangeBasis {I : Type*} (L : IntegralLatticeCat R)
    (b : Module.Basis I R L.obj.carrier) :
    Module.Basis I S ((baseChangeIntegral R S).obj L).obj.carrier :=
  b.baseChange S

@[simp]
theorem baseChangeBasis_apply {I : Type*} (L : IntegralLatticeCat R)
    (b : Module.Basis I R L.obj.carrier) (i : I) :
    baseChangeBasis S L b i = 1 ⊗ₜ[R] b i :=
  b.baseChange_apply S i

/-- Scalar extension maps a Gram matrix entrywise. -/
theorem gramMatrix_baseChangeIntegral {I : Type*} [Fintype I] [DecidableEq I]
    (L : IntegralLatticeCat R) (b : Module.Basis I R L.obj.carrier) :
    gramMatrix ((baseChangeIntegral R S).obj L) (baseChangeBasis S L b) =
      (gramMatrix L b).map (algebraMap R S) := by
  ext i j
  rw [gramMatrix, LinearMap.BilinForm.toMatrix_apply, BilinModuleCat.bilinMap_apply,
    baseChangeBasis_apply, baseChangeBasis_apply, baseChangeIntegral_pairing_tmul]
  simp [gramMatrix, LinearMap.BilinForm.toMatrix_apply]

/-- Scalar extension maps a Gram determinant. -/
theorem determinant_baseChangeIntegral {I : Type*} [Fintype I] [DecidableEq I]
    (L : IntegralLatticeCat R) (b : Module.Basis I R L.obj.carrier) :
    determinant ((baseChangeIntegral R S).obj L) (baseChangeBasis S L b) =
      algebraMap R S (determinant L b) := by
  rw [determinant, gramMatrix_baseChangeIntegral, determinant, RingHom.map_det,
    RingHom.mapMatrix_apply]

/-- Gram determinants of lattices isometric after scalar extension differ by the square of a
unit of the extended ring. -/
theorem exists_determinant_baseChange_eq_unit_sq_mul {I : Type*} [Fintype I] [DecidableEq I]
    {L M : IntegralLatticeCat R}
    (e : (baseChangeIntegral R S).obj L ≅ (baseChangeIntegral R S).obj M)
    (b : Module.Basis I R L.obj.carrier) (c : Module.Basis I R M.obj.carrier) :
    ∃ u : Sˣ,
      algebraMap R S (determinant M c) = (u : S) ^ 2 * algebraMap R S (determinant L b) := by
  obtain ⟨u, hu⟩ := exists_determinant_eq_unit_sq_mul e (baseChangeBasis S L b)
    (baseChangeBasis S M c)
  rw [determinant_baseChangeIntegral, determinant_baseChangeIntegral] at hu
  exact ⟨u, hu⟩

end BaseChange

section IntegerPlaces

/-- Two integers of equal `p`-adic norm at every prime have equal absolute value. -/
theorem natAbs_eq_of_padicInt_norm_eq {a b : ℤ}
    (h : ∀ (p : ℕ) (hp : p.Prime), letI : Fact p.Prime := ⟨hp⟩;
      ‖(a : ℤ_[p])‖ = ‖(b : ℤ_[p])‖) :
    a.natAbs = b.natAbs := by
  have key : ∀ x y : ℤ,
      (∀ (p : ℕ) (hp : p.Prime), letI : Fact p.Prime := ⟨hp⟩;
        ‖(x : ℤ_[p])‖ = ‖(y : ℤ_[p])‖) →
      x.natAbs ∣ y.natAbs := by
    intro x y hxy
    refine (Nat.dvd_iff_prime_pow_dvd_dvd y.natAbs x.natAbs).mpr ?_
    intro p k hp hdvd
    letI : Fact p.Prime := ⟨hp⟩
    have hxdvd : ((p : ℤ) ^ k) ∣ x := by
      rw [← Int.natAbs_dvd_natAbs]
      simpa using hdvd
    have hnorm : ‖(x : ℤ_[p])‖ ≤ (p : ℝ) ^ (-k : ℤ) := by
      refine PadicInt.norm_int_le_pow_iff_dvd.mpr ?_
      simpa using hxdvd
    rw [hxy p hp] at hnorm
    have hydvd : ((p : ℤ) ^ k) ∣ y := by
      simpa using PadicInt.norm_int_le_pow_iff_dvd.mp hnorm
    rw [← Int.natAbs_dvd_natAbs] at hydvd
    simpa using hydvd
  exact Nat.dvd_antisymm (key a b h) (key b a fun p hp ↦ (h p hp).symm)

/-- An integer scaled by the square of a `p`-adic unit keeps its `p`-adic norm. -/
theorem padicInt_norm_eq_of_unit_sq {p : ℕ} [Fact p.Prime] {a b : ℤ} {u : ℤ_[p]ˣ}
    (h : (b : ℤ_[p]) = (u : ℤ_[p]) ^ 2 * (a : ℤ_[p])) :
    ‖(a : ℤ_[p])‖ = ‖(b : ℤ_[p])‖ := by
  have hu : ‖(u : ℤ_[p])‖ = 1 := PadicInt.isUnit_iff.mp u.isUnit
  rw [h, norm_mul, norm_pow, hu, one_pow, one_mul]

/-- Two integers that agree up to a nonzero real square and have equal absolute value are
equal. -/
theorem eq_of_natAbs_eq_of_real_sq {a b : ℤ} {t : ℝ} (ht : t ≠ 0)
    (hreal : (b : ℝ) = t ^ 2 * (a : ℝ)) (hnat : a.natAbs = b.natAbs) : b = a := by
  rcases Int.natAbs_eq_natAbs_iff.mp hnat with hcase | hcase
  · exact hcase.symm
  · rcases eq_or_ne a 0 with ha | ha
    · omega
    · exfalso
      have hcast : ((b : ℤ) : ℝ) = -(a : ℝ) := by rw [hcase]; push_cast; ring
      rw [hcast] at hreal
      have hzero : (t ^ 2 + 1) * (a : ℝ) = 0 := by linarith [hreal]
      have hpos : (0 : ℝ) < t ^ 2 + 1 := by positivity
      have hane : ((a : ℤ) : ℝ) ≠ 0 := Int.cast_ne_zero.mpr ha
      exact hane (by
        rcases mul_eq_zero.mp hzero with h | h
        · exact absurd h hpos.ne'
        · exact h)

end IntegerPlaces

section Genus

variable {L M : FiniteProjectiveLatticeCat ℤ ℤ}

/-- Lattices of one genus have equal rank. -/
theorem rank_eq_of_sameGenus (h : SameGenus L M) : L.rank = M.rank := by
  obtain ⟨hreal, -⟩ := (sameGenus_iff_isClassicallyLocallyIsometric L M).mp h
  obtain ⟨e⟩ := hreal
  letI : Module.Free ℤ L.obj.obj.carrier := L.carrier_free
  letI : Module.Free ℤ M.obj.obj.carrier := M.carrier_free
  letI : Module.Finite ℤ L.obj.obj.carrier := L.property
  letI : Module.Finite ℤ M.obj.obj.carrier := M.property
  have hfin : Module.finrank ℝ (TensorProduct ℤ ℝ L.obj.obj.carrier) =
      Module.finrank ℝ (TensorProduct ℤ ℝ M.obj.obj.carrier) :=
    (latticeLinearEquivOfIso e).finrank_eq
  rw [FiniteProjectiveLatticeCat.rank, FiniteProjectiveLatticeCat.rank,
    ← Module.finrank_baseChange (R := ℝ) (S := ℤ) (M' := L.obj.obj.carrier),
    ← Module.finrank_baseChange (R := ℝ) (S := ℤ) (M' := M.obj.obj.carrier)]
  exact hfin

/-- Lattices of one genus have equal real signature. -/
theorem signature_eq_of_sameGenus (h : SameGenus L M) :
    integralSignature L = integralSignature M := by
  obtain ⟨hreal, -⟩ := (sameGenus_iff_isClassicallyLocallyIsometric L M).mp h
  obtain ⟨e⟩ := hreal
  exact signature_eq_of_iso ℝ ((finiteProjectiveToFiniteForm ℝ ℝ).mapIso
    ((isFiniteProjectiveLattice ℝ ℝ).fullyFaithfulι.preimageIso e))

/-- Lattices of one genus have Gram determinants agreeing up to the square of a unit at every
place: a real square at the archimedean place and a `p`-adic unit square at each prime. -/
theorem determinant_sq_class_eq_of_sameGenus (h : SameGenus L M)
    {I : Type*} [Fintype I] [DecidableEq I]
    (b : Module.Basis I ℤ L.obj.obj.carrier) (c : Module.Basis I ℤ M.obj.obj.carrier) :
    (∃ t : ℝˣ,
        ((determinant M.obj c : ℤ) : ℝ) = (t : ℝ) ^ 2 * ((determinant L.obj b : ℤ) : ℝ)) ∧
      ∀ (p : ℕ) (hp : p.Prime), letI : Fact p.Prime := ⟨hp⟩;
        ∃ u : ℤ_[p]ˣ, ((determinant M.obj c : ℤ) : ℤ_[p]) =
          (u : ℤ_[p]) ^ 2 * ((determinant L.obj b : ℤ) : ℤ_[p]) := by
  obtain ⟨hreal, hpadic⟩ := (sameGenus_iff_isClassicallyLocallyIsometric L M).mp h
  constructor
  · obtain ⟨e⟩ := hreal
    obtain ⟨t, ht⟩ := exists_determinant_baseChange_eq_unit_sq_mul ℝ e b c
    exact ⟨t, by simpa using ht⟩
  · intro p hp
    letI : Fact p.Prime := ⟨hp⟩
    obtain ⟨e⟩ := hpadic p hp
    obtain ⟨u, hu⟩ := exists_determinant_baseChange_eq_unit_sq_mul ℤ_[p] e b c
    exact ⟨u, by simpa using hu⟩

/-- **Lattices of one genus have equal Gram determinant.** The real place fixes the sign and each
prime fixes the `p`-adic valuation. -/
theorem determinant_eq_of_sameGenus (h : SameGenus L M)
    {I : Type*} [Fintype I] [DecidableEq I]
    (b : Module.Basis I ℤ L.obj.obj.carrier) (c : Module.Basis I ℤ M.obj.obj.carrier) :
    determinant M.obj c = determinant L.obj b := by
  obtain ⟨⟨t, ht⟩, hpadic⟩ := determinant_sq_class_eq_of_sameGenus h b c
  refine eq_of_natAbs_eq_of_real_sq (t := (t : ℝ)) (Units.ne_zero t) ht ?_
  refine natAbs_eq_of_padicInt_norm_eq ?_
  intro p hp
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨u, hu⟩ := hpadic p hp
  exact padicInt_norm_eq_of_unit_sq hu

end Genus

end LeanCategories.Lattices.Valued
