/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 License as described in the file LICENSE.
-/
module

public import Mathlib.GroupTheory.FiniteAbelian.Basic
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.LinearAlgebra.TensorProduct.Prod
public import Mathlib.LinearAlgebra.DirectSum.TensorProduct
public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.Algebra.Module.Torsion.Basic
public import LeanCategories.Homological.TorReductions
public import LeanCategories.Homological.TorArbitrary
public import LeanCategories.Homological.TorStages
public import LeanCategories.Homological.TorFreeResolution
public import LeanCategories.Homological.TorTorsionClass
public import LeanCategories.Homological.CyclicTor
public import LeanCategories.Homological.TorBridge

@[expose] public section

/-!
# TorExercise3A6: Hatcher §3.A Exercise 6 for arbitrary abelian groups

Card `E-HAT-3.A-6` of the qualifying-exam corpus.  Source: Hatcher, *Algebraic
Topology* (2002), §3.A Exercise 6 (printed p. 267): for all abelian groups `A`
and `B`, `Tor(A, B)` is a torsion group, and `Tor(A, B)` has an element of
order `n` if and only if `A` and `B` both have one.

LC-09 search record (formalization corpus, `scripts/formalization_corpus.py`,
2026-11-13, plus local Mathlib): queries `Tor torsion group`, `Tor commutes
with direct limit`, `element of order torsion`, `torsion subgroup flat
quotient`, `Tor kernel free resolution`, `orderOf`, `IsOfFinAddOrder`,
`Module.IsTorsion`, `IsAddTorsion.of_surjective`, `tensor product direct sum
distributivity`, `kernel of direct sum of maps`, `order of sum of elements
coprime`, `order of scalar multiple element`, `structure theorem finitely
generated abelian group`, `free abelian group surjection presentation
Finsupp`, `addOrderOf injective homomorphism`.  Hits used: Mathlib's structure
theorem `AddCommGroup.equiv_free_prod_directSum_zmod`, the DFinsupp tensor
distributivity `TensorProduct.directSumRight`, the order lemmas
`addOrderOf_nsmul'` and `addOrderOf_add_eq_mul_addOrderOf_of_coprime`, and
`IsAddTorsion.of_surjective` (which replaces the certificate's
`TorFGTorsion.isAddTorsion_of_linearEquiv`, applied backwards along `e.symm`).
Mathlib's `CategoryTheory.Tor` still supplies no long-exact-sequence,
balancing or colimit-comparison API, so the reduction is carried elementwise
through the presentation-level kernels of `TorReductions` and the subgroup
stages of `TorStages`, as the sibling certificates record.

## The route

*The torsion statement.*  `Tor₁(A, B)` is presented as a kernel for arbitrary
`A` by `TorArbitrary.torOneIsoKerIncl` (the dimension-shift bridge of Weibel
Exercise 2.4.3).  Every element of that kernel descends, by
`TorStages.exists_stage_of_free`, to the kernel of a finitely generated stage
whose middle term is a finitely generated direct summand of a free module.  At
that stage the group is finitely generated, and the finitely generated case
runs through the structure theorem: the free summand contributes nothing
(`isZero_torOne_of_projective`) and each cyclic prime-power summand is
`CyclicTor.torOneCyclicIsoTorsionBy`, the `n`-torsion of `B`.  Torsion
transports back along the stage inclusion because the stage's relation module
sits in the middle term so that the cokernel of the stage inclusion is
torsion-free hence flat, and `LinearMap.lTensor_injective_of_exact_of_flat`
(`TorReductions.rTensor_injective_of_flat_cokernel`) keeps the tensor map
injective.

*The order statement.*  Both directions reduce to prime powers by the coprime
order law `addOrderOf_add_eq_mul_addOrderOf_of_coprime` and the scaling law
`addOrderOf_nsmul'`.  For a prime power the two halves are dual.  An element of
order `p ^ k` in `A` gives the syzygy element `z = p ^ k • single a 1`, whose
cyclic subgroup is pure in the syzygy because `z` is supported at `a` alone; the
quotient is torsion-free, hence flat, so `z ⊗ b` survives in `ker (pres A) ⊗ B`
with order exactly `p ^ k` and transports to `Tor1` along the presentation
bridge.  Conversely an element of `Tor1` descends to a finitely generated stage,
whose relation map is put in Smith normal form; the coordinate engine
`tensorPiEquiv` reads a coordinate of order `p ^ k` in `B` off the diagonal
entries, and the diagonal entry itself is an elementary divisor of the stage's
group, giving an element of order `p ^ k` in `A`.
-/

namespace LeanCategories.Homological.TorExercise3A6

open CategoryTheory Limits MonoidalCategory
open scoped TensorProduct DirectSum ZeroObject

/-! ## Order arithmetic -/

section OrderArithmetic

variable {M : Type*} [AddCommGroup M]

/-- An element killed by `n ≠ 0`, and by no smaller positive multiple, has
additive order exactly `n`. -/
theorem addOrderOf_eq_of_nsmul {n : ℕ} (hn : n ≠ 0) (x : M)
    (hk : n • x = 0) (hmin : ∀ m : ℕ, 0 < m → m < n → m • x ≠ 0) :
    addOrderOf x = n := by
  have hfin : IsOfFinAddOrder x :=
    isOfFinAddOrder_iff_nsmul_eq_zero.mpr ⟨n, Nat.pos_of_ne_zero hn, hk⟩
  by_contra hne
  have hlt : addOrderOf x < n :=
    lt_of_le_of_ne (addOrderOf_le_of_nsmul_eq_zero (Nat.pos_of_ne_zero hn) hk) hne
  exact hmin (addOrderOf x) hfin.addOrderOf_pos hlt (by simp)

/-- Scaling an element of order `N` by the quotient `N / n` gives an element of order `n`,
for every positive divisor `n` of a positive `N`. -/
theorem addOrderOf_smul_div {N n : ℕ} (_hn : 0 < n) (hN : 0 < N) (hnN : n ∣ N) (x : M)
    (hx : addOrderOf x = N) : addOrderOf ((N / n) • x) = n := by
  have hpos : 0 < N / n := Nat.pos_of_dvd_of_pos (Nat.div_dvd_of_dvd hnN) (by omega)
  have hND : n * (N / n) = N := Nat.mul_div_cancel' hnN
  rw [addOrderOf_nsmul' x (ne_of_gt hpos), hx,
    Nat.gcd_eq_right (Nat.div_dvd_of_dvd hnN)]
  exact Nat.div_eq_of_eq_mul_left hpos hND.symm

/-- The additive order is preserved by an injective ℤ-linear map. -/
theorem addOrderOf_map_eq_of_injective {N : Type*} [AddCommGroup N] (f : M →ₗ[ℤ] N)
    (hf : Function.Injective f) (x : M) : addOrderOf (f x) = addOrderOf x := by
  have key : ∀ m : ℕ, m • (f x) = 0 ↔ m • x = 0 := by
    intro m
    constructor
    · intro h
      have h' : f (m • x) = 0 := by rw [map_nsmul f m x]; exact h
      rw [← map_zero f] at h'
      exact hf h'
    · intro h
      rw [← map_nsmul f m x, h, map_zero]
  by_cases h : IsOfFinAddOrder x
  · have hx : addOrderOf x ≠ 0 := fun h0 => by
      have := h.addOrderOf_pos
      omega
    have hfx : IsOfFinAddOrder (f x) := by
      obtain ⟨m, hm, hm0⟩ := isOfFinAddOrder_iff_nsmul_eq_zero.mp h
      exact isOfFinAddOrder_iff_nsmul_eq_zero.mpr ⟨m, hm, (key m).mpr hm0⟩
    refine le_antisymm ?_ ?_
    · refine addOrderOf_le_of_nsmul_eq_zero h.addOrderOf_pos ?_
      exact (key (addOrderOf x)).mpr (by simp)
    · refine addOrderOf_le_of_nsmul_eq_zero hfx.addOrderOf_pos ?_
      exact (key (addOrderOf (f x))).mp (by simp)
  · have hfx : ¬ IsOfFinAddOrder (f x) := fun hf2 => by
      obtain ⟨m, hm, hm0⟩ := isOfFinAddOrder_iff_nsmul_eq_zero.mp hf2
      exact h (isOfFinAddOrder_iff_nsmul_eq_zero.mpr ⟨m, hm, (key m).mp hm0⟩)
    rw [addOrderOf_eq_zero_iff.mpr hfx, addOrderOf_eq_zero_iff.mpr h]

/-- The order of the sum of two elements of coprime orders is the product of the orders. -/
theorem addOrderOf_add_eq_mul_of_coprime (x y : M) (hx : 0 < addOrderOf x)
    (hy : 0 < addOrderOf y) (hco : (addOrderOf x).Coprime (addOrderOf y)) :
    addOrderOf (x + y) = addOrderOf x * addOrderOf y := by
  have hax : (addOrderOf x) • x = 0 := by simp
  have hby : (addOrderOf y) • y = 0 := by simp
  refine addOrderOf_eq_of_nsmul (by positivity) (x + y) ?_ ?_
  · rw [smul_add]
    have h1 : (addOrderOf x * addOrderOf y) • x = 0 :=
      addOrderOf_dvd_iff_nsmul_eq_zero.mp (Nat.dvd_mul_right _ _)
    have h2 : (addOrderOf x * addOrderOf y) • y = 0 :=
      addOrderOf_dvd_iff_nsmul_eq_zero.mp (Nat.dvd_mul_left _ _)
    rw [h1, h2, add_zero]
  · intro m hm hmlt h0
    rw [smul_add] at h0
    have hmix : m • x = -(m • y) := eq_neg_of_add_eq_zero_left h0
    have hmiy : m • y = -(m • x) := eq_neg_of_add_eq_zero_right h0
    have h2 : addOrderOf y • (m • x) = 0 := by
      rw [hmix, smul_neg, smul_smul, Nat.mul_comm, ← smul_smul, hby, smul_zero, neg_zero]
    have h1 : (addOrderOf y * m) • x = 0 := by rw [← smul_smul]; exact h2
    have hdvd1 : addOrderOf x ∣ m * addOrderOf y := by
      rw [Nat.mul_comm]
      exact addOrderOf_dvd_iff_nsmul_eq_zero.mpr h1
    have hd1 : addOrderOf x ∣ m := hco.dvd_of_dvd_mul_right hdvd1
    have h4 : addOrderOf x • (m • y) = 0 := by
      rw [hmiy, smul_neg, smul_smul, Nat.mul_comm, ← smul_smul, hax, smul_zero, neg_zero]
    have h3 : (addOrderOf x * m) • y = 0 := by rw [← smul_smul]; exact h4
    have hdvd2 : addOrderOf y ∣ m * addOrderOf x := by
      rw [Nat.mul_comm]
      exact addOrderOf_dvd_iff_nsmul_eq_zero.mpr h3
    have hd2 : addOrderOf y ∣ m := hco.symm.dvd_of_dvd_mul_right hdvd2
    have habm : addOrderOf x * addOrderOf y ∣ m := hco.mul_dvd_of_dvd_of_dvd hd1 hd2
    exact absurd (Nat.le_of_dvd hm habm) (not_le.2 hmlt)

end OrderArithmetic

/-! ## The prime-power reduction of "has an element of order `n`"

Both statements of the exercise reduce, in all three groups involved, to prime powers: an
element of order `n > 0` yields elements of order `p ^ k` for every `p ^ k ∣ n` by scaling
(`addOrderOf_smul_div`), and conversely elements of order `p ^ k` for all the prime powers in
`n`'s factorization assemble into one of order `n` by the coprime order law, once the full
power of each prime is peeled off (`exists_prime_pow_mul_of_dvd`) so that the two factors
really are coprime. -/

section PrimePow

variable {M : Type*} [AddCommGroup M]

/-- An element of order `N > 0` yields an element of order `n`, for every positive divisor `n`
of its order. -/
theorem exists_addOrderOf_of_dvd_addOrderOf {N n : ℕ} (hN : 0 < N) (hn : n ∣ N) (x : M)
    (hx : addOrderOf x = N) : ∃ y : M, addOrderOf y = n :=
  ⟨(N / n) • x, addOrderOf_smul_div (Nat.pos_of_dvd_of_pos hn hN) hN hn x hx⟩

/-- Every positive `n` divisible by the prime `p` factors as `p ^ k * m` with `k > 0` and
`p ∤ m`, by strong induction on `n`. -/
theorem exists_prime_pow_mul_of_dvd {p : ℕ} (hp : p.Prime) {n : ℕ} (hn : 0 < n)
    (hpn : p ∣ n) : ∃ (k m : ℕ), n = p ^ k * m ∧ 0 < k ∧ ¬ p ∣ m := by
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    have hp2 : 2 ≤ p := hp.one_lt
    obtain ⟨n', rfl⟩ := hpn
    have hn' : 0 < n' := by
      rcases Nat.eq_zero_or_pos n' with h0 | h0
      · rw [h0, mul_zero] at hn
        exact absurd hn (by omega)
      · exact h0
    by_cases hd : p ∣ n'
    · obtain ⟨k, m, rfl, hk, hm⟩ := ih n' (by
          have := (Nat.mul_lt_mul_right hn').mpr hp.one_lt
          simpa using this) hn' hd
      exact ⟨k + 1, m, by rw [pow_succ]; ring, by omega, hm⟩
    · exact ⟨1, n', by rw [pow_one], by omega, hd⟩

/-- A divisor of a prime power is a smaller power of the same prime, by induction on the
exponent. -/
theorem exists_pow_eq_of_dvd_prime_pow {p k d : ℕ} (hp : p.Prime) (hd : d ∣ p ^ k) :
    ∃ j ≤ k, d = p ^ j := by
  induction k generalizing d with
  | zero =>
      rw [pow_zero] at hd
      obtain rfl := Nat.dvd_one.mp hd
      exact ⟨0, le_refl 0, (pow_zero p).symm⟩
  | succ k ih =>
      rw [pow_succ] at hd
      by_cases hpd : p ∣ d
      · obtain ⟨d', rfl⟩ := hpd
        rw [Nat.mul_comm (p ^ k) p] at hd
        obtain ⟨j, hj, rfl⟩ := ih (Nat.dvd_of_mul_dvd_mul_left hp.pos hd)
        exact ⟨j + 1, by omega, by rw [pow_succ, Nat.mul_comm]⟩
      · have hcop : d.Coprime p := (hp.coprime_iff_not_dvd.mpr hpd).symm
        obtain ⟨j, hj, rfl⟩ := ih (hcop.dvd_of_dvd_mul_left (by rwa [Nat.mul_comm] at hd))
        exact ⟨j, by omega, rfl⟩

/-- **The prime-power assembly.** If a group has an element of order `p ^ k` for every prime
power `p ^ k` dividing the positive number `n`, then it has an element of order `n`: peel off
one prime's full power, use the induction hypothesis on the coprime rest, and add. -/
theorem exists_addOrderOf_of_forall_prime_pow {n : ℕ} (hn : 0 < n)
    (h : ∀ p : ℕ, p.Prime → ∀ k : ℕ, 0 < k → p ^ k ∣ n → ∃ y : M, addOrderOf y = p ^ k) :
    ∃ x : M, addOrderOf x = n := by
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    by_cases h1 : n = 1
    · subst h1
      exact ⟨0, addOrderOf_zero⟩
    · obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd h1
      obtain ⟨k, m, rfl, hk, hpm⟩ := exists_prime_pow_mul_of_dvd hp hn hpdvd
      have hmpos : 0 < m := by
        rcases Nat.eq_zero_or_pos m with h0 | h0
        · rw [h0, mul_zero] at hn
          exact absurd hn (by omega)
        · exact h0
      have h1lt : 1 < p ^ k := one_lt_pow' hp.one_lt (ne_of_gt hk)
      have hcop : (p ^ k).Coprime m := by
        have hpmc : p.Coprime m := hp.coprime_iff_not_dvd.mpr hpm
        have := hpmc.pow k 1
        rwa [pow_one] at this
      have hmlt : m < p ^ k * m := by
        have := (Nat.mul_lt_mul_right hmpos).mpr h1lt
        simpa using this
      obtain ⟨y₁, hy₁⟩ := h p hp k hk (dvd_mul_right (p ^ k) m)
      obtain ⟨y₂, hy₂⟩ := ih m hmlt hmpos fun q hq j hj hqj => h q hq j hj (by
        obtain ⟨w, hw⟩ := hqj
        rw [hw]
        exact (dvd_mul_right (q ^ j) w).mul_left (p ^ k))
      refine ⟨y₁ + y₂, ?_⟩
      have hy1pos : 0 < addOrderOf y₁ := by rw [hy₁]; exact lt_trans zero_lt_one h1lt
      have hy2pos : 0 < addOrderOf y₂ := by rw [hy₂]; exact hmpos
      rw [addOrderOf_add_eq_mul_of_coprime y₁ y₂ hy1pos hy2pos
        (by rw [hy₁, hy₂]; exact hcop), hy₁, hy₂]

end PrimePow

/-! ## The order analysis of a direct sum

The additive order of a `DFinsupp` element is detected componentwise: a number kills the
element iff it kills every component (`nsmul_eq_zero_dfinsupp_iff`), so at prime powers an
element of order `p ^ k` has a component of order exactly `p ^ k`
(`exists_comp_addOrderOf_eq_of_eq_prime_pow`), and a single-supported element has the order of
its value (`addOrderOf_dfinsupp_single`). -/

section DFinsuppOrders

variable {M N : Type*} [AddCommGroup M] [AddCommGroup N]

/-- Two elements (possibly of different groups) killed by the same natural numbers have the
same additive order. -/
theorem addOrderOf_eq_of_forall_nsmul_eq_zero (x : M) (y : N)
    (h : ∀ m : ℕ, m • x = 0 ↔ m • y = 0) : addOrderOf x = addOrderOf y := by
  refine Nat.dvd_antisymm ?_ ?_
  · exact addOrderOf_dvd_iff_nsmul_eq_zero.mpr ((h (addOrderOf y)).mpr (by simp))
  · exact addOrderOf_dvd_iff_nsmul_eq_zero.mpr ((h (addOrderOf x)).mp (by simp))

variable {ι : Type*} {β : ι → Type*} [DecidableEq ι] [∀ i, AddCommGroup (β i)]

omit [DecidableEq ι] in
/-- A number kills a `DFinsupp` element iff it kills every component. -/
theorem nsmul_eq_zero_dfinsupp_iff (m : ℕ) (x : Π₀ i, β i) :
    m • x = 0 ↔ ∀ i, m • (x i) = 0 := by
  constructor
  · intro h i
    have h0 : (m • x) i = 0 := by rw [h, DFinsupp.zero_apply]
    rwa [DFinsupp.nsmul_apply] at h0
  · intro h
    ext i
    rw [DFinsupp.nsmul_apply, h i, DFinsupp.zero_apply]

/-- A single-supported `DFinsupp` element has the additive order of its value. -/
theorem addOrderOf_dfinsupp_single (i : ι) (y : β i) :
    addOrderOf (DFinsupp.single i y) = addOrderOf y := by
  refine addOrderOf_eq_of_forall_nsmul_eq_zero _ _ fun m => ?_
  rw [nsmul_eq_zero_dfinsupp_iff]
  constructor
  · intro h
    have hi : m • (DFinsupp.single i y) i = 0 := h i
    rw [DFinsupp.single_apply] at hi
    simpa using hi
  · intro h j
    by_cases hj : i = j
    · subst hj
      rw [DFinsupp.single_apply]
      simpa using h
    · rw [DFinsupp.single_apply]
      simp [hj]

/-- At a prime power, an element of a direct sum whose order is `p ^ k` has a component of
order exactly `p ^ k`. -/
theorem exists_comp_addOrderOf_eq_of_eq_prime_pow {p k : ℕ} (hp : p.Prime) (hk : 0 < k)
    (x : Π₀ i, β i) (hx : addOrderOf x = p ^ k) :
    ∃ (j : ι) (y : β j), addOrderOf y = p ^ k := by
  by_contra hcon
  push_neg at hcon
  have hkill0 : p ^ k • x = 0 := by rw [← hx]; exact addOrderOf_nsmul_eq_zero x
  have hcomp : ∀ i, addOrderOf (x i) ∣ p ^ k := fun i =>
    addOrderOf_dvd_iff_nsmul_eq_zero.mpr ((nsmul_eq_zero_dfinsupp_iff (p ^ k) x).mp hkill0 i)
  have hkill : p ^ (k - 1) • x = 0 := by
    refine (nsmul_eq_zero_dfinsupp_iff _ _).mpr fun i => ?_
    have hd : addOrderOf (x i) ∣ p ^ (k - 1) := by
      obtain ⟨j, hj, hjeq⟩ := exists_pow_eq_of_dvd_prime_pow hp (hcomp i)
      have hne : j ≠ k := fun hje => by
        rw [hje] at hjeq
        exact hcon i (x i) hjeq
      rw [hjeq]
      exact Nat.pow_dvd_pow p (by omega)
    exact addOrderOf_dvd_iff_nsmul_eq_zero.mp hd
  have hord : p ^ k ∣ p ^ (k - 1) := by
    rw [← hx]
    exact addOrderOf_dvd_iff_nsmul_eq_zero.mpr hkill
  rw [Nat.pow_dvd_pow_iff_le_right hp.one_lt] at hord
  omega

/-- **The prime-power order census of a direct sum**: a direct sum has an element of order
`p ^ k` iff one of its summands does. -/
theorem exists_addOrderOf_dfinsupp_iff_prime_pow {p k : ℕ} (hp : p.Prime) (hk : 0 < k) :
    (∃ x : Π₀ i, β i, addOrderOf x = p ^ k) ↔ ∃ (j : ι) (y : β j), addOrderOf y = p ^ k := by
  constructor
  · intro ⟨x, hx⟩
    exact exists_comp_addOrderOf_eq_of_eq_prime_pow hp hk x hx
  · intro ⟨j, y, hy⟩
    exact ⟨DFinsupp.single j y, addOrderOf_dfinsupp_single j y ▸ hy⟩

end DFinsuppOrders

/-! ## The structure-theorem presentation of the model group

For a finitely generated abelian group the structure theorem
(`AddCommGroup.equiv_free_prod_directSum_zmod`) provides an additive equivalence with a model
group `(Fin n →₀ ℤ) × ⨁ i, ZMod (p i ^ e i)`.  This section builds the free presentation of
that model group explicitly: the middle term `(Fin n →₀ ℤ) × (⨁ i : ι, ℤ)`, the surjection given by
the identity on the free part and the canonical map `ℤ → ZMod (p i ^ e i)` on the cyclic part,
and the relation map, which is multiplication by `p i ^ e i` coordinatewise.  The syzygy is
therefore the direct sum `⨁ i, ℤ` again, which is free, so the two-term resolution of the
generalized presentation applies. -/


/-! ## The two-term resolution of a free presentation, at any free middle term

`TorFreeResolution` builds its two-term projective resolution only for presentations whose
middle term is `(Fin r → ℤ)`.  The structure-theorem presentation below has middle term
`(Fin n →₀ ℤ) × (⨁ i : ι, ℤ)`, so the construction is generalized here: any surjection with
`F₀` free and the syzygy `ker f` projective carries the same two-term resolution, with
the same quasi-isomorphism proof.  The `(Fin r → ℤ)`-shaped original is the special case
`F₀ = Fin r → ℤ`; the generalization is a copy with the type and the projectivity proof
abstracted, not new mathematics. -/

section GeneralTwoTerm

variable {F₀ A : Type} [AddCommGroup F₀] [AddCommGroup A] [Module ℤ F₀] [Module ℤ A]
  (f : F₀ →ₗ[ℤ] A)

/-- The syzygy's carrier as a `ModuleCat` object, with the instances `ModuleCat` synthesizes:
the `toIntModule` structure, reached through the explicit instance arguments so that no
`Submodule.module` diamond is synthesized at the application site. -/
noncomputable def kerOf : ModuleCat ℤ :=
  @ModuleCat.of ℤ Int.instRing ↥(LinearMap.ker f) (LinearMap.ker f).addCommGroup
    (AddCommGroup.toIntModule ↥(LinearMap.ker f))

/-- The syzygy inclusion into the free middle term: `Subtype.val` as a ℤ-linear map for the
`toIntModule` structure on the syzygy, the structure-bridge `int_smul_eq_zsmul` supplying
scalar-linearity. -/
noncomputable def kerSubtypeHom : kerOf f ⟶ ModuleCat.of ℤ F₀ :=
  @ModuleCat.ofHom ℤ Int.instRing ↥(LinearMap.ker f) F₀
    (LinearMap.ker f).addCommGroup (AddCommGroup.toIntModule ↥(LinearMap.ker f))
    _ _
    { toFun := (Subtype.val : ↥(LinearMap.ker f) → F₀)
      map_add' := fun x y => rfl
      map_smul' := fun c x => by
        simp only [RingHom.id_apply]
        exact (int_smul_eq_zsmul (inferInstance : Module ℤ F₀) c (x : F₀)).symm }

/-- The two-term complex of a free presentation with projective syzygy. -/
noncomputable def twoTermComplexG : ChainComplex (ModuleCat ℤ) ℕ :=
  ChainComplex.mk' (ModuleCat.of ℤ F₀) (kerOf f) (kerSubtypeHom f)
    (fun _ => ⟨0, 0, by simp⟩)

theorem twoTermComplexG_X_zero : (twoTermComplexG f).X 0 = ModuleCat.of ℤ F₀ :=
  ChainComplex.mk'_X_0 ..

theorem twoTermComplexG_X_one : (twoTermComplexG f).X 1 = kerOf f :=
  ChainComplex.mk'_X_1 ..

theorem twoTermComplexG_d_one_zero :
    (twoTermComplexG f).d 1 0 = kerSubtypeHom f :=
  ChainComplex.mk'_d_1_0 ..

theorem twoTermComplexG_isZero_X_two : IsZero ((twoTermComplexG f).X 2) :=
  IsZero.of_iso (isZero_zero (ModuleCat ℤ))
    (ChainComplex.mk'XIso (ModuleCat.of ℤ F₀) (kerOf f) (kerSubtypeHom f)
      (fun _ => ⟨0, 0, by simp⟩) 0)

theorem twoTermComplexG_isZero_X (n : ℕ) (hn : 2 ≤ n) : IsZero ((twoTermComplexG f).X n) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  exact IsZero.of_iso (isZero_zero (ModuleCat ℤ))
    (ChainComplex.mk'XIso (ModuleCat.of ℤ F₀) (kerOf f) (kerSubtypeHom f)
      (fun _ => ⟨0, 0, by simp⟩) k)

theorem twoTermComplexG_mono_d_one_zero :
    Mono ((twoTermComplexG f).d 1 0) :=
  ConcreteCategory.mono_of_injective _ fun _x _y h => Subtype.ext h

theorem twoTermComplexG_projective [Module.Free ℤ F₀]
    [Projective (kerOf f)] (n : ℕ) :
    Projective ((twoTermComplexG f).X n) := by
  match n with
  | 0 =>
    exact (twoTermComplexG_X_zero f).symm ▸
      (by infer_instance : Projective (ModuleCat.of ℤ F₀))
  | 1 =>
    exact (twoTermComplexG_X_one f).symm ▸ ‹Projective (kerOf f)›
  | k + 2 =>
    exact Projective.of_iso (Iso.symm (ChainComplex.mk'XIso (ModuleCat.of ℤ F₀)
      (kerOf f) (kerSubtypeHom f)
      (fun _ => ⟨0, 0, by simp⟩) k)) (inferInstance : Projective (0 : ModuleCat ℤ))

noncomputable def twoTermPiG :
    twoTermComplexG f ⟶ (ChainComplex.single₀ (ModuleCat ℤ)).obj (ModuleCat.of ℤ A) :=
  (ChainComplex.toSingle₀Equiv _ _).symm ⟨ModuleCat.ofHom f, by
    rw [twoTermComplexG_d_one_zero]
    apply ModuleCat.hom_ext
    ext x
    exact x.2⟩

theorem twoTermComplexG_homology_one_isZero :
    IsZero ((twoTermComplexG f).homology 1) := by
  have hmono : Mono ((twoTermComplexG f).d 1 0) := twoTermComplexG_mono_d_one_zero f
  exact IsZero.of_iso (isZero_kernel_of_mono ((twoTermComplexG f).d 1 0))
    (TorBridge.homologyOneIsoKernel (twoTermComplexG_isZero_X_two f))

theorem twoTermComplexG_homology_isZero (k : ℕ) :
    IsZero ((twoTermComplexG f).homology (k + 2)) := by
  have hzero3 : IsZero ((twoTermComplexG f).X (k + 3)) :=
    twoTermComplexG_isZero_X f (k + 3) (by omega)
  have hd : (twoTermComplexG f).d (k + 3) (k + 2) = 0 := IsZero.eq_of_src hzero3 _ _
  refine IsZero.of_iso (TorFreeResolution.isZero_kernel_of_isZero_source
    ((twoTermComplexG f).d (k + 2) (k + 1)) (twoTermComplexG_isZero_X f (k + 2) (by omega)))
    (TorFreeResolution.homologyIsoKernelAt (twoTermComplexG f) k hd)

theorem twoTermComplexG_homology_pos_isZero (i : ℕ) (hi : i ≠ 0) :
    IsZero ((twoTermComplexG f).homology i) := by
  match i with
  | 0 => exact absurd rfl hi
  | 1 => exact twoTermComplexG_homology_one_isZero f
  | k + 2 => exact twoTermComplexG_homology_isZero f k

theorem quasiIsoAt_twoTermPiG_zero (hf : Function.Surjective f) :
    QuasiIsoAt (twoTermPiG f) 0 := by
  rw [ChainComplex.quasiIsoAt₀_iff]
  have hc := ModuleCat.isColimitCokernelCofork
    (f := kerSubtypeHom f)
    (g := (ModuleCat.ofHom f : ModuleCat.of ℤ F₀ ⟶ ModuleCat.of ℤ A))
    (fun a => ⟨fun h => ⟨⟨a, h⟩, rfl⟩, fun h => by
      obtain ⟨y, hy⟩ := h
      rw [← hy]
      exact y.2⟩) hf
  refine (ShortComplex.quasiIso_iff_of_zeros'
    (φ := (HomologicalComplex.shortComplexFunctor' (ModuleCat ℤ)
      (ComplexShape.down ℕ) 1 0 0).map
      (twoTermPiG f)) rfl rfl rfl).2 ?_
  exact ⟨ShortComplex.exact_of_g_is_cokernel (S := _) hc, Limits.epi_of_isColimit_cofork hc⟩

theorem quasiIsoAt_twoTermPiG_of_pos (i : ℕ) (hi : i ≠ 0) :
    QuasiIsoAt (twoTermPiG f) i := by
  rw [quasiIsoAt_iff_isIso_homologyMap]
  exact IsZero.isIso (twoTermComplexG_homology_pos_isZero f i hi)
    (TorFreeResolution.single₀_homology_pos_isZero (A := A) i hi) _

theorem quasiIso_twoTermPiG (hf : Function.Surjective f) : QuasiIso (twoTermPiG f) where
  quasiIsoAt := fun i => by
    rcases Nat.eq_zero_or_pos i with h | h
    · subst h
      exact quasiIsoAt_twoTermPiG_zero f hf
    · exact quasiIsoAt_twoTermPiG_of_pos f i h.ne'

/-- The two-term projective resolution of a free presentation with projective syzygy. -/
noncomputable def twoTermProjectiveResolutionG (hf : Function.Surjective f)
    [Module.Free ℤ F₀] [Projective (kerOf f)] :
    ProjectiveResolution (ModuleCat.of ℤ A) where
  complex := twoTermComplexG f
  projective := twoTermComplexG_projective f
  π := twoTermPiG f
  quasiIso := quasiIso_twoTermPiG f hf

/-! ### The master isomorphism: `Tor₁` as a right-tensored kernel -/

/-- **`Tor₁(A, B)` is the kernel of the right-tensored syzygy inclusion**, for a surjection
`f : F₀ →ₗ A` with `F₀` free and the syzygy projective: the two-term bridge
`TorBridge.torOneIsoTorKernel` at the generalized resolution.  The kernel is carried as the
categorical kernel of `TorBridge.diffRight`, whose underlying linear map is
`(kerSubtypeHom f).hom.rTensor ↥B` up to a definitional unfold; the further identification with
the linear-map kernel `↥(LinearMap.ker ((kerSubtypeHom f).hom.rTensor ↥B))` through
`ModuleCat.kernelIsoKer` meets the tensor-carrier `toIntModule`-versus-`instModule` diamond
(the same family as the repaired `TorBridge.lean:343`) and is left at the categorical kernel,
which the element-level work below consumes through `ModuleCat.kernelIsoKer` at each use. -/
noncomputable def torOneIsoKerTensor (hf : Function.Surjective f)
    [Module.Free ℤ F₀] [Projective (kerOf f)] (B : ModuleCat ℤ) :
    TorBridge.torOne (ModuleCat.of ℤ A) B ≅
      Limits.kernel (TorBridge.diffRight (B := B) (twoTermProjectiveResolutionG f hf)) :=
  TorBridge.torOneIsoTorKernel (B := B)
    (twoTermProjectiveResolutionG f hf) (twoTermComplexG_isZero_X_two f)

end GeneralTwoTerm

section ModelPresentation

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The coordinatewise map on direct sums, built from a family of linear maps, as a
`mapRange` of the family.  Both linearity and the component law are immediate. -/
noncomputable def dfinsuppLift {β γ : ι → Type} [∀ i, AddCommGroup (β i)]
    [∀ i, AddCommGroup (γ i)] [∀ i, Module ℤ (β i)] [∀ i, Module ℤ (γ i)]
    (g : ∀ i, β i →ₗ[ℤ] γ i) : (⨁ i, β i) →ₗ[ℤ] (⨁ i, γ i) where
  toFun z := DFinsupp.mapRange (fun i => (g i : β i → γ i)) (fun i => map_zero (g i)) z
  map_add' x y :=
    DFinsupp.mapRange_add _ (fun i => map_zero (g i)) (fun i => map_add (g i)) x y
  map_smul' c x := by
    ext i
    have h1 : (c • x) i = c • (x i) := rfl
    have h2 : ∀ y : ⨁ i, γ i, (c • y) i = c • (y i) := fun y => rfl
    rw [DFinsupp.mapRange_apply, h1, map_zsmul, RingHom.id_apply, h2]
    rfl

omit [DecidableEq ι] in
/-- The component law of `dfinsuppLift`. -/
theorem dfinsuppLift_apply {β γ : ι → Type} [∀ i, AddCommGroup (β i)]
    [∀ i, AddCommGroup (γ i)] [∀ i, Module ℤ (β i)] [∀ i, Module ℤ (γ i)]
    (g : ∀ i, β i →ₗ[ℤ] γ i) (z : ⨁ i, β i) (i : ι) : (dfinsuppLift g z) i = g i (z i) := by
  show (DFinsupp.mapRange (fun i => (g i : β i → γ i)) (fun i => map_zero (g i)) z) i = _
  exact DFinsupp.mapRange_apply _ _ _ _

omit [DecidableEq ι] in
/-- The component law of the inverse direction of the `Fintype` equivalence, for
assembling a direct sum from a function. -/
theorem equivFunOnFintype_symm_apply' {β : ι → Type} [∀ i, Zero (β i)]
    (f : ∀ i, β i) (i : ι) : DFinsupp.equivFunOnFintype.symm f i = f i := by
  have h := congrFun (Equiv.apply_symm_apply DFinsupp.equivFunOnFintype f) i
  simpa using h

omit [DecidableEq ι] in
/-- The component law of the linear version's inverse direction. -/
theorem linearEquivFunOnFintype_symm_apply {β : ι → Type} [∀ i, AddCommMonoid (β i)]
    [∀ i, Module ℤ (β i)] (f : ∀ i, β i) (i : ι) :
    (DFinsupp.linearEquivFunOnFintype (R := ℤ) (M := β)).symm f i = f i :=
  equivFunOnFintype_symm_apply' f i

omit [DecidableEq ι] in
/-- The composition law of `dfinsuppLift`. -/
theorem dfinsuppLift_comp {β γ δ : ι → Type} [∀ i, AddCommGroup (β i)]
    [∀ i, AddCommGroup (γ i)] [∀ i, AddCommGroup (δ i)] [∀ i, Module ℤ (β i)]
    [∀ i, Module ℤ (γ i)] [∀ i, Module ℤ (δ i)]
    (g₁ : ∀ i, β i →ₗ[ℤ] γ i) (g₂ : ∀ i, γ i →ₗ[ℤ] δ i) :
    (dfinsuppLift g₂).comp (dfinsuppLift g₁) = dfinsuppLift fun i => (g₂ i).comp (g₁ i) := by
  ext z i
  simp [dfinsuppLift_apply]

variable (n : ℕ) (p : ι → ℕ) (e : ι → ℕ)

/-- The model group the structure theorem produces. -/
abbrev modelGroup (n : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (p e : ι → ℕ) : Type :=
  (Fin n →₀ ℤ) × (⨁ i, ZMod (p i ^ e i))

/-- The free middle term of the model presentation. -/
abbrev modelFree (n : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] : Type :=
  (Fin n →₀ ℤ) × (⨁ i : ι, ℤ)

/-- The canonical map `ℤ → ZMod m`. -/
def intToZMod (m : ℕ) : ℤ →ₗ[ℤ] ZMod m where
  toFun x := (x : ZMod m)
  map_add' x y := by push_cast; ring
  map_smul' c x := by
    show ((c * x : ℤ) : ZMod m) = c • ((x : ZMod m))
    push_cast
    simp

/-- The surjection of the model presentation: the identity on the free part, the canonical
maps `ℤ → ZMod (p i ^ e i)` coordinatewise on the cyclic part. -/
noncomputable def modelPresentation : modelFree n ι →ₗ[ℤ] modelGroup n ι p e :=
  LinearMap.prodMap LinearMap.id (dfinsuppLift fun i => intToZMod (p i ^ e i))

/-- The relation map of the model presentation: multiplication by `p i ^ e i`,
coordinatewise, into the cyclic part of the middle term. -/
noncomputable def modelRel : (⨁ i : ι, ℤ) →ₗ[ℤ] modelFree n ι :=
  LinearMap.prod 0 (dfinsuppLift fun i => TorReductions.mulByInt ((p i ^ e i : ℕ)))

/-- The relation map lands in the kernel of the presentation. -/
theorem modelPresentation_modelRel (z : ⨁ i : ι, ℤ) :
    modelPresentation n p e (modelRel n p e z) = 0 := by
  apply Prod.ext
  · rfl
  · ext i
    have hmem : ((p i ^ e i : ℕ) : ℤ) ∣ (p i ^ e i : ℕ) * (z i) := dvd_mul_right _ _
    rw [modelPresentation, LinearMap.prodMap_apply, modelRel, LinearMap.prod_apply,
      dfinsuppLift_apply]
    change (((p i ^ e i : ℕ) * z i : ℤ) : ZMod (p i ^ e i)) = 0
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact hmem

/-- An element of the kernel of the presentation has all its cyclic coordinates divisible by
`p i ^ e i`, so it is the image of an explicit relation vector. -/
theorem exists_modelRel_of_mem_ker (y : modelFree n ι)
    (hy : modelPresentation n p e y = 0) :
    ∃ w : ⨁ i : ι, ℤ, modelRel n p e w = y := by
  obtain ⟨v, z, rfl⟩ : ∃ (v : Fin n →₀ ℤ) (z : ⨁ i : ι, ℤ), (v, z) = y := ⟨y.1, y.2, rfl⟩
  have hv : v = 0 := by
    have h := congrArg (fun g : modelGroup n ι p e => g.1) hy
    simp only [modelPresentation, LinearMap.prodMap_apply, LinearMap.id_apply,
      Prod.fst_zero] at h
    exact h
  have hval : ∀ i, ((p i ^ e i : ℕ) : ℤ) ∣ z i := by
    intro i
    have h := DFinsupp.ext_iff.mp (congrArg (fun g : modelGroup n ι p e => g.2) hy) i
    have h' : ((z i : ℤ) : ZMod (p i ^ e i)) = 0 := h
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h'
    exact h'
  refine ⟨(DFinsupp.linearEquivFunOnFintype (R := ℤ)).symm
    fun i => z i / (p i ^ e i : ℕ), ?_⟩
  apply Prod.ext
  · show (0 : Fin n →₀ ℤ) = v
    exact hv.symm
  · show (dfinsuppLift (fun i => TorReductions.mulByInt ((p i ^ e i : ℕ)))
        ((DFinsupp.linearEquivFunOnFintype (R := ℤ)).symm
          fun i => z i / (p i ^ e i : ℕ))) = z
    ext i
    rw [dfinsuppLift_apply, linearEquivFunOnFintype_symm_apply,
      TorReductions.mulByInt_apply, Int.mul_ediv_cancel' (hval i)]

/-- The kernel of the presentation is exactly the range of the relation map. -/
theorem ker_modelPresentation_eq : LinearMap.ker (modelPresentation n p e) =
    LinearMap.range (modelRel n p e) := by
  apply le_antisymm
  · intro y hy
    exact exists_modelRel_of_mem_ker n p e y (LinearMap.mem_ker.mp hy)
  · rintro y ⟨z, rfl⟩
    exact LinearMap.mem_ker.mpr (modelPresentation_modelRel n p e z)

/-- The relation map is injective, since each `p i ^ e i` is a nonzero integer. -/
theorem modelRel_injective (hp : ∀ i, (p i).Prime) :
    Function.Injective (modelRel n p e) := by
  intro w₁ w₂ h
  have h' := (Prod.ext_iff.mp h).2
  simp only [modelRel, LinearMap.prod_apply, Function.prod_def] at h'
  ext i
  have hi := DFinsupp.ext_iff.mp h' i
  rw [dfinsuppLift_apply, dfinsuppLift_apply, TorReductions.mulByInt_apply,
    TorReductions.mulByInt_apply] at hi
  have hpos : ((p i ^ e i : ℕ) : ℤ) ≠ 0 := by
    exact_mod_cast pow_ne_zero _ (Nat.Prime.ne_zero (hp i))
  exact mul_left_cancel₀ hpos hi

/-- **The relation module of the model presentation is the direct sum again.** -/
noncomputable def modelRelEquiv (hp : ∀ i, (p i).Prime) :
    (⨁ i : ι, ℤ) ≃ₗ[ℤ] ↥(LinearMap.ker (modelPresentation n p e)) :=
  LinearEquiv.ofBijective
    ((modelRel n p e).codRestrict _ fun z =>
      LinearMap.mem_ker.mpr (modelPresentation_modelRel n p e z))
    ⟨fun x y h => modelRel_injective n p e hp (Subtype.ext_iff.mp h), by
      intro y
      obtain ⟨w, hw⟩ := exists_modelRel_of_mem_ker n p e y.1 (LinearMap.mem_ker.mp y.2)
      exact ⟨w, Subtype.ext hw⟩⟩

theorem modelRelEquiv_subtype (hp : ∀ i, (p i).Prime) (w : ⨁ i : ι, ℤ) :
    (LinearMap.ker (modelPresentation n p e)).subtype (modelRelEquiv n p e hp w) =
      modelRel n p e w :=
  rfl

/-- The relation module's carrier is free, being a direct sum of copies of `ℤ`. -/
theorem dfinsuppInt_free : Module.Free ℤ (⨁ i : ι, ℤ) :=
  Module.Free.of_basis
    (Finsupp.basisSingleOne.map (finsuppLequivDFinsupp (R := ℤ) (M := ℤ)))

/-- The model group's middle term is free: a product of free modules. -/
theorem modelFree_free : Module.Free ℤ (modelFree n ι) := by
  haveI := dfinsuppInt_free (ι := ι)
  infer_instance

/-- The relation module of the model presentation, as an object of `ModuleCat`, is projective:
it is isomorphic to the free `⨁ i, ℤ` through `modelRelEquiv`. -/
theorem kerOf_model_projective (hp : ∀ i, (p i).Prime) :
    CategoryTheory.Projective (kerOf (modelPresentation n p e)) := by
  have h : ModuleCat.of ℤ (⨁ i : ι, ℤ) ≅ kerOf (modelPresentation n p e) :=
    ((TorArbitrary.addEquivIntLinearEquiv (modelRelEquiv n p e hp).toAddEquiv
      (_i := inferInstance) (_j := AddCommGroup.toIntModule ↥(LinearMap.ker
        (modelPresentation n p e))))).toModuleIso
  haveI := dfinsuppInt_free (ι := ι)
  haveI : Module.Projective ℤ (⨁ i : ι, ℤ) := Module.Projective.of_free
  exact CategoryTheory.Projective.of_iso h inferInstance

/-- The model presentation is surjective: the identity covers the free part and the
canonical maps cover each cyclic coordinate. -/
theorem modelPresentation_surjective (hp : ∀ i, (p i).Prime) :
    Function.Surjective (modelPresentation n p e) := by
  rintro ⟨v, w⟩
  refine ⟨(v, (DFinsupp.linearEquivFunOnFintype (R := ℤ)).symm
    fun i => ((w i : ZMod (p i ^ e i)).val : ℤ)), ?_⟩
  apply Prod.ext
  · rfl
  · ext i
    have hne : NeZero (p i ^ e i) := ⟨pow_ne_zero _ (Nat.Prime.ne_zero (hp i))⟩
    show (intToZMod (p i ^ e i))
        (((DFinsupp.linearEquivFunOnFintype (R := ℤ)).symm
          fun j => ((w j : ZMod (p j ^ e j)).val : ℤ)) i) = w i
    rw [linearEquivFunOnFintype_symm_apply]
    show (((w i : ZMod (p i ^ e i)).val : ℤ) : ZMod (p i ^ e i)) = w i
    push_cast
    exact ZMod.natCast_zmod_val _

end ModelPresentation



/-! ## Hatcher §3.A Exercise 6, first statement (#154): `Tor₁(A, B)` is torsion

For all abelian groups `A` and `B`, every element of `Tor₁(A, B)` is killed by some positive
integer.  The proof is the four steps below, assembled in `isAddTorsion_torOne`.

* Step 1 (`torOne_exists_torKernel`) presents `Tor₁(A, B)` at a free presentation of `A`
  through the committed dimension-shift bridge `TorArbitrary.torOneIsoKerIncl`, the tensor
  symmetry (`LinearMap.rTensor_comm`) and Mathlib's `ModuleCat.kernelIsoKer`: every element
  of `Tor₁` is carried by an injective additive map to an element of the kernel of the
  right-tensored syzygy inclusion `(ker π) ⊗ B → F ⊗ B`.
* Step 2 (`exists_fg_stage`) is the stage descent of the proof of Hatcher Proposition 3A.5 (3)
  (printed p. 265, `.tmp-sources/hatcher-2002-algebraic-topology.md` line 5662): the element
  already lies at a finitely generated stage whose middle term is a finitely generated
  submodule of the free middle term `F`.
* Step 3 (`exists_nsmul_eq_zero_of_stage`) is the finitely generated case: Smith normal form
  (`Submodule.smithNormalForm`) puts the stage's relation submodule into diagonal form
  inside the finitely generated coordinate summand containing it, and the diagonal entries
  define a division map `ν` with `ν ∘ inclusion = (∏ |d i|) · id`; tensoring `ν` with `B`
  then kills every element of the kernel by that product.
* Step 4 (`nsmul_eq_zero_of_nsmul_map_eq_zero`) transports the killing integer back along the
  injective additive map of Step 1.

The instance discipline: Step 1 produces elements of
`TensorProduct ℤ ↥(ker π) B` at the module structures the committed bridge carries; the
step lemmas therefore take their `Module ℤ` structures as explicit binders instead of
assuming the `AddCommGroup`-synthesized ones, so that no instance is synthesized at an
application site.
-/

section Hatcher3A6Torsion

/-- **Step 4 (transport).**  An injective additive map reflects being killed by `N`. -/
theorem nsmul_eq_zero_of_nsmul_map_eq_zero {M N1 : Type*} [AddCommGroup M] [AddCommGroup N1]
    (f : N1 →+ M) (hf : Function.Injective f) (N : ℕ) (x : N1) (h : N • f x = 0) :
    N • x = 0 := by
  refine hf ?_
  rw [map_nsmul f N x, h, map_zero]

/-- **Step 1 as a bijection.**  For a surjection `π : F →ₗ A` from a free module, `Tor1(A, B)` is
in bijection with the kernel of the right-tensored syzygy inclusion: the injective map of
`torOne_exists_torKernel`, now with the reverse chain of isomorphisms supplied, so that orders
transfer in both directions and an element of the kernel is the image of an element of `Tor1`. -/
noncomputable def torOneTorKernelAddEquiv {F A : Type} [AddCommGroup F] [AddCommGroup A]
    [Module.Free ℤ F] (π : F →ₗ[ℤ] A)
    (hπ : Function.Surjective π) (B : Type) [AddCommGroup B] :
    ↥(TorBridge.torOne (ModuleCat.of ℤ A) (ModuleCat.of ℤ B)) ≃+
      ↥(LinearMap.ker (((LinearMap.ker π).subtype).rTensor B)) := by
  classical
  haveI : Epi (ModuleCat.ofHom π) := (ModuleCat.epi_iff_surjective _).mpr hπ
  haveI : CategoryTheory.Projective (ModuleCat.of ℤ F) := inferInstance
  -- the composite element chain: torOne -> kerIncl -> functor-mapped kernelIsoKer -> comm
  set Bm := ModuleCat.of ℤ B with hBm
  set ι := (ModuleCat.kernelIsoKer (ModuleCat.ofHom π)).hom with hi
  set w : ↥(TorBridge.torOne (ModuleCat.of ℤ A) Bm) →
      TensorProduct ℤ ↥(LinearMap.ker π) B :=
    fun x => (TensorProduct.comm ℤ ↥Bm ↥(LinearMap.ker (ModuleCat.ofHom π).hom))
      (((tensorLeft Bm).map ι).hom
        ((TorArbitrary.torOneIsoKerIncl (ModuleCat.ofHom π) Bm).hom.hom x).1) with hw
  -- **the kernel condition**: functoriality of `tensorLeft` past
  -- `kernelIsoKer_hom_ker_subtype` turns the right-tensored syzygy inclusion into the
  -- tensored kernel inclusion, which kills the element by its `kerIncl` membership
  have hker : ∀ x : ↥(TorBridge.torOne (ModuleCat.of ℤ A) Bm),
      (((LinearMap.ker π).subtype).rTensor B) (w x) = 0 := by
    intro x
    simp only [hw]
    set u := (TorArbitrary.torOneIsoKerIncl (ModuleCat.ofHom π) Bm).hom.hom x with hu
    set v := ((tensorLeft Bm).map ι).hom u.1 with hv
    have hfun : (tensorLeft Bm).map ι ≫ (tensorLeft Bm).map (ModuleCat.ofHom
        ((LinearMap.ker (ModuleCat.ofHom π).hom).subtype)) =
        (tensorLeft Bm).map (Limits.kernel.ι (ModuleCat.ofHom π)) := by
      rw [hi, ← CategoryTheory.Functor.map_comp,
        ModuleCat.kernelIsoKer_hom_ker_subtype (ModuleCat.ofHom π)]
    have hzero : ((tensorLeft Bm).map (ModuleCat.ofHom
        ((LinearMap.ker (ModuleCat.ofHom π).hom).subtype))).hom v = 0 := by
      have h2 : ((tensorLeft Bm).map ι ≫ (tensorLeft Bm).map (ModuleCat.ofHom
          ((LinearMap.ker (ModuleCat.ofHom π).hom).subtype))).hom u.1 = 0 := by
        rw [hfun]
        exact LinearMap.mem_ker.mp u.2
      exact h2
    have hc := LinearMap.rTensor_comm
      ((LinearMap.ker (ModuleCat.ofHom π).hom).subtype) v
    have hfinal : (TensorProduct.comm ℤ ↥Bm F)
        (LinearMap.lTensor ↥Bm ((LinearMap.ker (ModuleCat.ofHom π).hom).subtype) v) = 0 := by
      have h3 : LinearMap.lTensor ↥Bm ((LinearMap.ker (ModuleCat.ofHom π).hom).subtype) v = 0 :=
        hzero
      rw [h3]
      exact LinearEquiv.map_zero _
    exact hc.trans hfinal
  -- **additivity and zero**: every layer of the chain is additive
  have hw0 : w 0 = 0 := by
    simp only [hw, map_zero, Submodule.coe_zero]
  have hwa : ∀ x y : ↥(TorBridge.torOne (ModuleCat.of ℤ A) Bm),
      w (x + y) = w x + w y := by
    intro x y
    simp only [hw, map_add, Submodule.coe_add]
  -- **injectivity**: the functor-mapped kernel isomorphism and the bridge isomorphism
  -- have left inverses; the tensor symmetry is injective
  have hinvL : ∀ z, ((tensorLeft Bm).map
      (ModuleCat.kernelIsoKer (ModuleCat.ofHom π)).inv).hom
      (((tensorLeft Bm).map ι).hom z) = z := by
    have h : (tensorLeft Bm).map ι ≫ (tensorLeft Bm).map
        (ModuleCat.kernelIsoKer (ModuleCat.ofHom π)).inv = 𝟙 _ := by
      rw [hi, ← CategoryTheory.Functor.map_comp, CategoryTheory.Iso.hom_inv_id,
        CategoryTheory.Functor.map_id]
    intro z
    exact DFunLike.congr_fun (congrArg (fun m => m.hom) h) z
  have hinvE : Function.LeftInverse
      ((TorArbitrary.torOneIsoKerIncl (ModuleCat.ofHom π) Bm).inv.hom)
      ((TorArbitrary.torOneIsoKerIncl (ModuleCat.ofHom π) Bm).hom.hom) := by
    intro z
    exact DFunLike.congr_fun (congrArg (fun m => m.hom)
      (CategoryTheory.Iso.hom_inv_id (TorArbitrary.torOneIsoKerIncl (ModuleCat.ofHom π) Bm))) z
  have hinj : Function.Injective fun x : ↥(TorBridge.torOne (ModuleCat.of ℤ A) Bm) =>
      (⟨w x, hker x⟩ : ↥(LinearMap.ker (((LinearMap.ker π).subtype).rTensor B))) := by
    intro x x' hxx
    have hwx : w x = w x' := congrArg Subtype.val hxx
    have h1 : ((tensorLeft Bm).map ι).hom
        ((TorArbitrary.torOneIsoKerIncl (ModuleCat.ofHom π) Bm).hom.hom x).1 =
        ((tensorLeft Bm).map ι).hom
        ((TorArbitrary.torOneIsoKerIncl (ModuleCat.ofHom π) Bm).hom.hom x').1 := by
      have h2 := congrArg (⇑(TensorProduct.comm ℤ ↥Bm
        ↥(LinearMap.ker (ModuleCat.ofHom π).hom)).symm) hwx
      simp only [hw] at h2
      simpa using h2
    have h3 : ((TorArbitrary.torOneIsoKerIncl (ModuleCat.ofHom π) Bm).hom.hom x).1 =
        ((TorArbitrary.torOneIsoKerIncl (ModuleCat.ofHom π) Bm).hom.hom x').1 := by
      have h4 := congrArg (((tensorLeft Bm).map
        (ModuleCat.kernelIsoKer (ModuleCat.ofHom π)).inv).hom) h1
      simp only [hinvL] at h4
      exact h4
    exact hinvE.injective (Subtype.ext h3)


  -- **surjectivity**: the reverse chain of isomorphisms
  have hinvL' : ∀ z, ((tensorLeft Bm).map ι).hom
      (((tensorLeft Bm).map (ModuleCat.kernelIsoKer (ModuleCat.ofHom π)).inv).hom z) = z := by
    have h : (tensorLeft Bm).map (ModuleCat.kernelIsoKer (ModuleCat.ofHom π)).inv ≫
        (tensorLeft Bm).map ι = 𝟙 _ := by
      rw [hi, ← CategoryTheory.Functor.map_comp, CategoryTheory.Iso.inv_hom_id,
        CategoryTheory.Functor.map_id]
    intro z
    exact DFunLike.congr_fun (congrArg (fun m => m.hom) h) z
  have hinvE'' : ∀ z : ↥(TorArbitrary.kerIncl (ModuleCat.ofHom π) Bm),
      ((TorArbitrary.torOneIsoKerIncl (ModuleCat.ofHom π) Bm).hom.hom
        ((TorArbitrary.torOneIsoKerIncl (ModuleCat.ofHom π) Bm).inv.hom z)).1 = z.1 := by
    intro z
    exact congrArg Subtype.val (DFunLike.congr_fun (congrArg (fun m => m.hom)
      (CategoryTheory.Iso.inv_hom_id (TorArbitrary.torOneIsoKerIncl (ModuleCat.ofHom π) Bm))) z)
  have hfun' : (tensorLeft Bm).map ι ≫ (tensorLeft Bm).map (ModuleCat.ofHom
      ((LinearMap.ker (ModuleCat.ofHom π).hom).subtype)) =
      (tensorLeft Bm).map (Limits.kernel.ι (ModuleCat.ofHom π)) := by
    rw [hi, ← CategoryTheory.Functor.map_comp,
      ModuleCat.kernelIsoKer_hom_ker_subtype (ModuleCat.ofHom π)]
  have hsurj : Function.Surjective fun x : ↥(TorBridge.torOne (ModuleCat.of ℤ A) Bm) =>
      (⟨w x, hker x⟩ : ↥(LinearMap.ker (((LinearMap.ker π).subtype).rTensor B))) := by
    intro e
    set y := (TensorProduct.comm ℤ ↥Bm
      ↥(LinearMap.ker (ModuleCat.ofHom π).hom)).symm e.1 with hydef
    have hyl : LinearMap.lTensor ↥Bm
        ((LinearMap.ker (ModuleCat.ofHom π).hom).subtype) y = 0 := by
      have hc := LinearMap.rTensor_comm ((LinearMap.ker (ModuleCat.ofHom π).hom).subtype) y
      rw [hydef, LinearEquiv.apply_symm_apply] at hc
      have he : (LinearMap.rTensor ↥Bm
          ((LinearMap.ker (ModuleCat.ofHom π).hom).subtype)) e.1 = 0 :=
        LinearMap.mem_ker.mp e.2
      rw [he] at hc
      exact (TensorProduct.comm ℤ ↥Bm F).injective hc.symm
    have hmem : ((tensorLeft Bm).map (Limits.kernel.ι (ModuleCat.ofHom π))).hom
        (((tensorLeft Bm).map (ModuleCat.kernelIsoKer (ModuleCat.ofHom π)).inv).hom y) = 0 := by
      rw [← hfun']
      show ((tensorLeft Bm).map (ModuleCat.ofHom
        ((LinearMap.ker (ModuleCat.ofHom π).hom).subtype))).hom
        (((tensorLeft Bm).map ι).hom
          (((tensorLeft Bm).map (ModuleCat.kernelIsoKer (ModuleCat.ofHom π)).inv).hom y)) = 0
      rw [hinvL', TorArbitrary.hom_lTensor]
      exact hyl
    refine ⟨(TorArbitrary.torOneIsoKerIncl (ModuleCat.ofHom π) Bm).inv.hom ⟨_, hmem⟩, ?_⟩
    refine Subtype.ext ?_
    simp only [hw, Subtype.coe_mk]
    rw [hinvE'', hinvL', hydef, LinearEquiv.apply_symm_apply]
  refine AddEquiv.ofBijective
    ({ toFun := fun x => ⟨w x, hker x⟩
       map_zero' := Subtype.ext hw0
       map_add' := fun x y => Subtype.ext (hwa x y) } :
      ↥(TorBridge.torOne (ModuleCat.of ℤ A) Bm) →+
        ↥(LinearMap.ker (((LinearMap.ker π).subtype).rTensor B))) ?_
  exact ⟨hinj, hsurj⟩

/-- **Step 1 (the presentation bridge).**  For a surjection `π : F →ₗ A` from a free module,
every element of `Tor1(A, B)` is carried by an injective additive map into the kernel of the
right-tensored syzygy inclusion `(ker π) ⊗ B → F ⊗ B`: the additive form of
`torOneTorKernelAddEquiv`. -/
theorem torOne_exists_torKernel {F A : Type} [AddCommGroup F] [AddCommGroup A]
    [Module.Free ℤ F] (π : F →ₗ[ℤ] A)
    (hπ : Function.Surjective π) (B : Type) [AddCommGroup B] :
    ∃ (φ : ↥(TorBridge.torOne (ModuleCat.of ℤ A) (ModuleCat.of ℤ B)) →+
        ↥(LinearMap.ker (((LinearMap.ker π).subtype).rTensor B))),
      Function.Injective φ := by
  refine ⟨{ toFun := (torOneTorKernelAddEquiv (B := B) π hπ).toFun
            map_zero' := (torOneTorKernelAddEquiv (B := B) π hπ).map_zero
            map_add' := fun x y => (torOneTorKernelAddEquiv (B := B) π hπ).map_add x y }, ?_⟩
  exact (torOneTorKernelAddEquiv (B := B) π hπ).injective

/-- **Step 2 (the stage descent).**  For an injective relation map `i : K →ₗ F` into a free
module with basis `b`, every element of `ker (i ⊗ B)` comes from an element of the kernel of
`(range i ⊓ F') ⊗ B → F' ⊗ B` for a finitely generated submodule `F'` of `F`: the element
already lies at a finitely generated stage. -/
theorem exists_fg_stage {F K B : Type} [AddCommGroup F] [AddCommGroup K] [AddCommGroup B]
    {ι : Type*} (b : Module.Basis ι ℤ F)
    (i : K →ₗ[ℤ] F) (hi : Function.Injective i)
    {w : TensorProduct ℤ K B} (hw : (i.rTensor B) w = 0) :
    ∃ (F' : Submodule ℤ F) (_ : F'.FG)
      (t : ↥(LinearMap.ker (((LinearMap.range i ⊓ F').subtype).rTensor B))),
      (((LinearEquiv.ofInjective i hi).symm.toLinearMap.comp
        (Submodule.inclusion inf_le_left)).rTensor B) t.1 = w := by
  classical
  obtain ⟨F', hF', ρ, hρ, t₀, hta, htb⟩ :=
    TorStages.exists_stage_of_free (K := K) b i hw
  -- the repackage map: `comap i F' → range i ⊓ F'`, `k ↦ i k`
  set g : ↥(Submodule.comap i F') →ₗ[ℤ] ↥(LinearMap.range i ⊓ F') :=
    LinearMap.codRestrict (LinearMap.range i ⊓ F') (i.comp (Submodule.comap i F').subtype)
      (fun k => Submodule.mem_inf.mpr ⟨⟨k.1, rfl⟩, k.2⟩) with hg
  -- it commutes with the submodules' inclusions into `F`
  have hsub : ((LinearMap.range i ⊓ F').subtype).comp g
      = i.comp (Submodule.comap i F').subtype := by
    ext k
    rfl
  -- and the stage inclusion followed by the range splitting is the identity on `comap i F'`
  have hge : ((LinearEquiv.ofInjective i hi).symm.toLinearMap.comp
      (Submodule.inclusion inf_le_left)).comp g
      = (Submodule.comap i F').subtype := by
    ext k
    simp only [LinearMap.comp_apply]
    have h1 : (Submodule.inclusion inf_le_left) (g k)
        = (LinearEquiv.ofInjective i hi) k.1 := by
      apply Subtype.ext
      rfl
    rw [h1]
    exact LinearEquiv.symm_apply_apply _ _
  refine ⟨F', hF', ⟨(LinearMap.rTensor B g) t₀, ?_⟩, ?_⟩
  · refine LinearMap.mem_ker.mpr ?_
    have hcomp : (LinearMap.rTensor B ((LinearMap.range i ⊓ F').subtype)).comp
        (LinearMap.rTensor B g)
        = (LinearMap.rTensor B i).comp
          (LinearMap.rTensor B (Submodule.comap i F').subtype) := by
      rw [← LinearMap.rTensor_comp, ← LinearMap.rTensor_comp, hsub]
    rw [← LinearMap.comp_apply, hcomp, LinearMap.comp_apply, hta, hw]
  · have hcomp2 : (LinearMap.rTensor B ((LinearEquiv.ofInjective i hi).symm.toLinearMap.comp
        (Submodule.inclusion inf_le_left))).comp (LinearMap.rTensor B g)
        = LinearMap.rTensor B (Submodule.comap i F').subtype := by
      rw [← LinearMap.rTensor_comp, hge]
    rw [← LinearMap.comp_apply, hcomp2]
    exact hta

/-- **Step 3 (the finitely generated stage).**  For a finitely generated submodule `F'` of a
free module with basis `b` and any relation submodule `R`, every element of
`ker ((R ⊓ F') ⊗ B → F ⊗ B)` is killed by a positive integer.  Smith normal form
(`Submodule.smithNormalForm`) puts `R ⊓ F'` into diagonal form `g i = d i • e (f i)` inside
the finitely generated coordinate summand `F₀ ⊇ F'`; the diagonal entries define a division
map `ν : F₀ →ₗ R ⊓ F'` with `ν ∘ incl = ∏ |d i| · id` (send `e (f i)` to
`(N / d i) • g i` and the other basis vectors to `0`).  Tensoring `ν ∘ (R ⊓ F').subtype`
with `B` then exhibits `N • t` as the image of `0`, so `N` kills the element; extending `ν`
along the coordinate retraction `F → F₀` needs no injectivity of any tensored inclusion. -/

theorem exists_nsmul_eq_zero_of_stage {F B : Type} [AddCommGroup F] [AddCommGroup B]
    {ι : Type*} (b : Module.Basis ι ℤ F)
    (F' R : Submodule ℤ F) (hF'fg : F'.FG)
    (t : ↥(LinearMap.ker (((R ⊓ F').subtype).rTensor B))) :
    ∃ N : ℕ, 0 < N ∧ (N : ℤ) • t = 0 := by
  classical
  -- **the stage**: `F'` lies in the span of finitely many basis vectors, a direct summand
  obtain ⟨S, hSfin, hSspan⟩ := Submodule.fg_def.mp hF'fg
  set s : Finset ι := hSfin.toFinset.biUnion fun x => (b.repr x).support with hsdef
  set F₀ := TorStages.coordSpan b s with hF₀def
  have hF'le : F' ≤ F₀ := by
    rw [← hSspan, Submodule.span_le]
    rintro x hx
    have hsupp : (b.repr x).support ⊆ s := fun i hi =>
      Finset.mem_biUnion.mpr ⟨x, hSfin.mem_toFinset.mpr hx, hi⟩
    rw [← Module.Basis.linearCombination_repr b x, Finsupp.linearCombination_apply,
      Finsupp.sum]
    refine Submodule.sum_mem _ fun i hi => Submodule.smul_mem _ _ ?_
    exact Submodule.subset_span ⟨i, Finset.mem_coe.mpr (hsupp hi), rfl⟩
  have hP : R ⊓ F' ≤ F₀ := inf_le_right.trans hF'le
  -- **the finite basis of `F₀`**, from the linear independence of the basis vectors in `s`
  have hli : LinearIndependent ℤ (fun i : (s : Set ι) => b i.val) :=
    b.linearIndependent.comp Subtype.val Subtype.val_injective
  have he : Submodule.span ℤ (Set.range fun i : (s : Set ι) => b i.val) = F₀ :=
    congrArg (fun T => Submodule.span ℤ T) (Set.image_eq_range b (s : Set ι)).symm
  have hmem : ∀ x : ↥(Submodule.span ℤ (Set.range fun i : (s : Set ι) => b i.val)),
      (Submodule.span ℤ (Set.range fun i : (s : Set ι) => b i.val)).subtype x ∈ F₀ := by
    intro x
    rw [← he]
    exact x.2
  set hfwd := (Submodule.span ℤ (Set.range fun i : (s : Set ι) => b i.val)).subtype.codRestrict
    F₀ hmem with hhfwd
  have ε₀ : ↥(Submodule.span ℤ (Set.range fun i : (s : Set ι) => b i.val)) ≃ₗ[ℤ] ↥F₀ :=
    LinearEquiv.ofBijective hfwd
      ⟨fun x y hxy => Subtype.ext
          (show x.val = y.val from congrArg (fun z : ↥F₀ => (z : F)) hxy),
        fun y => ⟨⟨y.1, by rw [he]; exact y.2⟩, Subtype.ext rfl⟩⟩
  set bF₀ := (Module.Basis.span hli).map ε₀ with hbF₀
  -- **Smith normal form** of `R ⊓ F'` inside `F₀`
  obtain ⟨n, snf⟩ :=
    (Submodule.comap F₀.subtype (R ⊓ F')).smithNormalForm bF₀
  obtain ⟨bQ, bN₀, f, a, hdiag⟩ := snf
  set ε := Submodule.comapSubtypeEquivOfLe hP with hε
  set bP := bN₀.map ε with hbP
  have hεcoe : ∀ y : ↥(Submodule.comap F₀.subtype (R ⊓ F')),
      Submodule.inclusion hP (ε y) = (y : ↥F₀) := fun y => Subtype.ext rfl
  have hdiag' : ∀ i : Fin n, Submodule.inclusion hP (bP i) = a i • bQ (f i) := by
    intro i
    rw [hbP, Module.Basis.map_apply, hεcoe]
    exact hdiag i
  -- **the diagonal entries are nonzero**, so `N := ∏ |a i|` is positive and divisible
  have hane : ∀ i : Fin n, a i ≠ 0 := by
    intro i h0
    have h1 : (bN₀ i : ↥F₀) = 0 := by rw [hdiag i, h0, zero_smul]
    exact bN₀.ne_zero i (Subtype.ext h1)
  set N : ℕ := ∏ i : Fin n, (a i).natAbs with hNdef
  have hNpos : 0 < N := Finset.prod_pos fun i _ => Int.natAbs_pos.mpr (hane i)
  have hdvd : ∀ i : Fin n, a i ∣ (N : ℤ) := by
    intro i
    have h1 : (a i).natAbs ∣ N := Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
    have h2 : (a i).natAbs ∣ (N : ℤ).natAbs := by rw [Int.natAbs_natCast]; exact h1
    exact Int.natAbs_dvd_natAbs.mp h2
  -- **the division map**: `ν₀ (e (f i)) = (N / a i) • g i`, zero on the other basis vectors
  set g : ↥(s : Set ι) → ↥(R ⊓ F') := fun j =>
    ∑ i : Fin n, if f i = j then ((N : ℤ) / a i) • bP i else 0 with hgdef
  have hgσ : ∀ i : Fin n, g (f i) = ((N : ℤ) / a i) • bP i := by
    intro i
    simp only [hgdef]
    rw [Finset.sum_eq_single i]
    · simp
    · intro i' _ hne
      have hf : ¬(f i' = f i) := fun hcon => hne (f.injective hcon)
      simp [hf]
    · intro hi
      exact (hi (Finset.mem_univ i)).elim
  set ν₀ := (bQ.constr ℤ) g with hν₀def
  have hν₀apply : ∀ j : ↥(s : Set ι), ν₀ (bQ j) = g j := by
    intro j
    rw [hν₀def]
    simp [Module.Basis.constr_apply_fintype]
  have hbPprop : ∀ i : Fin n, ν₀ (Submodule.inclusion hP (bP i)) = (N : ℤ) • bP i := by
    intro i
    rw [hdiag' i, map_smul, hν₀apply, hgσ, smul_smul, Int.mul_ediv_cancel' (hdvd i)]
  -- the division map is `N ·` on all of `R ⊓ F'`, by linearity from the basis `bP`
  have hprop : ∀ p : ↥(R ⊓ F'), ν₀ (Submodule.inclusion hP p) = (N : ℤ) • p := by
    intro p
    have hr : ∑ i : Fin n, (bP.repr p) i • bP i = p := bP.sum_repr p
    have hincl : Submodule.inclusion hP (∑ i : Fin n, (bP.repr p) i • bP i)
        = ∑ i : Fin n, (bP.repr p) i • Submodule.inclusion hP (bP i) := by
      simp only [map_sum, map_smul]
    have e1 : ν₀ (Submodule.inclusion hP p)
        = ∑ i : Fin n, (bP.repr p) i • ν₀ (Submodule.inclusion hP (bP i)) := by
      rw [show Submodule.inclusion hP p =
          Submodule.inclusion hP (∑ i : Fin n, (bP.repr p) i • bP i) from
          (congrArg (Submodule.inclusion hP) hr).symm, hincl]
      simp only [map_sum, map_smul]
    have hrhs : (N : ℤ) • ∑ i : Fin n, (bP.repr p) i • bP i
        = ∑ i : Fin n, (bP.repr p) i • ((N : ℤ) • bP i) := by
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [smul_smul, smul_smul, mul_comm]
    rw [e1]
    simp only [hbPprop]
    rw [← hrhs, hr]
  -- **extend along the coordinate retraction** `F → F₀`
  set ρ := TorStages.coordRetract b s with hρdef
  have hrid : ∀ x : ↥F₀, ρ (F₀.subtype x) = x := by
    intro x
    have h := DFunLike.congr_fun (TorStages.coordRetract_comp_subtype b s) x
    simpa using h
  set ν := ν₀.comp ρ with hνdef
  have hνprop : ∀ p : ↥(R ⊓ F'), ν ((R ⊓ F').subtype p) = (N : ℤ) • p := by
    intro p
    have h1 : (R ⊓ F').subtype p = F₀.subtype (Submodule.inclusion hP p) := rfl
    rw [hνdef, LinearMap.comp_apply, h1, hrid]
    exact hprop p
  -- **the kill**: `N • t` is `(ν ⊗ B)` applied to the image of `t`, which is `0`
  refine ⟨N, hNpos, Subtype.ext ?_⟩
  have hcomp : ν.comp (R ⊓ F').subtype
      = ((N : ℤ) • LinearMap.id : ↥(R ⊓ F') →ₗ[ℤ] ↥(R ⊓ F')) := by
    refine LinearMap.ext fun p => ?_
    rw [hνdef, LinearMap.comp_apply, hνprop, LinearMap.smul_apply, LinearMap.id_apply]
  calc (N : ℤ) • t.1
      = (LinearMap.rTensor B (((N : ℤ) • LinearMap.id :
          ↥(R ⊓ F') →ₗ[ℤ] ↥(R ⊓ F')))) t.1 := by
        rw [LinearMap.rTensor_smul, LinearMap.rTensor_id, LinearMap.smul_apply,
          LinearMap.id_apply]
    _ = (LinearMap.rTensor B (ν.comp (R ⊓ F').subtype)) t.1 := by rw [hcomp]
    _ = ((LinearMap.rTensor B ν).comp (LinearMap.rTensor B (R ⊓ F').subtype)) t.1 := by
        rw [LinearMap.rTensor_comp]
    _ = (LinearMap.rTensor B ν) ((LinearMap.rTensor B ((R ⊓ F').subtype)) t.1) :=
        LinearMap.comp_apply _ _ _
    _ = (LinearMap.rTensor B ν) 0 := by rw [LinearMap.mem_ker.mp t.2]
    _ = 0 := map_zero _

/-- The free abelian group on `A`, as a `ℤ`-module at the `AddCommGroup`-synthesized
structure, with its basis transported from the canonical Finsupp one along the committed
`addEquivIntLinearEquiv` identity bridge. -/
noncomputable def presBasis (A : Type) [AddCommGroup A] :
    @Module.Basis A ℤ (A →₀ ℤ) _ _ (AddCommGroup.toIntModule (A →₀ ℤ)) :=
  Finsupp.basisSingleOne.map
    (TorArbitrary.addEquivIntLinearEquiv (AddEquiv.refl (A →₀ ℤ))
      (_j := AddCommGroup.toIntModule (A →₀ ℤ)))

/-- The additive sum map underlying `pres`. -/
def presHom (A : Type) [AddCommGroup A] : (A →₀ ℤ) →+ A where
  toFun s := s.sum fun a n => n • a
  map_zero' := by simp
  map_add' s t := by
    classical
    exact Finsupp.sum_add_index (fun a _ => by simp) (fun a _ b c => by simp [add_zsmul])

/-- The canonical surjection from the free abelian group on `A`, both module structures
pinned to the `AddCommGroup`-synthesized ones, with ℤ-linearity by the `int_smul_eq_zsmul`
bridge. -/
def pres (A : Type) [AddCommGroup A] :
    @LinearMap ℤ ℤ _ _ (RingHom.id ℤ) (A →₀ ℤ) A _ _
      (AddCommGroup.toIntModule (A →₀ ℤ)) (AddCommGroup.toIntModule A) where
  toFun := presHom A
  map_add' s t := (presHom A).map_add' s t
  map_smul' c s := (presHom A).map_zsmul c s

theorem presHom_single (A : Type) [AddCommGroup A] (a : A) :
    presHom A (Finsupp.single a 1) = a := by
  show (Finsupp.single a 1).sum (fun a n => n • a) = a
  exact (Finsupp.sum_single_index (by simp)).trans (by simp)

theorem pres_surjective (A : Type) [AddCommGroup A] : Function.Surjective (pres A) :=
  fun a => ⟨Finsupp.single a 1, by
    show (Finsupp.single a 1).sum (fun a n => n • a) = a
    exact (Finsupp.sum_single_index (by simp)).trans (by simp)⟩

/-- **Hatcher, *Algebraic Topology* (2002), §3.A Exercise 6, printed p. 267, first statement
(#154).**  For all abelian groups `A` and `B`, `Tor1(A, B)` is a torsion group. -/
theorem isAddTorsion_torOne {A B : Type} [AddCommGroup A] [AddCommGroup B] :
    IsAddTorsion ↥(TorBridge.torOne (ModuleCat.of ℤ A) (ModuleCat.of ℤ B)) := by
  intro x
  haveI : @Module.Free ℤ (A →₀ ℤ) _ _ (AddCommGroup.toIntModule (A →₀ ℤ)) :=
    Module.Free.of_basis (presBasis A)
  obtain ⟨φ, hφinj⟩ := torOne_exists_torKernel (pres A) (pres_surjective A) B
  have hw : (((LinearMap.ker (pres A)).subtype).rTensor B) (φ x).1 = 0 :=
    LinearMap.mem_ker.mp (φ x).2
  obtain ⟨F', hF'fg, t, htim⟩ := exists_fg_stage (b := presBasis A)
    ((LinearMap.ker (pres A)).subtype) (fun a b h => Subtype.ext h) hw
  obtain ⟨N, hNpos, hNt⟩ := exists_nsmul_eq_zero_of_stage (b := presBasis A) F'
    (LinearMap.range ((LinearMap.ker (pres A)).subtype)) hF'fg t
  refine isOfFinAddOrder_iff_zsmul_eq_zero.mpr ⟨(N : ℤ), ?_, ?_⟩
  · exact_mod_cast hNpos.ne'
  -- Step 3's killing integer, transported through the stage map
  have h2 : (N : ℤ) • (φ x).1 = 0 := by
    have e1 : (((LinearEquiv.ofInjective ((LinearMap.ker (pres A)).subtype)
        (fun a b h => Subtype.ext h)).symm.toLinearMap.comp
        (Submodule.inclusion inf_le_left)).rTensor B)
        (((N : ℤ) • t : ↥(LinearMap.ker (((LinearMap.range
        ((LinearMap.ker (pres A)).subtype) ⊓ F').subtype).rTensor B))) : TensorProduct ℤ ↥(LinearMap.range
        ((LinearMap.ker (pres A)).subtype) ⊓ F') B) = 0 := by
      rw [hNt]
      simp
    rw [← htim, ← map_zsmul]
    exact e1
  have h3 : (N : ℤ) • φ x = 0 := by
    apply Subtype.ext
    show (N : ℤ) • (φ x).1 = _
    rw [h2]
    rfl
  -- and reflected by the injective bridge onto x
  refine hφinj ?_
  rw [map_zsmul φ, h3, map_zero]

/-! ## Hatcher §3.A Exercise 6, second statement (#155): elements of order `n`

`Tor1(A, B)` has an element of order `n` if and only if both `A` and `B` have one.  Both
directions reduce to prime powers `p ^ k` — the assembling direction by
`exists_addOrderOf_of_forall_prime_pow`, the extracting direction by
`exists_addOrderOf_of_dvd_addOrderOf`, as in the `PrimePow` section above — and the prime-power
core `torOne_prime_pow_iff` is proved by the two halves below.

* The `←` half (`exists_torOne_of_addOrderOf`) starts from `a : A` and `b : B` of order
  `p ^ k`: the syzygy element `z = p ^ k • Finsupp.single a 1` and the kernel element `z ⊗ b`
  (they lie in the tensored syzygy kernel by `kerTmul_mem_ker`).  `ℤ z` is *pure* in the
  syzygy, so the quotient is torsion-free, hence flat, and `ℤ z ⊗ B → ker (pres A) ⊗ B` is
  injective: `z ⊗ b` is nonzero of order exactly `p ^ k`, and the order transports to `Tor1`
  along the bijection `torOneTorKernelAddEquiv`.
* The `→` half (`exists_addOrderOf_of_torOne`) descends an element of `Tor1` to a finitely
  generated stage of the universal presentation (`TorStages.exists_stage_of_free`), puts the
  stage's relation map in Smith normal form, and reads the order off the coordinates: a
  coordinate of order `p ^ k` in `B`, and a diagonal entry divisible by `p ^ k`, which is an
  elementary divisor of the stage's group and so gives an element of order `p ^ k` in `A`.
-/

section Hatcher3A6Order

/-- **The lift's multiple lies in the kernel (#155, `←` half).**  If `n • a = 0` then
`n • Finsupp.single a 1` lies in `ker (pres A)`, since `pres` is linear and sends the
singleton to `a`. -/
theorem smul_single_mem_ker {A : Type} [AddCommGroup A] {n : ℤ} {a : A} (ha : n • a = 0) :
    n • Finsupp.single a 1 ∈ LinearMap.ker (pres A) := by
  rw [LinearMap.mem_ker, map_zsmul]
  show n • (presHom A) (Finsupp.single a 1) = 0
  rw [presHom_single]
  exact ha

/-- **The tensor kernel element (#155, `←` half).**  If `n • a = 0` and `n • b = 0` then
`(n • Finsupp.single a 1) ⊗ b` lies in the kernel of the right-tensed syzygy inclusion:
its image exchanges to `Finsupp.single a 1 ⊗ (n • b) = 0`. -/
theorem kerTmul_mem_ker {A B : Type} [AddCommGroup A] [AddCommGroup B] {n : ℤ}
    {a : A} (ha : n • a = 0) {b : B} (hb : n • b = 0) :
    ((⟨n • Finsupp.single a 1, smul_single_mem_ker ha⟩ :
        ↥(LinearMap.ker (pres A))) ⊗ₜ[ℤ] b)
      ∈ LinearMap.ker (((LinearMap.ker (pres A)).subtype).rTensor B) := by
  rw [LinearMap.mem_ker, LinearMap.rTensor_tmul]
  show (n • Finsupp.single a 1) ⊗ₜ[ℤ] b = 0
  rw [TensorProduct.smul_tmul, hb, TensorProduct.tmul_zero]

/-! ### The coordinate engine: `F ⊗ B ≃ (ι → B)` at a finite basis

Both halves of the order statement read a tensor element through the coordinates of a finite
basis.  `tensorPiEquiv` is that coordinate equivalence, `tensorPiEquiv_tmul` its value on a
simple tensor, and `tensorPiEquiv_rTensor_eq` the coordinate form of a relation map that is
diagonal in a pair of bases — the shape Smith normal form produces.  The rest of the section
turns that into the two statements the halves need: the kernel condition
(`rTensor_eq_zero_iff`), a killing integer (`natAbs_prod_smul_eq_zero`), and the extraction of
a coordinate of order `p ^ k` together with the diagonal entry divisible by it
(`exists_coord_of_prime_pow`). -/

section TensorPiEngine

variable {F B : Type*} [AddCommGroup F] [AddCommGroup B] {ι : Type*}

/-- **The coordinates of a tensor element** against a finite basis: `F ⊗ B ≅ (ι → B)`. -/
noncomputable def tensorPiEquiv [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℤ F) : TensorProduct ℤ F B ≃ₗ[ℤ] (ι → B) :=
  (TensorProduct.comm ℤ F B).trans
    ((LinearEquiv.lTensor B b.equivFun).trans (TensorProduct.piScalarRight ℤ ℤ B ι))

/-- The coordinate of a simple tensor is the coordinate of the basis vector times the element. -/
theorem tensorPiEquiv_tmul [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℤ F)
    (f : F) (x : B) (i : ι) :
    (tensorPiEquiv (B := B) b) (f ⊗ₜ[ℤ] x) i = b.repr f i • x := by
  show (TensorProduct.comm ℤ F B).trans ((LinearEquiv.lTensor B b.equivFun).trans
      (TensorProduct.piScalarRight ℤ ℤ B ι)) (f ⊗ₜ[ℤ] x) i = b.repr f i • x
  simp [LinearEquiv.trans_apply, Module.Basis.equivFun_apply]

variable {K : Type*} [AddCommGroup K] {n : ℕ} {κ : Type*}

/-- The coordinates of `i x` in the diagonal basis, as a `Finsupp`. -/
theorem basis_repr_comp_eq_sum (bK : Module.Basis (Fin n) ℤ K) (bF : Module.Basis κ ℤ F)
    (i : K →ₗ[ℤ] F) (g : Fin n → κ) (a : Fin n → ℤ)
    (hi : ∀ k, i (bK k) = a k • bF (g k)) (x : K) :
    bF.repr (i x) = ∑ k : Fin n, Finsupp.single (g k) ((bK.repr x) k * a k) := by
  have hx : x = ∑ k : Fin n, (bK.repr x) k • bK k := (bK.sum_repr x).symm
  conv_lhs => rw [hx]
  rw [map_sum, map_sum]
  exact Finset.sum_congr rfl fun k _ => by
    rw [map_smul, hi, map_smul, map_smul, Module.Basis.repr_self,
      Finsupp.smul_single', mul_one, Finsupp.smul_single']

variable [Fintype κ] [DecidableEq κ]

/-- **The coordinate form of a diagonal relation map.**  If the relation map is diagonal with
entries `a` against the bases `bK` and `bF`, then the coordinates of its tensor are the diagonal
entries times the coordinates of the element, summed over the image of the embedding. -/
theorem tensorPiEquiv_rTensor_eq (bK : Module.Basis (Fin n) ℤ K) (bF : Module.Basis κ ℤ F)
    (i : K →ₗ[ℤ] F) (g : Fin n → κ) (a : Fin n → ℤ)
    (hi : ∀ k, i (bK k) = a k • bF (g k)) (t : TensorProduct ℤ K B) :
    (tensorPiEquiv (B := B) bF) (i.rTensor B t) =
      fun j => ∑ k : Fin n, if g k = j then a k • ((tensorPiEquiv (B := B) bK) t k) else 0 := by
  classical
  have key : ∀ x : K, ∀ y : B,
      (tensorPiEquiv (B := B) bF) (i.rTensor B (x ⊗ₜ[ℤ] y)) =
        fun j => ∑ k : Fin n,
          if g k = j then a k • ((tensorPiEquiv (B := B) bK) (x ⊗ₜ[ℤ] y) k) else 0 := by
    intro x y
    rw [LinearMap.rTensor_tmul]
    funext j
    rw [tensorPiEquiv_tmul]
    have hval : bF.repr (i x) j = ∑ k : Fin n,
        if g k = j then (bK.repr x) k * a k else 0 := by
      rw [basis_repr_comp_eq_sum bK bF i g a hi x, Finset.sum_apply']
      exact Finset.sum_congr rfl fun k _ => by rw [Finsupp.single_apply]
    rw [hval, Finset.sum_smul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [tensorPiEquiv_tmul]
    by_cases h : g k = j
    · rw [if_pos h, if_pos h, mul_comm, smul_smul]
    · rw [if_neg h, if_neg h, zero_smul]
  induction t using TensorProduct.inductionOn with
  | tmul x y => exact key x y
  | add p q hp hq =>
      funext j
      rw [map_add, map_add, Pi.add_apply, hp, hq]
      have hrhs : (∑ k : Fin n,
            if g k = j then a k • (tensorPiEquiv (B := B) bK) (p + q) k else 0)
          = ∑ x : Fin n, ((if g x = j then a x • (tensorPiEquiv (B := B) bK) p x else 0)
              + (if g x = j then a x • (tensorPiEquiv (B := B) bK) q x else 0)) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [map_add, Pi.add_apply, smul_add]
        by_cases h : g k = j <;> simp [h]
      rw [hrhs, Finset.sum_add_distrib]

/-- The order of a submodule element is the order of its value. -/
theorem addOrderOf_coe_submodule {M : Type*} [AddCommGroup M] (P : Submodule ℤ M) (x : ↥P) :
    addOrderOf (x : M) = addOrderOf x := by
  have h : ∀ m : ℕ, m • (x : M) = 0 ↔ m • x = 0 := fun m => by
    constructor
    · intro hm; exact Subtype.ext hm
    · intro hm; exact congrArg Subtype.val hm
  exact addOrderOf_eq_of_forall_nsmul_eq_zero _ _ h

/-- **The kernel condition in coordinates.**  A kernel element is one whose every coordinate is
killed by the corresponding diagonal entry. -/
theorem rTensor_eq_zero_iff (bK : Module.Basis (Fin n) ℤ K) (bF : Module.Basis κ ℤ F)
    (i : K →ₗ[ℤ] F) (g : Fin n → κ) (a : Fin n → ℤ)
    (hi : ∀ k, i (bK k) = a k • bF (g k)) (hg : Function.Injective g)
    (t : TensorProduct ℤ K B) :
    i.rTensor B t = 0 ↔ ∀ k : Fin n, a k • ((tensorPiEquiv (B := B) bK) t k) = 0 := by
  have h := tensorPiEquiv_rTensor_eq bK bF i g a hi t
  constructor
  · intro hzero k
    rw [hzero, map_zero] at h
    have h' : (fun j => ∑ k : Fin n,
        if g k = j then a k • ((tensorPiEquiv (B := B) bK) t k) else 0) = 0 := h.symm
    have hk := congrFun h' (g k)
    rw [Pi.zero_apply, Finset.sum_eq_single k] at hk
    · rwa [if_pos rfl] at hk
    · intro j _ hj
      rw [if_neg (fun hh => hj (hg hh))]
    · intro hj
      exact absurd (Finset.mem_univ k) hj
  · intro hc
    refine (tensorPiEquiv (B := B) bF).map_eq_zero_iff.mp ?_
    rw [h]
    funext j
    exact Finset.sum_eq_zero fun k _ => by
      by_cases hh : g k = j
      · rw [if_pos hh, hc k]
      · rw [if_neg hh]

/-- **A killing integer for the stage.**  The product of the diagonal entries' absolute values
kills every kernel element. -/
theorem natAbs_prod_smul_eq_zero (bK : Module.Basis (Fin n) ℤ K) (bF : Module.Basis κ ℤ F)
    (i : K →ₗ[ℤ] F) (g : Fin n → κ) (a : Fin n → ℤ)
    (hi : ∀ k, i (bK k) = a k • bF (g k)) (hg : Function.Injective g)
    (t : ↥(LinearMap.ker (i.rTensor B))) :
    ((∏ k : Fin n, (a k).natAbs : ℕ) : ℤ) • t.1 = 0 := by
  classical
  have hco := (rTensor_eq_zero_iff bK bF i g a hi hg t.1).mp t.2
  have hcoord : ∀ k : Fin n,
      ((∏ j : Fin n, (a j).natAbs : ℕ) : ℤ) •
        ((tensorPiEquiv (B := B) bK) t.1 k) = 0 := by
    intro k
    have hdvd : a k ∣ ((∏ j : Fin n, (a j).natAbs : ℕ) : ℤ) := by
      have h1 : (a k).natAbs ∣ ∏ j : Fin n, (a j).natAbs :=
        Finset.dvd_prod_of_mem _ (Finset.mem_univ k)
      have h2 : (a k).natAbs ∣ ((∏ j : Fin n, (a j).natAbs : ℕ) : ℤ).natAbs := by
        rw [Int.natAbs_natCast]; exact h1
      exact Int.natAbs_dvd_natAbs.mp h2
    obtain ⟨c, hc⟩ := hdvd
    rw [hc, mul_comm, mul_smul, hco k, smul_zero]
  have hzero : (tensorPiEquiv (B := B) bK)
      (((∏ j : Fin n, (a j).natAbs : ℕ) : ℤ) • t.1) = 0 := by
    rw [map_smul]
    funext k
    rw [Pi.smul_apply]
    exact hcoord k
  exact (tensorPiEquiv (B := B) bK).map_eq_zero_iff.mp hzero

variable {p k : ℕ}

/-- A number kills a function iff it kills every value. -/
theorem nsmul_eq_zero_pi_iff (m : ℕ) (x : ι → B) : m • x = 0 ↔ ∀ i, m • (x i) = 0 := by
  constructor
  · intro h i
    have h0 : (m • x) i = 0 := by rw [h, Pi.zero_apply]
    rwa [Pi.smul_apply] at h0
  · intro h
    funext i
    rw [Pi.smul_apply, h i, Pi.zero_apply]

/-- At a prime power, a function whose order is `p ^ k` has a value of order exactly `p ^ k`. -/
theorem exists_comp_addOrderOf_eq_of_eq_prime_pow_pi (hp : p.Prime) (hk : 0 < k)
    (x : ι → B) (hx : addOrderOf x = p ^ k) :
    ∃ j : ι, addOrderOf (x j) = p ^ k := by
  by_contra hcon
  push_neg at hcon
  have hkill0 : p ^ k • x = 0 := by rw [← hx]; exact addOrderOf_nsmul_eq_zero x
  have hcomp : ∀ i, addOrderOf (x i) ∣ p ^ k := fun i =>
    addOrderOf_dvd_iff_nsmul_eq_zero.mpr ((nsmul_eq_zero_pi_iff (p ^ k) x).mp hkill0 i)
  have hkill : p ^ (k - 1) • x = 0 := by
    refine (nsmul_eq_zero_pi_iff _ _).mpr fun i => ?_
    have hd : addOrderOf (x i) ∣ p ^ (k - 1) := by
      obtain ⟨j, hj, hjeq⟩ := exists_pow_eq_of_dvd_prime_pow hp (hcomp i)
      have hne : j ≠ k := fun hje => by
        rw [hje] at hjeq
        exact hcon i hjeq
      rw [hjeq]
      exact Nat.pow_dvd_pow p (by omega)
    exact addOrderOf_dvd_iff_nsmul_eq_zero.mp hd
  have hord : p ^ k ∣ p ^ (k - 1) := by
    rw [← hx]
    exact addOrderOf_dvd_iff_nsmul_eq_zero.mpr hkill
  rw [Nat.pow_dvd_pow_iff_le_right hp.one_lt] at hord
  omega

/-- **The Smith-normal-form stage step.**  A kernel element whose order is divisible by `p ^ k`
gives both a coordinate of order `p ^ k` in `B` and a diagonal entry divisible by `p ^ k`. -/
theorem exists_coord_of_prime_pow (bK : Module.Basis (Fin n) ℤ K) (bF : Module.Basis κ ℤ F)
    (i : K →ₗ[ℤ] F) (g : Fin n → κ) (a : Fin n → ℤ)
    (hi : ∀ k, i (bK k) = a k • bF (g k)) (hg : Function.Injective g)
    (hp : p.Prime) (hk : 0 < k)
    (t : ↥(LinearMap.ker (i.rTensor B))) (htpos : 0 < addOrderOf t)
    (htord : p ^ k ∣ addOrderOf t) :
    ∃ (kk : Fin n) (b : B), addOrderOf b = p ^ k ∧ (p : ℤ) ^ k ∣ a kk := by
  classical
  have hpk : 0 < p ^ k := pow_pos hp.pos k
  set y : ↥(LinearMap.ker (i.rTensor B)) := (addOrderOf t / p ^ k) • t with hy
  have hyord : addOrderOf y = p ^ k := addOrderOf_smul_div hpk htpos htord t rfl
  have hyval : addOrderOf (y : TensorProduct ℤ K B) = p ^ k := by
    rw [← hyord]; exact addOrderOf_coe_submodule _ y
  set v : Fin n → B := (tensorPiEquiv (B := B) bK) y.1 with hv
  have hvord : addOrderOf v = p ^ k := by
    rw [hv, ← hyval]
    refine addOrderOf_eq_of_forall_nsmul_eq_zero _ _ fun m => ?_
    rw [← map_nsmul, (tensorPiEquiv (B := B) bK).map_eq_zero_iff]
  obtain ⟨kk, hb'⟩ := exists_comp_addOrderOf_eq_of_eq_prime_pow_pi (B := B) hp hk v hvord
  refine ⟨kk, v kk, hb', ?_⟩
  have hker : a kk • v kk = 0 :=
    (rTensor_eq_zero_iff bK bF i g a hi hg y.1).mp y.2 kk
  have hdvd : (↑(addOrderOf (v kk)) : ℤ) ∣ a kk :=
    addOrderOf_dvd_iff_zsmul_eq_zero.mpr hker
  rw [hb', Int.natCast_pow] at hdvd
  exact hdvd

end TensorPiEngine

/-- The presentation sends a singleton to the corresponding multiple of its index. -/
theorem pres_single (A : Type) [AddCommGroup A] (a : A) (n : ℤ) :
    (pres A) (Finsupp.single a n) = n • a := by
  have h1 : Finsupp.single a n = n • Finsupp.single a 1 := by
    rw [Finsupp.smul_single', mul_one]
  rw [h1, map_zsmul]
  show n • (presHom A) (Finsupp.single a 1) = n • a
  rw [presHom_single]

/-! ### The `←` half: a pure cyclic subgroup of the syzygy

An element `a` of order `p ^ k` gives the syzygy element `z = p ^ k • single a 1`, and an element
`b` of order `p ^ k` gives the kernel element `z ⊗ b`.  The content of the section is that
`z ⊗ b` is nonzero of order exactly `p ^ k`.  The cyclic subgroup `ℤ z` is *pure* in the syzygy:
a multiple `m • y` of an element of the syzygy that lands in `ℤ z` puts `y` there too, because
`z` is supported at the single index `a`, so no coordinate off `a` can survive multiplication
by `m ≠ 0`, and the `a`-coordinate is pinned by the order of `a`.  The quotient is therefore
torsion-free, hence flat, and `ℤ z ⊗ B → ker (pres A) ⊗ B` is injective — no functional out
of the syzygy and no basis of it is needed. -/

section OrderBackward

variable {A B : Type} [AddCommGroup A] [AddCommGroup B]

/-- **The `←` half of the prime-power core.**  Elements of order `p ^ k` in `A` and in `B` give
an element of `Tor1(A, B)` of order `p ^ k`. -/
theorem exists_torOne_of_addOrderOf {p k : ℕ} (hp : p.Prime) (_hk : 0 < k)
    {a : A} (ha : addOrderOf a = p ^ k) {b : B} (hb : addOrderOf b = p ^ k) :
    ∃ x : TorBridge.torOne (ModuleCat.of ℤ A) (ModuleCat.of ℤ B), addOrderOf x = p ^ k := by
  classical
  have hpk : (p : ℤ) ^ k ≠ 0 := pow_ne_zero k (by exact_mod_cast hp.ne_zero)
  have hpk' : p ^ k ≠ 0 := pow_ne_zero k hp.ne_zero
  -- the two multiples vanish
  have haz : ((p : ℤ) ^ k) • a = 0 := by
    rw [← Int.natCast_pow, ← ha]
    exact addOrderOf_dvd_iff_zsmul_eq_zero.mp dvd_rfl
  have hbz : ((p : ℤ) ^ k) • b = 0 := by
    rw [← Int.natCast_pow, ← hb]
    exact addOrderOf_dvd_iff_zsmul_eq_zero.mp dvd_rfl
  -- the syzygy element
  set z : ↥(LinearMap.ker (pres A)) :=
    ⟨((p : ℤ) ^ k) • Finsupp.single a 1, smul_single_mem_ker haz⟩ with hzdef
  have hzval : (z : A →₀ ℤ) = Finsupp.single a ((p : ℤ) ^ k) := by
    rw [hzdef]
    exact Finsupp.smul_single' _ _ _ |>.trans (by rw [mul_one])
  -- the cyclic subgroup, as the range of the span map
  set f₀ : ℤ →ₗ[ℤ] ↥(LinearMap.ker (pres A)) :=
    LinearMap.toSpanSingleton ℤ ↥(LinearMap.ker (pres A)) z with hf₀
  have hf₀app : ∀ c : ℤ, f₀ c = c • z := fun c =>
    LinearMap.toSpanSingleton_apply ℤ ↥(LinearMap.ker (pres A)) z c
  -- a multiple of `z` vanishing in the free module is zero
  have hzm : ∀ m : ℤ, m • z = 0 → m = 0 := by
    intro m hm
    have h1 : m • (z : A →₀ ℤ) = 0 := congrArg Subtype.val hm
    rw [hzval, Finsupp.smul_single'] at h1
    have h2 : m * (p : ℤ) ^ k = 0 := by
      by_contra hne
      exact hne (Finsupp.single_eq_zero.mp h1)
    exact (mul_eq_zero.mp h2).resolve_right hpk
  have hf₀inj : Function.Injective f₀ := by
    intro m n hmn
    have h : f₀ (m - n) = 0 := by rw [map_sub, hmn, sub_self]
    rw [hf₀app] at h
    exact sub_eq_zero.mp (hzm (m - n) h)
  -- purity: a multiple in the cyclic subgroup is already there
  have hpure : ∀ (m : ℤ) (y : ↥(LinearMap.ker (pres A))), m ≠ 0 →
      m • y ∈ LinearMap.range f₀ → y ∈ LinearMap.range f₀ := by
    intro m y hm hmem
    rw [LinearMap.range_toSpanSingleton, Submodule.mem_span_singleton] at hmem
    obtain ⟨c, hc⟩ := hmem
    rw [LinearMap.range_toSpanSingleton, Submodule.mem_span_singleton]
    have hcoe : m • (y : A →₀ ℤ) = c • (z : A →₀ ℤ) := by
      have h := congrArg Subtype.val hc
      simpa only [Submodule.coe_smul] using h.symm
    -- every coordinate off `a` vanishes
    have hsingle : (y : A →₀ ℤ) = Finsupp.single a ((y : A →₀ ℤ) a) := by
      ext x
      by_cases hx : x = a
      · rw [hx, Finsupp.single_eq_same]
      · rw [Finsupp.single_eq_of_ne hx]
        have h0 : (m • (y : A →₀ ℤ)) x = 0 := by
          rw [hcoe, Finsupp.smul_apply, hzval, Finsupp.single_eq_of_ne hx, smul_zero]
        rw [Finsupp.smul_apply] at h0
        exact (mul_eq_zero.mp h0).resolve_left hm
    -- the `a`-coordinate is a multiple of `p ^ k`
    have hdvd : ((p : ℤ) ^ k) ∣ (y : A →₀ ℤ) a := by
      have hy : (pres A) (Finsupp.single a ((y : A →₀ ℤ) a)) = 0 := by
        rw [← hsingle]; exact y.2
      rw [pres_single] at hy
      rw [← Int.natCast_pow, ← ha]
      exact addOrderOf_dvd_iff_zsmul_eq_zero.mpr hy
    obtain ⟨c', hc'⟩ := hdvd
    refine ⟨c', ?_⟩
    apply Subtype.ext
    show c' • (z : A →₀ ℤ) = (y : A →₀ ℤ)
    rw [hzval, Finsupp.smul_single', hsingle, hc', mul_comm]
  -- the quotient is torsion-free, hence flat
  have htors : Submodule.torsion ℤ
      (↥(LinearMap.ker (pres A)) ⧸ LinearMap.range f₀) = ⊥ := by
    rw [Submodule.eq_bot_iff]
    rintro x hx
    obtain ⟨r, hr⟩ := hx
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective (p := LinearMap.range f₀) x
    have hr0 : (r : ℤ) ≠ 0 := by simpa using r.2
    have hmem : (r : ℤ) • y ∈ LinearMap.range f₀ := by
      refine (Submodule.Quotient.mk_eq_zero _).mp ?_
      rw [← Submodule.mkQ_apply, map_zsmul, Submodule.mkQ_apply]
      exact hr
    exact (Submodule.Quotient.mk_eq_zero _).mpr (hpure (r : ℤ) y hr0 hmem)
  haveI hTF : Module.IsTorsionFree ℤ (↥(LinearMap.ker (pres A)) ⧸ LinearMap.range f₀) :=
    Submodule.isTorsionFree_iff_torsion_eq_bot.mpr htors
  have hinj : Function.Injective (LinearMap.rTensor B f₀) :=
    TorReductions.rTensor_injective_of_flat_cokernel (B := B) f₀ hf₀inj
  -- the kernel element
  have hker : (z ⊗ₜ[ℤ] b) ∈
      LinearMap.ker (((LinearMap.ker (pres A)).subtype).rTensor B) := by
    rw [hzdef]
    exact kerTmul_mem_ker haz hbz
  set e : ↥(LinearMap.ker (((LinearMap.ker (pres A)).subtype).rTensor B)) := ⟨_, hker⟩
    with hedef
  -- its order is `p ^ k`
  have heordval : addOrderOf ((z : ↥(LinearMap.ker (pres A))) ⊗ₜ[ℤ] b) = p ^ k := by
    refine addOrderOf_eq_of_nsmul hpk' _ ?_ ?_
    · have h : ((p ^ k : ℕ) : ℤ) •
          ((z : ↥(LinearMap.ker (pres A))) ⊗ₜ[ℤ] b) = 0 := by
        rw [Nat.cast_pow, TensorProduct.smul_tmul', TensorProduct.smul_tmul, hbz,
          TensorProduct.tmul_zero]
      rwa [Nat.cast_smul_eq_nsmul] at h
    · intro m hm hmlt hzero
      have hzero' : ((m : ℤ) • ((z : ↥(LinearMap.ker (pres A))) ⊗ₜ[ℤ] b)) = 0 := by
        rwa [Nat.cast_smul_eq_nsmul]
      have himg : (m : ℤ) • ((z : ↥(LinearMap.ker (pres A))) ⊗ₜ[ℤ] b)
          = (LinearMap.rTensor B f₀) ((m : ℤ) ⊗ₜ[ℤ] b) := by
        rw [TensorProduct.smul_tmul', LinearMap.rTensor_tmul, hf₀app]
      rw [himg] at hzero'
      have h2 : ((m : ℤ) ⊗ₜ[ℤ] b) = 0 := hinj (by rw [hzero', map_zero])
      have h3 : (m : ℤ) • b = 0 := by
        have h4 := congrArg (TensorProduct.lid ℤ B) h2
        simpa only [TensorProduct.lid_tmul, map_zero] using h4
      have h3' : m • b = 0 := by rwa [Nat.cast_smul_eq_nsmul] at h3
      have hdvd : addOrderOf b ∣ m := addOrderOf_dvd_iff_nsmul_eq_zero.mpr h3'
      rw [hb] at hdvd
      exact absurd (Nat.le_of_dvd hm hdvd) (not_le.mpr hmlt)
  have heq : (e : TensorProduct ℤ ↥(LinearMap.ker (pres A)) B)
      = (z : ↥(LinearMap.ker (pres A))) ⊗ₜ[ℤ] b := by
    rw [hedef]
  have heord : addOrderOf e = p ^ k := by
    refine (addOrderOf_coe_submodule (LinearMap.ker
      (((LinearMap.ker (pres A)).subtype).rTensor B)) e).symm.trans ?_
    rw [heq]
    exact heordval
  refine ⟨(torOneTorKernelAddEquiv (B := B) (pres A) (pres_surjective A)).symm e, ?_⟩
  rw [AddEquiv.addOrderOf_eq]
  exact heord

end OrderBackward

/-! ### The `→` half: the stage and Smith normal form

An element of `Tor1(A, B)` of order `p ^ k` descends to a finitely generated stage of the
universal presentation (`TorStages.exists_stage_of_free`), whose middle term is free of finite
rank.  Smith normal form puts the stage's relation map in diagonal form, and the coordinate
engine reads the order: a coordinate of order `p ^ k` in `B`, and a diagonal entry divisible by
`p ^ k`, which is an elementary divisor of the stage's group and so gives an element of order
`p ^ k` in `A`. -/

section OrderForward

variable {A B : Type} [AddCommGroup A] [AddCommGroup B]

/-- The stage's relation map is injective: it is the restriction of the syzygy inclusion. -/
theorem stageRelMap_injective {K F : Type} [AddCommGroup K] [AddCommGroup F]
    (f : K →ₗ[ℤ] F) (hf : Function.Injective f) (F' : Submodule ℤ F) :
    Function.Injective (TorStages.stageRelMap f F') := by
  intro x y hxy
  exact Subtype.ext (hf (congrArg Subtype.val hxy))

/-- **The `→` half of the prime-power core.**  An element of `Tor1(A, B)` of order `p ^ k`
forces elements of order `p ^ k` in `A` and in `B`. -/
theorem exists_addOrderOf_of_torOne {p k : ℕ} (hp : p.Prime) (hk : 0 < k)
    (h : ∃ x : TorBridge.torOne (ModuleCat.of ℤ A) (ModuleCat.of ℤ B), addOrderOf x = p ^ k) :
    (∃ a : A, addOrderOf a = p ^ k) ∧ (∃ b : B, addOrderOf b = p ^ k) := by
  classical
  obtain ⟨x, hx⟩ := h
  have hpk : 0 < p ^ k := pow_pos hp.pos k
  have hpk1 : 1 < p ^ k := Nat.one_lt_pow hk.ne' hp.one_lt
  have hxne : x ≠ 0 := by
    intro h0
    rw [h0, addOrderOf_zero] at hx
    exact hpk1.ne' hx.symm
  -- the kernel element of the universal presentation
  set φ := torOneTorKernelAddEquiv (B := B) (pres A) (pres_surjective A) with hφ
  set e := φ x with he
  have heord : addOrderOf e = p ^ k := by rw [he, AddEquiv.addOrderOf_eq, hx]
  have hene : e ≠ 0 := by
    intro h0
    rw [h0, addOrderOf_zero] at heord
    exact hpk1.ne' heord.symm
  have heord1 : addOrderOf (e : TensorProduct ℤ ↥(LinearMap.ker (pres A)) B) = p ^ k :=
    (addOrderOf_coe_submodule _ e).trans heord
  -- the stage descent
  obtain ⟨F', hF'fg, ρ, hρ, t, ht1, ht2⟩ :=
    TorStages.exists_stage_of_free (K := ↥(LinearMap.ker (pres A))) (presBasis A)
      (LinearMap.ker (pres A)).subtype (x := (e : TensorProduct ℤ ↥(LinearMap.ker (pres A)) B))
      (LinearMap.mem_ker.mp e.2)
  -- the order of the stage element
  have htne : t ≠ 0 := by
    intro h0
    apply hene
    have h1 : (e : TensorProduct ℤ ↥(LinearMap.ker (pres A)) B) = 0 := by
      rw [← ht1, h0, map_zero]
    exact Subtype.ext h1
  have htord : p ^ k ∣ addOrderOf t := by
    have h1 : addOrderOf (e : TensorProduct ℤ ↥(LinearMap.ker (pres A)) B) ∣
        addOrderOf t := by
      refine addOrderOf_dvd_iff_nsmul_eq_zero.mpr ?_
      rw [← ht1, ← map_nsmul, addOrderOf_nsmul_eq_zero, map_zero]
    rwa [heord1] at h1
  -- `F'` is finitely generated and torsion-free, hence free
  haveI hFin : Module.Finite ℤ ↥F' := Module.Finite.of_fg hF'fg
  haveI hTF : Module.IsTorsionFree ℤ ↥F' :=
    Function.Injective.moduleIsTorsionFree F'.subtype F'.subtype_injective (fun _ _ => rfl)
  obtain ⟨n₀, bM⟩ := Module.basisOfFiniteTypeTorsionFree' (R := ℤ) (M := ↥F')
  -- Smith normal form of the stage's relation module inside `F'`
  set i := TorStages.stageRelMap (LinearMap.ker (pres A)).subtype F' with hi
  have hinj : Function.Injective i :=
    stageRelMap_injective _ (fun _ _ hab => Subtype.ext hab) F'
  set N : Submodule ℤ ↥F' := LinearMap.range i with hN
  have hNrange : LinearMap.range i = N := rfl
  obtain ⟨nn, bM', bN, g, a, hdiag⟩ := N.smithNormalForm bM
  -- the stage's presentation is the inclusion of `N`
  set eN : ↥(Submodule.comap (LinearMap.ker (pres A)).subtype F') ≃ₗ[ℤ] ↥N :=
    LinearEquiv.ofInjective i hinj with heN
  have hcomp : N.subtype.comp
      (eN : ↥(Submodule.comap (LinearMap.ker (pres A)).subtype F') →ₗ[ℤ] ↥N) = i := by
    ext k
    rfl
  -- transport the stage element along that identification
  set t' : TensorProduct ℤ ↥N B := (LinearMap.rTensor B (eN : _ →ₗ[ℤ] _)) t with ht'
  have htker : t' ∈ LinearMap.ker (N.subtype.rTensor B) := by
    rw [LinearMap.mem_ker, ht', ← LinearMap.comp_apply, ← LinearMap.rTensor_comp, hcomp]
    exact LinearMap.mem_ker.mp ht2
  have ht'ord : addOrderOf t' = addOrderOf t := by
    rw [ht']
    exact AddEquiv.addOrderOf_eq (LinearEquiv.rTensor B eN).toAddEquiv t
  have ht'pos : 0 < addOrderOf t' := by
    have hfin : ((∏ j : Fin nn, (a j).natAbs : ℕ) : ℤ) • t' = 0 :=
      natAbs_prod_smul_eq_zero bN bM' N.subtype g a hdiag g.injective ⟨t', htker⟩
    have hpos : 0 < (∏ j : Fin nn, (a j).natAbs : ℕ) := Finset.prod_pos fun j _ =>
      Int.natAbs_pos.mpr (by
        intro h0
        have h1 : (bN j : ↥F') = 0 := by rw [hdiag j, h0, zero_smul]
        exact bN.ne_zero j (Subtype.ext h1))
    refine Nat.pos_of_dvd_of_pos ?_ hpos
    rw [addOrderOf_dvd_iff_nsmul_eq_zero]
    simpa only [Nat.cast_smul_eq_nsmul] using hfin
  have ht'div : p ^ k ∣ addOrderOf (⟨t', htker⟩ :
      ↥(LinearMap.ker (N.subtype.rTensor B))) := by
    rw [(addOrderOf_coe_submodule _ ⟨t', htker⟩).symm, ht'ord]
    exact htord
  have ht'pos' : 0 < addOrderOf (⟨t', htker⟩ : ↥(LinearMap.ker (N.subtype.rTensor B))) := by
    rw [(addOrderOf_coe_submodule _ ⟨t', htker⟩).symm]
    exact ht'pos
  -- the engine at the stage
  obtain ⟨kk, b, hb, hdvd⟩ :=
    exists_coord_of_prime_pow bN bM' N.subtype g a hdiag g.injective hp hk
      ⟨t', htker⟩ ht'pos' ht'div
  refine ⟨?_, ⟨b, hb⟩⟩
  -- the elementary divisor gives an element of `A`
  set x₀ : ↥F' := bM' (g kk) with hx₀
  have hane : a kk ≠ 0 := by
    intro h0
    have h1 : (bN kk : ↥F') = 0 := by rw [hdiag kk, h0, zero_smul]
    exact bN.ne_zero kk (Subtype.ext h1)
  have hNeq : TorStages.stageRel (LinearMap.ker (pres A)).subtype F' = N := by
    rw [← TorStages.range_stageRelMap, hN]
  have hmem : (a kk) • x₀ ∈ N := by
    rw [← hdiag kk]
    exact (bN kk).2
  have hkey : ∀ n : ℕ, (n : ℤ) • x₀ ∈ N → (a kk).natAbs ∣ n := by
    intro n hn
    set z : ↥N := ⟨(n : ℤ) • x₀, hn⟩ with hz
    have h1 : (bM'.repr ((n : ℤ) • x₀)) (g kk) = (n : ℤ) := by
      rw [map_zsmul, hx₀, Module.Basis.repr_self, Finsupp.smul_single', mul_one,
        Finsupp.single_eq_same]
    have hzval : (N.subtype z : ↥F') = (n : ℤ) • x₀ := rfl
    have h2 : (bM'.repr ((n : ℤ) • x₀)) (g kk) = (bN.repr z) kk * a kk := by
      rw [← hzval, basis_repr_comp_eq_sum bN bM' N.subtype g a hdiag z, Finset.sum_apply',
        Finset.sum_eq_single kk]
      · rw [Finsupp.single_eq_same]
      · intro j _ hj
        rw [Finsupp.single_eq_of_ne (g.injective.ne hj).symm]
      · intro hj
        exact absurd (Finset.mem_univ kk) hj
    have h3 : a kk ∣ (n : ℤ) := by
      rw [← h1, h2]
      exact dvd_mul_left _ _
    simpa using Int.natAbs_dvd_natAbs.mpr h3
  have hcoker : addOrderOf (Submodule.Quotient.mk (p := N) x₀) = (a kk).natAbs := by
    have hA : addOrderOf (Submodule.Quotient.mk (p := N) x₀) ∣ (a kk).natAbs := by
      have hz : (a kk) • (Submodule.Quotient.mk (p := N) x₀) = 0 := by
        show (a kk) • (N.mkQ x₀) = 0
        rw [← map_zsmul, Submodule.mkQ_apply]
        exact (Submodule.Quotient.mk_eq_zero N).mpr hmem
      have h4 := addOrderOf_dvd_iff_zsmul_eq_zero.mpr hz
      simpa using Int.natAbs_dvd_natAbs.mpr h4
    have hB : (a kk).natAbs ∣ addOrderOf (Submodule.Quotient.mk (p := N) x₀) := by
      refine hkey _ ?_
      have h6 : Submodule.Quotient.mk (p := N)
          (((addOrderOf (Submodule.Quotient.mk (p := N) x₀) : ℕ) : ℤ) • x₀) = 0 := by
        rw [← Submodule.mkQ_apply, map_zsmul, Submodule.mkQ_apply,
          Nat.cast_smul_eq_nsmul, addOrderOf_nsmul_eq_zero]
      exact (Submodule.Quotient.mk_eq_zero N).mp h6
    exact Nat.dvd_antisymm hA hB
  -- transport the cokernel element into `A`
  set y₁ : ↥F' ⧸ TorStages.stageRel (LinearMap.ker (pres A)).subtype F' :=
    (Submodule.quotEquivOfEq N _ hNeq.symm).toLinearMap
      (Submodule.Quotient.mk (p := N) x₀) with hy₁
  have hy₁ord : addOrderOf y₁ = (a kk).natAbs := by
    rw [hy₁]
    exact (AddEquiv.addOrderOf_eq (Submodule.quotEquivOfEq N _ hNeq.symm).toAddEquiv _).trans
      hcoker
  set y₂ : (A →₀ ℤ) ⧸ LinearMap.range (LinearMap.ker (pres A)).subtype :=
    TorStages.stageMap (LinearMap.ker (pres A)).subtype F' y₁ with hy₂
  have hy₂ord : addOrderOf y₂ = (a kk).natAbs := by
    rw [hy₂]
    rw [addOrderOf_map_eq_of_injective _ (TorStages.stageMap_injective _ _)]
    exact hy₁ord
  set y₃ : (A →₀ ℤ) ⧸ LinearMap.ker (pres A) :=
    (Submodule.quotEquivOfEq (LinearMap.range (LinearMap.ker (pres A)).subtype)
      (LinearMap.ker (pres A)) (Submodule.range_subtype _)).toLinearMap y₂ with hy₃
  have hy₃ord : addOrderOf y₃ = (a kk).natAbs := by
    rw [hy₃]
    exact (AddEquiv.addOrderOf_eq (Submodule.quotEquivOfEq _ _
      (Submodule.range_subtype _)).toAddEquiv _).trans hy₂ord
  set y₄ : A := (LinearMap.quotKerEquivOfSurjective (pres A) (pres_surjective A)).toLinearMap y₃
    with hy₄
  have hy₄ord : addOrderOf y₄ = (a kk).natAbs := by
    rw [hy₄]
    exact (AddEquiv.addOrderOf_eq
      (LinearMap.quotKerEquivOfSurjective (pres A) (pres_surjective A)).toAddEquiv _).trans
      hy₃ord
  have hdvd' : p ^ k ∣ (a kk).natAbs := by
    rw [← Int.natCast_pow] at hdvd
    simpa using Int.natAbs_dvd_natAbs.mpr hdvd
  obtain ⟨a', ha'⟩ := exists_addOrderOf_of_dvd_addOrderOf
    (Int.natAbs_pos.mpr hane) hdvd' y₄ hy₄ord
  exact ⟨a', ha'⟩

end OrderForward

/-- **The prime-power core of the order statement (#155).**  `Tor1(A, B)` has an element
of order `p ^ k` if and only if both `A` and `B` have one. -/
theorem torOne_prime_pow_iff {A B : Type} [AddCommGroup A] [AddCommGroup B]
    {p k : ℕ} (hp : p.Prime) (hk : 0 < k) :
    (∃ x : TorBridge.torOne (ModuleCat.of ℤ A) (ModuleCat.of ℤ B), addOrderOf x = p ^ k) ↔
    (∃ a : A, addOrderOf a = p ^ k) ∧ (∃ b : B, addOrderOf b = p ^ k) :=
  ⟨exists_addOrderOf_of_torOne hp hk,
    fun ⟨⟨_, ha⟩, ⟨_, hb⟩⟩ => exists_torOne_of_addOrderOf hp hk ha hb⟩

/-- **Hatcher, *Algebraic Topology* (2002), §3.A Exercise 6, printed p. 267, second
statement (#155).**  For all abelian groups `A` and `B` and every positive `n`,
`Tor1(A, B)` has an element of order `n` if and only if both `A` and `B` have one:
both directions assemble from the prime-power core `torOne_prime_pow_iff` through the coprime
order law `addOrderOf_add_eq_mul_addOrderOf_of_coprime` and the scaling law `addOrderOf_nsmul'`. -/
theorem torOne_exists_addOrderOf_iff {A B : Type} [AddCommGroup A] [AddCommGroup B] {n : ℕ}
    (hn : 0 < n) :
    (∃ x : TorBridge.torOne (ModuleCat.of ℤ A) (ModuleCat.of ℤ B), addOrderOf x = n) ↔
    (∃ a : A, addOrderOf a = n) ∧ (∃ b : B, addOrderOf b = n) := by
  constructor
  · intro h
    have hpp : ∀ p : ℕ, p.Prime → ∀ k : ℕ, 0 < k → p ^ k ∣ n →
        (∃ a : A, addOrderOf a = p ^ k) ∧ (∃ b : B, addOrderOf b = p ^ k) := by
      intro p hp' k hk hdvd
      obtain ⟨y, hy⟩ := h
      obtain ⟨y', hy'⟩ := exists_addOrderOf_of_dvd_addOrderOf hn hdvd y hy
      exact (torOne_prime_pow_iff hp' hk).mp ⟨y', hy'⟩
    exact ⟨exists_addOrderOf_of_forall_prime_pow hn fun p hp' k hk hdvd =>
      (hpp p hp' k hk hdvd).1,
      exists_addOrderOf_of_forall_prime_pow hn fun p hp' k hk hdvd =>
      (hpp p hp' k hk hdvd).2⟩
  · rintro ⟨⟨a, ha⟩, b, hb⟩
    refine exists_addOrderOf_of_forall_prime_pow hn fun p hp' k hk hdvd => ?_
    obtain ⟨a', ha'⟩ := exists_addOrderOf_of_dvd_addOrderOf hn hdvd a ha
    obtain ⟨b', hb'⟩ := exists_addOrderOf_of_dvd_addOrderOf hn hdvd b hb
    exact (torOne_prime_pow_iff hp' hk).mpr ⟨⟨a', ha'⟩, b', hb'⟩

end Hatcher3A6Order
end Hatcher3A6Torsion
end LeanCategories.Homological.TorExercise3A6
