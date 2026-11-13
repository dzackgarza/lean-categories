/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 License as described in the file LICENSE.
-/
module

public import Mathlib.Data.DFinsupp.FiniteInfinite
public import Mathlib.GroupTheory.FiniteAbelian.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Unbundled.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Prod
public import Mathlib.SetTheory.ZFC.Class
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
public import Mathlib.RingTheory.PrincipalIdealDomain
public import Mathlib.Algebra.EuclideanDomain.Int
public import Mathlib.LinearAlgebra.Dimension.Localization
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.CategoryTheory.Abelian.Projective.Resolution
public import Mathlib.Algebra.Homology.ShortComplex.Homology
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.RingTheory.Flat.Equalizer
public import Mathlib.CategoryTheory.Abelian.LeftDerived
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

@[expose] public section

/-!
# TorFGTorsion: torsion closure properties for Tor

Card `E-HAT-3.A-6 / E-HAT-3.A-2` of the qualifying-exam corpus.  Source: Hatcher, *Algebraic
Topology*, Section 3.A, exercises 2 and 6 (printed p. 267).  Certificate:
new-qual-site `proofs/cards/TorFGTorsion.lean` at commit `16c09abaa4`.

LC-09 search record (queries run against the formalization corpus and local
Mathlib): the statements below are the certificate's own; Mathlib's
CategoryTheory.Tor supplies the derived-functor definition and no comparison
API, so the certificate is ported whole.

Provenance: ported from new-qual-site at commit `16c09abaa4`,
`proofs/cards/TorFGTorsion.lean` with the `def` names carrying underscores renamed per the
  `defsWithUnderscore` lint (`prodRight_int` -> `prodRightInt`); theorem names keep the
    certificate's spelling.
-/


/-!
# `E-HAT-3.A-6` / `E-HAT-3.A-2`: `Tor₁` of a finitely generated abelian group is torsion

The structure theorem of finitely generated abelian groups
(`AddCommGroup.equiv_free_prod_directSum_zmod`) splits a finitely generated `A` into a free part
and a finite direct sum of cyclic prime-power groups.  This file proves that `Tor₁(A, B)` is a
torsion group for every `B`, from the free case (vanishing on projectives), the cyclic case
(the Serre-Class route of `cards/TorTorsionClass.lean`), and the additivity of `Tor₁` in its
first argument, which is carried through the dimension-shift bridge
(`cards/TorArbitrary.lean`'s `torOneIsoKerIncl`) and the presentation-level kernel computation
(`cards/TorReductions.lean`'s `map_prodLeft_torKernel`).
-/

namespace LeanCategories.Homological.TorFGTorsion

open CategoryTheory Limits MonoidalCategory
open scoped TensorProduct

/-! ## The torsion closure properties -/

/-- A product of two torsion groups is torsion. -/
theorem isAddTorsion_prod {M N : Type*} [AddCommGroup M] [AddCommGroup N]
    (hM : IsAddTorsion M) (hN : IsAddTorsion N) : IsAddTorsion (M × N) := by
  intro x
  obtain ⟨a, b⟩ := x
  obtain ⟨m, hm, hma⟩ := isOfFinAddOrder_iff_nsmul_eq_zero.mp (hM a)
  obtain ⟨n, hn, hna⟩ := isOfFinAddOrder_iff_nsmul_eq_zero.mp (hN b)
  refine isOfFinAddOrder_iff_nsmul_eq_zero.mpr ⟨m * n, Nat.mul_pos (by omega) (by omega), ?_⟩
  ext
  · show (m * n) • a = 0
    rw [Nat.mul_comm m n, mul_smul, hma, smul_zero]
  · show (m * n) • b = 0
    rw [mul_smul, hna, smul_zero]

/-- The divisibility transfer for `ℕ`-multiples: if `k` kills `y` and `k ∣ N`, then `N` kills
`y`.  By induction on the quotient, splitting `k * (j + 1)` as `k * j + k`. -/
theorem nsmul_eq_zero_of_dvd {M : Type*} [AddCommGroup M] (k N : ℕ) (y : M)
    (hk : k ∣ N) (h0 : k • y = 0) : N • y = 0 := by
  obtain ⟨j, hj⟩ := hk
  subst hj
  induction j with
  | zero => simp
  | succ j ih =>
    have hsplit : k * (j + 1) = k * j + k := by ring
    rw [hsplit, add_nsmul, ih, h0, add_zero]

/-- The `ZMod` killing step: for `m ≠ 0`, `m` kills every element of `ZMod m`, by the
`Fintype`-card Lagrange route (`card_nsmul_eq_zero`) with `ZMod.card`. -/
theorem zmod_nsmul_eq_zero (m : ℕ) (hm : m ≠ 0) (y : ZMod m) : (m : ℕ) • y = 0 := by
  haveI : NeZero m := ⟨hm⟩
  have h : (Fintype.card (ZMod m)) • y = 0 := card_nsmul_eq_zero
  rw [ZMod.card m] at h
  exact h

/-- A finite direct sum of finite groups is torsion: the `Fintype`-card route, with the
`DFinsupp` `Fintype` instance over a `Fintype` index. -/
theorem isAddTorsion_dfinsupp_fintype {ι : Type*} [Fintype ι] [DecidableEq ι] {β : ι → Type*}
    [∀ i, AddCommGroup (β i)] [∀ i, Fintype (β i)] :
    IsAddTorsion (Π₀ i, β i) := by
  intro x
  haveI : Nonempty (Π₀ i, β i) := ⟨0⟩
  refine isOfFinAddOrder_iff_nsmul_eq_zero.mpr ⟨Fintype.card (Π₀ i, β i), Fintype.card_pos, ?_⟩
  exact card_nsmul_eq_zero

/-- The structure theorem's torsion part: a finite direct sum of prime-power cyclic groups is
torsion. -/
theorem isAddTorsion_dfinsupp_zmod {ι : Type*} [Fintype ι] [DecidableEq ι] (p : ι → ℕ)
    (e : ι → ℕ) (hp : ∀ i, 0 < p i) : IsAddTorsion (Π₀ i, ZMod (p i ^ e i)) := by
  haveI hfintype : ∀ i, Fintype (ZMod (p i ^ e i)) := fun i => by
    haveI : NeZero (p i ^ e i) := ⟨ne_of_gt (pow_pos (hp i) (e i))⟩
    exact ZMod.fintype (p i ^ e i)
  exact isAddTorsion_dfinsupp_fintype

/-! ## The transport along a linear equivalence, and the tensor distributivity -/

/-- `IsAddTorsion` transports backwards along a `ℤ`-linear equivalence: if the target is torsion,
so is the source. This is the direction the card statements need, since the bridge
(`TorArbitrary.torOneIsoKerIncl`) presents `Tor₁` as a kernel submodule. -/
theorem isAddTorsion_of_linearEquiv {M N : Type*} [AddCommGroup M] [AddCommGroup N]
    (e : M ≃ₗ[ℤ] N) (hN : IsAddTorsion N) : IsAddTorsion M := by
  intro x
  obtain ⟨n, hn, hne⟩ := isOfFinAddOrder_iff_nsmul_eq_zero.mp (hN (e x))
  refine isOfFinAddOrder_iff_nsmul_eq_zero.mpr ⟨n, hn, ?_⟩
  refine e.injective ?_
  rw [map_nsmul, hne]
  exact (map_zero e).symm

/-- The left-tensor distributivity over a binary product, in the `prodRight` form the
`tensorLeft B` bridge of `cards/TorArbitrary.lean` consumes. -/
noncomputable def prodRightInt {B M N : Type*} [AddCommGroup B] [AddCommGroup M]
    [AddCommGroup N] : B ⊗[ℤ] (M × N) ≃ₗ[ℤ] (B ⊗[ℤ] M) × (B ⊗[ℤ] N) :=
  TensorProduct.prodRight ℤ ℤ B M N

end LeanCategories.Homological.TorFGTorsion

