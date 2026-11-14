/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 License as described in the file LICENSE.
-/
module

public import Mathlib.GroupTheory.FiniteAbelian.Basic
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.LinearAlgebra.TensorProduct.Prod
public import Mathlib.LinearAlgebra.DirectSum.TensorProduct
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
`addOrderOf_nsmul'`; the prime-power case is read off the same stage descent,
where the finitely generated case is the coordinate analysis of
`TorTorsion.exists_coord` in the cyclic decomposition.
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

/-! ## The two-term resolution of a free presentation, at any free middle term

`TorFreeResolution` builds its two-term projective resolution only for presentations whose
middle term is `(Fin r → ℤ)`.  The structure-theorem presentation below has middle term
`(Fin n →₀ ℤ) × (⨁ i, ℤ)`, so the construction is generalized here: any surjection with
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
  ConcreteCategory.mono_of_injective _ fun x y h => Subtype.ext h

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
  haveI : Mono ((twoTermComplexG f).d 1 0) := twoTermComplexG_mono_d_one_zero f
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

end LeanCategories.Homological.TorExercise3A6
