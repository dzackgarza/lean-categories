/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality
public import Mathlib.Algebra.Category.Grp.ZModuleEquivalence
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.LinearAlgebra.Quotient.Bilinear
public import Mathlib.LinearAlgebra.TensorProduct.Basic

/-!
# Cup products on ordinary group cohomology

This is the discrete, inhomogeneous-cochain adaptation of the all-degree cup-product
construction in

`ImperialCollegeLondon/FLT@81d8bee0f708ac41cb975da76ed3c43ad99fae72`
`FLT/Mathlib/RepresentationTheory/Homological/ContCohomology/CupProduct.lean`.

The checked FLT reference constructs a cochain pairing, proves its Leibniz rule, restricts it to
cocycles, proves that coboundaries in either variable die in the target quotient, and then descends
the pairing to cohomology.  We use exactly that proof spine here, but on Mathlib's canonical
ordinary group-cohomology carrier `groupCohomology.inhomogeneousCochains`.  For trivial integral
coefficients the cochain pairing is the usual inhomogeneous formula

`(σ ∪ τ)(g₁, ..., gₚ₊q) = σ(g₁, ..., gₚ) * τ(gₚ₊₁, ..., gₚ₊q)`.

This file is the reference-port infrastructure used by Weibel Construction 6.1.14
(FC05-C06-U016).  The external product itself is obtained in
`GroupCohomologyCrossProduct` by pulling back along the two projections and then applying this cup
product.
-/

@[expose] public section

noncomputable section

namespace LeanCategories.Homological

open CategoryTheory
open MonoidalCategory
open scoped TensorProduct

variable (G : Type) [Group G]

abbrev groupCohomologyTrivialIntRep : Rep ℤ G := Rep.trivial ℤ G ℤ

abbrev groupCohomologyCochains (n : ℕ) : ModuleCat ℤ :=
  (groupCohomology.inhomogeneousCochains (groupCohomologyTrivialIntRep G)).X n

/-- The ordinary inhomogeneous cup product on integral cochains with trivial coefficients.
The explicit target degree keeps the subsequent Leibniz statement free of transport noise. -/
def groupCohomologyCupCochain (p q r : ℕ) (hr : r = p + q)
    (σ : groupCohomologyCochains G p) (τ : groupCohomologyCochains G q) :
    groupCohomologyCochains G r :=
  fun g ↦
    σ (g ∘ Fin.cast hr.symm ∘ Fin.castAdd q) *
      τ (g ∘ Fin.cast hr.symm ∘ Fin.natAdd p)

@[simp]
lemma groupCohomologyCupCochain_apply (p q r : ℕ) (hr : r = p + q)
    (σ : groupCohomologyCochains G p) (τ : groupCohomologyCochains G q)
    (g : Fin r → G) :
    groupCohomologyCupCochain G p q r hr σ τ g =
      σ (g ∘ Fin.cast hr.symm ∘ Fin.castAdd q) *
        τ (g ∘ Fin.cast hr.symm ∘ Fin.natAdd p) := rfl

/-- The cochain cup product, bundled as a bilinear map. -/
def groupCohomologyCupCochainBilinear (p q r : ℕ) (hr : r = p + q) :
    groupCohomologyCochains G p →ₗ[ℤ]
      groupCohomologyCochains G q →ₗ[ℤ] groupCohomologyCochains G r :=
  LinearMap.mk₂ ℤ (groupCohomologyCupCochain G p q r hr)
    (fun _ _ _ ↦ by ext; simp [groupCohomologyCupCochain, add_mul])
    (fun _ _ _ ↦ by ext; simp [groupCohomologyCupCochain, smul_eq_mul, mul_assoc])
    (fun _ _ _ ↦ by ext; simp [groupCohomologyCupCochain, mul_add])
    (fun _ _ _ ↦ by ext; simp [groupCohomologyCupCochain, smul_eq_mul]; ring)

@[simp]
lemma groupCohomologyCupCochainBilinear_apply (p q r : ℕ) (hr : r = p + q)
    (σ : groupCohomologyCochains G p) (τ : groupCohomologyCochains G q) :
    groupCohomologyCupCochainBilinear G p q r hr σ τ =
      groupCohomologyCupCochain G p q r hr σ τ := rfl

@[simp]
lemma groupCohomologyCupCochain_zero_left (p q r : ℕ) (hr : r = p + q)
    (τ : groupCohomologyCochains G q) :
    groupCohomologyCupCochain G p q r hr 0 τ = 0 := by
  ext g
  change (0 : ℤ) * τ (g ∘ Fin.cast hr.symm ∘ Fin.natAdd p) = 0
  simp

@[simp]
lemma groupCohomologyCupCochain_zero_right (p q r : ℕ) (hr : r = p + q)
    (σ : groupCohomologyCochains G p) :
    groupCohomologyCupCochain G p q r hr σ 0 = 0 := by
  ext g
  change σ (g ∘ Fin.cast hr.symm ∘ Fin.castAdd q) * (0 : ℤ) = 0
  simp

private lemma groupCohomologyCupCochain_add_left (p q r : ℕ) (hr : r = p + q)
    (σ₁ σ₂ : groupCohomologyCochains G p) (τ : groupCohomologyCochains G q) :
    groupCohomologyCupCochain G p q r hr (σ₁ + σ₂) τ =
      groupCohomologyCupCochain G p q r hr σ₁ τ +
        groupCohomologyCupCochain G p q r hr σ₂ τ := by
  ext g
  change (σ₁ _ + σ₂ _) * τ _ = σ₁ _ * τ _ + σ₂ _ * τ _
  ring

private lemma groupCohomologyCupCochain_zsmul_left (p q r : ℕ) (hr : r = p + q)
    (c : ℤ) (σ : groupCohomologyCochains G p) (τ : groupCohomologyCochains G q) :
    groupCohomologyCupCochain G p q r hr (c • σ) τ =
      c • groupCohomologyCupCochain G p q r hr σ τ := by
  ext g
  change (c * σ _) * τ _ = c * (σ _ * τ _)
  ring

private lemma groupCohomologyCupCochain_add_right (p q r : ℕ) (hr : r = p + q)
    (σ : groupCohomologyCochains G p) (τ₁ τ₂ : groupCohomologyCochains G q) :
    groupCohomologyCupCochain G p q r hr σ (τ₁ + τ₂) =
      groupCohomologyCupCochain G p q r hr σ τ₁ +
        groupCohomologyCupCochain G p q r hr σ τ₂ := by
  ext g
  change σ _ * (τ₁ _ + τ₂ _) = σ _ * τ₁ _ + σ _ * τ₂ _
  ring

private lemma groupCohomologyCupCochain_zsmul_right (p q r : ℕ) (hr : r = p + q)
    (c : ℤ) (σ : groupCohomologyCochains G p) (τ : groupCohomologyCochains G q) :
    groupCohomologyCupCochain G p q r hr σ (c • τ) =
      c • groupCohomologyCupCochain G p q r hr σ τ := by
  ext g
  change σ _ * (c * τ _) = c * (σ _ * τ _)
  ring

private lemma sum_fin_add_succ {M : Type} [AddCommMonoid M] (p q : ℕ)
    (f : Fin (p + q + 1) → M) :
    (∑ j, f j) =
      (∑ i : Fin p, f (Fin.castAdd (q + 1) i)) +
        ∑ j : Fin (q + 1), f (Fin.natAdd p j) :=
  Fin.sum_univ_add (a := p) (b := q + 1) f

private lemma fin_cast_self_fun {n : ℕ} (h : n = n) : Fin.cast h = id := by
  funext i
  apply Fin.ext
  rfl

private lemma contractNth_castAdd_prefix (p q : ℕ) (g : Fin (p + q + 1) → G)
    (i : Fin p) :
    (Fin.contractNth (Fin.castAdd (q + 1) i) (· * ·) g) ∘ Fin.castAdd q =
      Fin.contractNth (Fin.castSucc i) (· * ·)
        (g ∘ Fin.cast (by omega : (p + 1) + q = p + q + 1) ∘ Fin.castAdd q) := by
  funext k
  simp only [Function.comp_apply, Fin.contractNth, Fin.val_castAdd, Fin.val_castSucc,
    Fin.val_cast, Fin.val_succ]
  split_ifs <;> congr 1 <;> apply Fin.ext <;> simp_all

private lemma contractNth_castAdd_suffix (p q : ℕ) (g : Fin (p + q + 1) → G)
    (i : Fin p) :
    (Fin.contractNth (Fin.castAdd (q + 1) i) (· * ·) g) ∘ Fin.natAdd p =
      g ∘ Fin.cast (by omega : (p + 1) + q = p + q + 1) ∘ Fin.natAdd (p + 1) := by
  funext k
  simp only [Function.comp_apply]
  rw [Fin.contractNth_apply_of_gt _ _ _ _ (by simp; omega)]
  apply congrArg g
  apply Fin.ext
  change p + k.val + 1 = p + 1 + k.val
  omega

private lemma contractNth_natAdd_prefix (p q : ℕ) (g : Fin (p + q + 1) → G)
    (j : Fin (q + 1)) :
    (Fin.contractNth (@Fin.natAdd (q + 1) p j) (· * ·) g) ∘ Fin.castAdd q =
      g ∘ Fin.castAdd (q + 1) := by
  funext k
  simp only [Function.comp_apply]
  rw [Fin.contractNth_apply_of_lt _ _ _ _ (by simp; omega)]
  apply congrArg g
  apply Fin.ext
  rfl

private lemma contractNth_natAdd_suffix (p q : ℕ) (g : Fin (p + q + 1) → G)
    (j : Fin (q + 1)) :
    (Fin.contractNth (@Fin.natAdd (q + 1) p j) (· * ·) g) ∘ Fin.natAdd p =
      Fin.contractNth j (· * ·) (g ∘ Fin.natAdd p) := by
  funext k
  simp only [Function.comp_apply]
  rcases lt_trichotomy k.val j.val with h | h | h
  · rw [Fin.contractNth_apply_of_lt _ _ _ _ (by simp; omega),
      Fin.contractNth_apply_of_lt _ _ _ _ h]
    apply congrArg g
    apply Fin.ext
    rfl
  · rw [Fin.contractNth_apply_of_eq _ _ _ _ (by simp; omega),
      Fin.contractNth_apply_of_eq _ _ _ _ h]
    congr 1 <;> apply congrArg g <;> apply Fin.ext <;> rfl
  · rw [Fin.contractNth_apply_of_gt _ _ _ _ (by simp; omega),
      Fin.contractNth_apply_of_gt _ _ _ _ h]
    apply congrArg g
    apply Fin.ext
    rfl

private lemma tail_castAdd (p q : ℕ) (g : Fin (p + q + 1) → G) :
    (fun i : Fin (p + q) ↦ g i.succ) ∘ Fin.castAdd q =
      (fun i : Fin p ↦
        (g ∘ Fin.cast (by omega : (p + 1) + q = p + q + 1) ∘ Fin.castAdd q) i.succ) := by
  funext i
  apply congrArg g
  apply Fin.ext
  rfl

private lemma tail_natAdd (p q : ℕ) (g : Fin (p + q + 1) → G) :
    (fun i : Fin (p + q) ↦ g i.succ) ∘ Fin.natAdd p =
      g ∘ Fin.cast (by omega : (p + 1) + q = p + q + 1) ∘ Fin.natAdd (p + 1) := by
  funext i
  apply congrArg g
  apply Fin.ext
  change p + i.val + 1 = p + 1 + i.val
  omega

private lemma natAdd_tail (p q : ℕ) (g : Fin (p + q + 1) → G) :
    (fun i : Fin q ↦ (g ∘ Fin.natAdd p) i.succ) =
      g ∘ Fin.cast (by omega : (p + 1) + q = p + q + 1) ∘ Fin.natAdd (p + 1) := by
  funext i
  apply congrArg g
  apply Fin.ext
  change p + (i.val + 1) = p + 1 + i.val
  omega

private lemma contractNth_last_prefix (p q : ℕ) (g : Fin (p + q + 1) → G) :
    Fin.contractNth (Fin.last p) (· * ·)
        (g ∘ Fin.cast (by omega : (p + 1) + q = p + q + 1) ∘ Fin.castAdd q) =
      g ∘ Fin.castAdd (q + 1) := by
  funext k
  simp only [Function.comp_apply]
  rw [Fin.contractNth_apply_of_lt _ _ _ _ (by simp)]
  apply congrArg g
  apply Fin.ext
  rfl

private lemma neg_one_pow_shift (p : ℕ) (j : ℕ) :
    (-1 : ℤ) ^ (p + j + 1) = (-1 : ℤ) ^ p * (-1 : ℤ) ^ (j + 1) := by
  rw [← pow_add]
  congr 1

private lemma neg_one_pow_succ_add (p : ℕ) :
    (-1 : ℤ) ^ (p + 1) + (-1 : ℤ) ^ p = 0 := by
  rw [pow_succ]
  ring

/-- The Leibniz identity for the ordinary inhomogeneous cup product.  This is the direct
ordinary-cochain counterpart of `ContRepresentation.cupPair_d_comm` and
`ContinuousCohomology.cup_d_comm` in the checked FLT reference. -/
lemma groupCohomologyCup_d_comm (p q r : ℕ) (hr : r = p + q)
    (σ : groupCohomologyCochains G p) (τ : groupCohomologyCochains G q) :
    inhomogeneousCochains.d (groupCohomologyTrivialIntRep G) r
        (groupCohomologyCupCochain G p q r hr σ τ) =
      groupCohomologyCupCochain G (p + 1) q (r + 1) (by omega)
          (inhomogeneousCochains.d (groupCohomologyTrivialIntRep G) p σ) τ +
        (-1 : ℤ) ^ p •
          groupCohomologyCupCochain G p (q + 1) (r + 1) (by omega) σ
            (inhomogeneousCochains.d (groupCohomologyTrivialIntRep G) q τ) := by
  subst r
  ext g
  simp only [inhomogeneousCochains.d_hom_apply, Rep.trivial_ρ_apply,
    groupCohomologyCupCochain, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [sum_fin_add_succ p q]
  simp only [Fin.val_castAdd, Fin.val_natAdd]
  simp only [fin_cast_self_fun, Function.comp_id, Function.id_comp,
    Representation.trivial_apply]
  simp_rw [contractNth_castAdd_prefix G p q g, contractNth_castAdd_suffix G p q g]
  simp_rw [contractNth_natAdd_prefix G p q g, contractNth_natAdd_suffix G p q g]
  simp_rw [tail_castAdd G p q g, tail_natAdd G p q g]
  rw [natAdd_tail G p q g]
  simp_rw [neg_one_pow_shift p]
  have hσ :
      (∑ x : Fin (p + 1),
          (-1 : ℤ) ^ (x.val + 1) *
            σ (Fin.contractNth x (· * ·)
              (g ∘ Fin.cast (by omega : (p + 1) + q = p + q + 1) ∘ Fin.castAdd q))) =
        (∑ x : Fin p,
            (-1 : ℤ) ^ (x.val + 1) *
              σ (Fin.contractNth x.castSucc (· * ·)
                (g ∘ Fin.cast (by omega : (p + 1) + q = p + q + 1) ∘ Fin.castAdd q))) +
          (-1 : ℤ) ^ (p + 1) * σ (g ∘ Fin.castAdd (q + 1)) := by
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [contractNth_last_prefix G p q g]
  rw [hσ]
  rw [add_mul, add_mul, mul_add, mul_add]
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  ring_nf

private abbrev groupCohomologyCanonicalComplex :=
  groupCohomology.inhomogeneousCochains (groupCohomologyTrivialIntRep G)

private lemma groupCohomology_iCocycles_d_eq_zero (n : ℕ)
    (σ : groupCohomology.cocycles (groupCohomologyTrivialIntRep G) n) :
    inhomogeneousCochains.d (groupCohomologyTrivialIntRep G) n
      (groupCohomology.iCocycles (groupCohomologyTrivialIntRep G) n σ) = 0 := by
  rw [← groupCohomology.inhomogeneousCochains.d_def]
  change ((groupCohomologyCanonicalComplex G).iCycles n ≫
      (groupCohomologyCanonicalComplex G).d n (n + 1)) σ = 0
  rw [(groupCohomologyCanonicalComplex G).iCycles_d]
  rfl

private lemma groupCohomology_iCocycles_zsmul (n : ℕ) (c : ℤ)
    (σ : groupCohomology.cocycles (groupCohomologyTrivialIntRep G) n) :
    groupCohomology.iCocycles (groupCohomologyTrivialIntRep G) n (c • σ) =
      c • groupCohomology.iCocycles (groupCohomologyTrivialIntRep G) n σ := by
  exact map_zsmul (groupCohomology.iCocycles (groupCohomologyTrivialIntRep G) n).hom c σ

private def groupCohomologyCupCocycleAux (p q r : ℕ) (hr : r = p + q)
    (σ : groupCohomology.cocycles (groupCohomologyTrivialIntRep G) p)
    (τ : groupCohomology.cocycles (groupCohomologyTrivialIntRep G) q) :
    groupCohomology.cocycles (groupCohomologyTrivialIntRep G) r :=
  groupCohomology.cocyclesMk
    (groupCohomologyCupCochain G p q r hr
      (groupCohomology.iCocycles (groupCohomologyTrivialIntRep G) p σ)
    (groupCohomology.iCocycles (groupCohomologyTrivialIntRep G) q τ))
    (by
      calc
        _ = groupCohomologyCupCochain G (p + 1) q (r + 1) (by omega)
              (inhomogeneousCochains.d (groupCohomologyTrivialIntRep G) p
                (groupCohomology.iCocycles (groupCohomologyTrivialIntRep G) p σ))
              (groupCohomology.iCocycles (groupCohomologyTrivialIntRep G) q τ) +
            (-1 : ℤ) ^ p •
              groupCohomologyCupCochain G p (q + 1) (r + 1) (by omega)
                (groupCohomology.iCocycles (groupCohomologyTrivialIntRep G) p σ)
                (inhomogeneousCochains.d (groupCohomologyTrivialIntRep G) q
                  (groupCohomology.iCocycles (groupCohomologyTrivialIntRep G) q τ)) :=
          groupCohomologyCup_d_comm G p q r hr _ _
        _ = 0 := by
          rw [groupCohomology_iCocycles_d_eq_zero G p σ,
            groupCohomology_iCocycles_d_eq_zero G q τ]
          simp)

private lemma groupCohomology_iCocycles_cupAux (p q r : ℕ) (hr : r = p + q)
    (σ : groupCohomology.cocycles (groupCohomologyTrivialIntRep G) p)
    (τ : groupCohomology.cocycles (groupCohomologyTrivialIntRep G) q) :
    groupCohomology.iCocycles (groupCohomologyTrivialIntRep G) r
        (groupCohomologyCupCocycleAux G p q r hr σ τ) =
      groupCohomologyCupCochain G p q r hr
        (groupCohomology.iCocycles (groupCohomologyTrivialIntRep G) p σ)
        (groupCohomology.iCocycles (groupCohomologyTrivialIntRep G) q τ) := by
  unfold groupCohomologyCupCocycleAux
  apply groupCohomology.iCocycles_mk

private lemma groupCohomologyCupCocycleAux_add_left (p q r : ℕ) (hr : r = p + q)
    (σ₁ σ₂ : groupCohomology.cocycles (groupCohomologyTrivialIntRep G) p)
    (τ : groupCohomology.cocycles (groupCohomologyTrivialIntRep G) q) :
    groupCohomologyCupCocycleAux G p q r hr (σ₁ + σ₂) τ =
      groupCohomologyCupCocycleAux G p q r hr σ₁ τ +
        groupCohomologyCupCocycleAux G p q r hr σ₂ τ := by
  apply (ModuleCat.mono_iff_injective
    (groupCohomology.iCocycles (groupCohomologyTrivialIntRep G) r)).1 inferInstance
  calc
    _ = groupCohomologyCupCochain G p q r hr
          (groupCohomology.iCocycles (groupCohomologyTrivialIntRep G) p (σ₁ + σ₂))
          (groupCohomology.iCocycles (groupCohomologyTrivialIntRep G) q τ) :=
      groupCohomology_iCocycles_cupAux G p q r hr _ _
    _ = groupCohomologyCupCochain G p q r hr
          (groupCohomology.iCocycles (groupCohomologyTrivialIntRep G) p σ₁ +
            groupCohomology.iCocycles (groupCohomologyTrivialIntRep G) p σ₂)
          (groupCohomology.iCocycles (groupCohomologyTrivialIntRep G) q τ) := by rw [map_add]
    _ = _ := by
      rw [groupCohomologyCupCochain_add_left, map_add,
        groupCohomology_iCocycles_cupAux, groupCohomology_iCocycles_cupAux]

private lemma groupCohomologyCupCocycleAux_zsmul_left (p q r : ℕ) (hr : r = p + q)
    (c : ℤ) (σ : groupCohomology.cocycles (groupCohomologyTrivialIntRep G) p)
    (τ : groupCohomology.cocycles (groupCohomologyTrivialIntRep G) q) :
    groupCohomologyCupCocycleAux G p q r hr (c • σ) τ =
      c • groupCohomologyCupCocycleAux G p q r hr σ τ := by
  apply (ModuleCat.mono_iff_injective
    (groupCohomology.iCocycles (groupCohomologyTrivialIntRep G) r)).1 inferInstance
  calc
    _ = groupCohomologyCupCochain G p q r hr
          (groupCohomology.iCocycles (groupCohomologyTrivialIntRep G) p (c • σ))
          (groupCohomology.iCocycles (groupCohomologyTrivialIntRep G) q τ) :=
      groupCohomology_iCocycles_cupAux G p q r hr _ _
    _ = groupCohomologyCupCochain G p q r hr
          (c • groupCohomology.iCocycles (groupCohomologyTrivialIntRep G) p σ)
          (groupCohomology.iCocycles (groupCohomologyTrivialIntRep G) q τ) := by
      rw [groupCohomology_iCocycles_zsmul]
    _ = _ := by
      rw [groupCohomologyCupCochain_zsmul_left, groupCohomology_iCocycles_zsmul,
        groupCohomology_iCocycles_cupAux]

private lemma groupCohomologyCupCocycleAux_add_right (p q r : ℕ) (hr : r = p + q)
    (σ : groupCohomology.cocycles (groupCohomologyTrivialIntRep G) p)
    (τ₁ τ₂ : groupCohomology.cocycles (groupCohomologyTrivialIntRep G) q) :
    groupCohomologyCupCocycleAux G p q r hr σ (τ₁ + τ₂) =
      groupCohomologyCupCocycleAux G p q r hr σ τ₁ +
        groupCohomologyCupCocycleAux G p q r hr σ τ₂ := by
  apply (ModuleCat.mono_iff_injective
    (groupCohomology.iCocycles (groupCohomologyTrivialIntRep G) r)).1 inferInstance
  calc
    _ = groupCohomologyCupCochain G p q r hr
          (groupCohomology.iCocycles (groupCohomologyTrivialIntRep G) p σ)
          (groupCohomology.iCocycles (groupCohomologyTrivialIntRep G) q (τ₁ + τ₂)) :=
      groupCohomology_iCocycles_cupAux G p q r hr _ _
    _ = groupCohomologyCupCochain G p q r hr
          (groupCohomology.iCocycles (groupCohomologyTrivialIntRep G) p σ)
          (groupCohomology.iCocycles (groupCohomologyTrivialIntRep G) q τ₁ +
            groupCohomology.iCocycles (groupCohomologyTrivialIntRep G) q τ₂) := by rw [map_add]
    _ = _ := by
      rw [groupCohomologyCupCochain_add_right, map_add,
        groupCohomology_iCocycles_cupAux, groupCohomology_iCocycles_cupAux]

private lemma groupCohomologyCupCocycleAux_zsmul_right (p q r : ℕ) (hr : r = p + q)
    (c : ℤ) (σ : groupCohomology.cocycles (groupCohomologyTrivialIntRep G) p)
    (τ : groupCohomology.cocycles (groupCohomologyTrivialIntRep G) q) :
    groupCohomologyCupCocycleAux G p q r hr σ (c • τ) =
      c • groupCohomologyCupCocycleAux G p q r hr σ τ := by
  apply (ModuleCat.mono_iff_injective
    (groupCohomology.iCocycles (groupCohomologyTrivialIntRep G) r)).1 inferInstance
  calc
    _ = groupCohomologyCupCochain G p q r hr
          (groupCohomology.iCocycles (groupCohomologyTrivialIntRep G) p σ)
          (groupCohomology.iCocycles (groupCohomologyTrivialIntRep G) q (c • τ)) :=
      groupCohomology_iCocycles_cupAux G p q r hr _ _
    _ = groupCohomologyCupCochain G p q r hr
          (groupCohomology.iCocycles (groupCohomologyTrivialIntRep G) p σ)
          (c • groupCohomology.iCocycles (groupCohomologyTrivialIntRep G) q τ) := by
      rw [groupCohomology_iCocycles_zsmul]
    _ = _ := by
      rw [groupCohomologyCupCochain_zsmul_right, groupCohomology_iCocycles_zsmul,
        groupCohomology_iCocycles_cupAux]

/-- A coboundary in the left variable cups with a cocycle to a coboundary in the target.
This is the first quotient-descent step in the checked FLT proof spine. -/
private lemma groupCohomologyCup_boundary_left (i q : ℕ)
    (x : (groupCohomologyCanonicalComplex G).X i)
    (τ : groupCohomology.cocycles (groupCohomologyTrivialIntRep G) q) :
    groupCohomology.π (groupCohomologyTrivialIntRep G) (i + q + 1)
        (groupCohomologyCupCocycleAux G (i + 1) q (i + q + 1) (by omega)
          ((groupCohomologyCanonicalComplex G).toCycles i (i + 1) x) τ) = 0 := by
  let s := i + q
  let r := s + 1
  let pre : (groupCohomologyCanonicalComplex G).X s :=
    groupCohomologyCupCochain G i q s rfl x
      (groupCohomology.iCocycles (groupCohomologyTrivialIntRep G) q τ)
  have hboundary :
      groupCohomologyCupCocycleAux G (i + 1) q r (by omega)
          ((groupCohomologyCanonicalComplex G).toCycles i (i + 1) x) τ =
        (groupCohomologyCanonicalComplex G).toCycles s r pre := by
    apply (ModuleCat.mono_iff_injective
      ((groupCohomologyCanonicalComplex G).iCycles r)).1 inferInstance
    rw [groupCohomology_iCocycles_cupAux]
    change
      groupCohomologyCupCochain G (i + 1) q r (by omega)
          (((groupCohomologyCanonicalComplex G).toCycles i (i + 1) ≫
            (groupCohomologyCanonicalComplex G).iCycles (i + 1)) x)
          (groupCohomology.iCocycles (groupCohomologyTrivialIntRep G) q τ) =
        (((groupCohomologyCanonicalComplex G).toCycles s r ≫
          (groupCohomologyCanonicalComplex G).iCycles r) pre)
    rw [(groupCohomologyCanonicalComplex G).toCycles_i,
      (groupCohomologyCanonicalComplex G).toCycles_i]
    change
      groupCohomologyCupCochain G (i + 1) q r (by omega)
          ((groupCohomologyCanonicalComplex G).d i (i + 1) x)
          (groupCohomology.iCocycles (groupCohomologyTrivialIntRep G) q τ) =
        (groupCohomologyCanonicalComplex G).d s r pre
    have h := groupCohomologyCup_d_comm G i q s rfl x
      (groupCohomology.iCocycles (groupCohomologyTrivialIntRep G) q τ)
    rw [groupCohomology_iCocycles_d_eq_zero G q τ] at h
    simp at h
    simpa [groupCohomology.inhomogeneousCochains.d_def, s, r, pre] using h.symm
  change (groupCohomologyCanonicalComplex G).homologyπ r
      (groupCohomologyCupCocycleAux G (i + 1) q r (by omega)
        ((groupCohomologyCanonicalComplex G).toCycles i (i + 1) x) τ) = 0
  rw [hboundary]
  change (((groupCohomologyCanonicalComplex G).toCycles s r ≫
    (groupCohomologyCanonicalComplex G).homologyπ r) pre) = 0
  rw [(groupCohomologyCanonicalComplex G).toCycles_comp_homologyπ]
  rfl

/-- A cocycle in the left variable cups with a coboundary in the right variable to a target
coboundary.  The `(-1)^p` factor is the signed second boundary-descent step from the checked FLT
proof spine. -/
private lemma groupCohomologyCup_boundary_right (p j : ℕ)
    (σ : groupCohomology.cocycles (groupCohomologyTrivialIntRep G) p)
    (y : (groupCohomologyCanonicalComplex G).X j) :
    groupCohomology.π (groupCohomologyTrivialIntRep G) (p + j + 1)
        (groupCohomologyCupCocycleAux G p (j + 1) (p + j + 1) rfl σ
          ((groupCohomologyCanonicalComplex G).toCycles j (j + 1) y)) = 0 := by
  let s := p + j
  let r := s + 1
  let pre : (groupCohomologyCanonicalComplex G).X s :=
    (-1 : ℤ) ^ p • groupCohomologyCupCochain G p j s rfl
      (groupCohomology.iCocycles (groupCohomologyTrivialIntRep G) p σ) y
  have hboundary :
      groupCohomologyCupCocycleAux G p (j + 1) r rfl σ
          ((groupCohomologyCanonicalComplex G).toCycles j (j + 1) y) =
        (groupCohomologyCanonicalComplex G).toCycles s r pre := by
    apply (ModuleCat.mono_iff_injective
      ((groupCohomologyCanonicalComplex G).iCycles r)).1 inferInstance
    rw [groupCohomology_iCocycles_cupAux]
    change
      groupCohomologyCupCochain G p (j + 1) r rfl
          (groupCohomology.iCocycles (groupCohomologyTrivialIntRep G) p σ)
          (((groupCohomologyCanonicalComplex G).toCycles j (j + 1) ≫
            (groupCohomologyCanonicalComplex G).iCycles (j + 1)) y) =
        (((groupCohomologyCanonicalComplex G).toCycles s r ≫
          (groupCohomologyCanonicalComplex G).iCycles r) pre)
    rw [(groupCohomologyCanonicalComplex G).toCycles_i,
      (groupCohomologyCanonicalComplex G).toCycles_i]
    change
      groupCohomologyCupCochain G p (j + 1) r rfl
          (groupCohomology.iCocycles (groupCohomologyTrivialIntRep G) p σ)
          ((groupCohomologyCanonicalComplex G).d j (j + 1) y) =
        (groupCohomologyCanonicalComplex G).d s r pre
    have h := groupCohomologyCup_d_comm G p j s rfl
      (groupCohomology.iCocycles (groupCohomologyTrivialIntRep G) p σ) y
    rw [groupCohomology_iCocycles_d_eq_zero G p σ] at h
    simp at h
    rw [show (groupCohomologyCanonicalComplex G).d s r =
        inhomogeneousCochains.d (groupCohomologyTrivialIntRep G) s by
      simpa [s, r] using
        groupCohomology.inhomogeneousCochains.d_def (groupCohomologyTrivialIntRep G) s]
    rw [show (groupCohomologyCanonicalComplex G).d j (j + 1) =
        inhomogeneousCochains.d (groupCohomologyTrivialIntRep G) j by
      simpa using
        groupCohomology.inhomogeneousCochains.d_def (groupCohomologyTrivialIntRep G) j]
    dsimp [pre]
    rw [map_zsmul, h]
    ext g
    change _ = (-1 : ℤ) ^ p * ((-1 : ℤ) ^ p * _)
    rw [← mul_assoc, ← pow_add, Even.neg_one_pow ⟨p, rfl⟩, one_mul]
  change (groupCohomologyCanonicalComplex G).homologyπ r
      (groupCohomologyCupCocycleAux G p (j + 1) r rfl σ
        ((groupCohomologyCanonicalComplex G).toCycles j (j + 1) y)) = 0
  rw [hboundary]
  change (((groupCohomologyCanonicalComplex G).toCycles s r ≫
    (groupCohomologyCanonicalComplex G).homologyπ r) pre) = 0
  rw [(groupCohomologyCanonicalComplex G).toCycles_comp_homologyπ]
  rfl

private abbrev groupCohomologyForgetToAddCommGrp :=
  forget₂ (ModuleCat ℤ) AddCommGrpCat

private lemma groupCohomologyCupCocycleAux_zero_right (p q r : ℕ) (hr : r = p + q)
    (σ : groupCohomology.cocycles (groupCohomologyTrivialIntRep G) p) :
    groupCohomologyCupCocycleAux G p q r hr σ 0 = 0 := by
  have h := groupCohomologyCupCocycleAux_zsmul_right G p q r hr 0 σ
    (0 : groupCohomology.cocycles (groupCohomologyTrivialIntRep G) q)
  simpa using h

/-- For a fixed left cocycle, cup product followed by the target homology projection,
viewed first as an additive map.  Passing through `AddCommGrpCat` avoids choosing between the two
definitionally distinct presentations of integer scalar multiplication exposed by the module API. -/
private def groupCohomologyCupCyclesToHomologyAdd (p q r : ℕ) (hr : r = p + q)
    (σ : groupCohomology.cocycles (groupCohomologyTrivialIntRep G) p) :
    (groupCohomologyForgetToAddCommGrp.obj
        (groupCohomology.cocycles (groupCohomologyTrivialIntRep G) q)) ⟶
      groupCohomologyForgetToAddCommGrp.obj
        (groupCohomology (groupCohomologyTrivialIntRep G) r) :=
  AddCommGrpCat.ofHom
    { toFun := fun τ ↦
        groupCohomology.π (groupCohomologyTrivialIntRep G) r
          (groupCohomologyCupCocycleAux G p q r hr σ τ)
      map_zero' := by
        rw [groupCohomologyCupCocycleAux_zero_right, map_zero]
      map_add' := by
        intro τ₁ τ₂
        rw [groupCohomologyCupCocycleAux_add_right, map_add] }

/-- For a fixed left cocycle, cup product followed by projection to target cohomology, bundled as
a `ℤ`-linear morphism on the canonical cocycle object. -/
private def groupCohomologyCupCyclesToHomology (p q r : ℕ) (hr : r = p + q)
    (σ : groupCohomology.cocycles (groupCohomologyTrivialIntRep G) p) :
    groupCohomology.cocycles (groupCohomologyTrivialIntRep G) q ⟶
      groupCohomology (groupCohomologyTrivialIntRep G) r :=
  groupCohomologyForgetToAddCommGrp.preimage
    (groupCohomologyCupCyclesToHomologyAdd G p q r hr σ)

@[simp]
private lemma groupCohomologyCupCyclesToHomology_apply (p q r : ℕ) (hr : r = p + q)
    (σ : groupCohomology.cocycles (groupCohomologyTrivialIntRep G) p)
    (τ : groupCohomology.cocycles (groupCohomologyTrivialIntRep G) q) :
    groupCohomologyCupCyclesToHomology G p q r hr σ τ =
      groupCohomology.π (groupCohomologyTrivialIntRep G) r
        (groupCohomologyCupCocycleAux G p q r hr σ τ) := by
  change (groupCohomologyForgetToAddCommGrp.map
      (groupCohomologyForgetToAddCommGrp.preimage
        (groupCohomologyCupCyclesToHomologyAdd G p q r hr σ))) τ = _
  rw [groupCohomologyForgetToAddCommGrp.map_preimage]
  rfl

private lemma groupCohomologyCupCyclesToHomology_boundary_right
    (p j r : ℕ) (hr : r = p + (j + 1))
    (σ : groupCohomology.cocycles (groupCohomologyTrivialIntRep G) p)
    (y : (groupCohomologyCanonicalComplex G).X j) :
    groupCohomologyCupCyclesToHomology G p (j + 1) r hr σ
        ((groupCohomologyCanonicalComplex G).toCycles j (j + 1) y) = 0 := by
  rw [groupCohomologyCupCyclesToHomology_apply]
  have hdeg : r = p + j + 1 := by omega
  cases hdeg
  exact groupCohomologyCup_boundary_right G p j σ y

/-- First homology-quotient descent: for a fixed left cocycle, the right cocycle variable descends
through the canonical cokernel presentation of ordinary group cohomology. -/
private def groupCohomologyCupRightDescData (p q r : ℕ) (hr : r = p + q)
    (σ : groupCohomology.cocycles (groupCohomologyTrivialIntRep G) p) :
    { l : groupCohomology (groupCohomologyTrivialIntRep G) q ⟶
        groupCohomology (groupCohomologyTrivialIntRep G) r //
      groupCohomology.π (groupCohomologyTrivialIntRep G) q ≫ l =
        groupCohomologyCupCyclesToHomology G p q r hr σ } := by
  cases q with
  | zero =>
      apply CokernelCofork.IsColimit.desc'
        ((groupCohomologyCanonicalComplex G).homologyIsCokernel
          (i := 0) (j := 0) (by simp))
      simpa only [(groupCohomologyCanonicalComplex G).toCycles_eq_zero
        (i := 0) (j := 0) (by simp), zero_comp]
  | succ j =>
      apply CokernelCofork.IsColimit.desc'
        ((groupCohomologyCanonicalComplex G).homologyIsCokernel
          (i := j) (j := j + 1) (by simp))
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro y
      change groupCohomologyCupCyclesToHomology G p (j + 1) r hr σ
          ((groupCohomologyCanonicalComplex G).toCycles j (j + 1) y) = 0
      exact groupCohomologyCupCyclesToHomology_boundary_right G p j r hr σ y

private def groupCohomologyCupRightDesc (p q r : ℕ) (hr : r = p + q)
    (σ : groupCohomology.cocycles (groupCohomologyTrivialIntRep G) p) :
    groupCohomology (groupCohomologyTrivialIntRep G) q ⟶
      groupCohomology (groupCohomologyTrivialIntRep G) r :=
  (groupCohomologyCupRightDescData G p q r hr σ).1

private lemma groupCohomologyCupRightDesc_π (p q r : ℕ) (hr : r = p + q)
    (σ : groupCohomology.cocycles (groupCohomologyTrivialIntRep G) p) :
    groupCohomology.π (groupCohomologyTrivialIntRep G) q ≫
        groupCohomologyCupRightDesc G p q r hr σ =
      groupCohomologyCupCyclesToHomology G p q r hr σ :=
  (groupCohomologyCupRightDescData G p q r hr σ).2

private lemma groupCohomologyCupCyclesToHomology_add_left
    (p q r : ℕ) (hr : r = p + q)
    (σ₁ σ₂ : groupCohomology.cocycles (groupCohomologyTrivialIntRep G) p) :
    groupCohomologyCupCyclesToHomology G p q r hr (σ₁ + σ₂) =
      groupCohomologyCupCyclesToHomology G p q r hr σ₁ +
        groupCohomologyCupCyclesToHomology G p q r hr σ₂ := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro τ
  rw [groupCohomologyCupCyclesToHomology_apply,
    groupCohomologyCupCocycleAux_add_left, map_add,
    groupCohomologyCupCyclesToHomology_apply,
    groupCohomologyCupCyclesToHomology_apply]

private lemma groupCohomologyCupCyclesToHomology_zero_left
    (p q r : ℕ) (hr : r = p + q) :
    groupCohomologyCupCyclesToHomology G p q r hr 0 = 0 := by
  have h := groupCohomologyCupCyclesToHomology_add_left G p q r hr
    (0 : groupCohomology.cocycles (groupCohomologyTrivialIntRep G) p) 0
  simpa using h

private lemma groupCohomologyCupRightDesc_add_left
    (p q r : ℕ) (hr : r = p + q)
    (σ₁ σ₂ : groupCohomology.cocycles (groupCohomologyTrivialIntRep G) p) :
    groupCohomologyCupRightDesc G p q r hr (σ₁ + σ₂) =
      groupCohomologyCupRightDesc G p q r hr σ₁ +
        groupCohomologyCupRightDesc G p q r hr σ₂ := by
  apply (cancel_epi (groupCohomology.π (groupCohomologyTrivialIntRep G) q)).1
  simp only [groupCohomologyCupRightDesc_π, Preadditive.comp_add]
  exact groupCohomologyCupCyclesToHomology_add_left G p q r hr σ₁ σ₂

private lemma groupCohomologyCupRightDesc_zero_left
    (p q r : ℕ) (hr : r = p + q) :
    groupCohomologyCupRightDesc G p q r hr 0 = 0 := by
  apply (cancel_epi (groupCohomology.π (groupCohomologyTrivialIntRep G) q)).1
  rw [groupCohomologyCupRightDesc_π,
    groupCohomologyCupCyclesToHomology_zero_left]
  simp

private abbrev groupCohomologyCupHomTarget (q r : ℕ) : ModuleCat ℤ :=
  (ihom (groupCohomology (groupCohomologyTrivialIntRep G) q)).obj
    (groupCohomology (groupCohomologyTrivialIntRep G) r)

/-- The once-descended cup pairing, regarded additively in its remaining left cocycle variable. -/
private def groupCohomologyCupLeftCyclesAdd (p q r : ℕ) (hr : r = p + q) :
    groupCohomologyForgetToAddCommGrp.obj
        (groupCohomology.cocycles (groupCohomologyTrivialIntRep G) p) ⟶
      groupCohomologyForgetToAddCommGrp.obj (groupCohomologyCupHomTarget G q r) :=
  AddCommGrpCat.ofHom
    { toFun := groupCohomologyCupRightDesc G p q r hr
      map_zero' := groupCohomologyCupRightDesc_zero_left G p q r hr
      map_add' := groupCohomologyCupRightDesc_add_left G p q r hr }

/-- The once-descended cup pairing as a `ℤ`-linear morphism in the remaining left cocycle
variable.  `ℤ`-linearity is supplied canonically by the equivalence with additive commutative
groups. -/
private def groupCohomologyCupLeftCyclesMap (p q r : ℕ) (hr : r = p + q) :
    groupCohomology.cocycles (groupCohomologyTrivialIntRep G) p ⟶
      groupCohomologyCupHomTarget G q r :=
  groupCohomologyForgetToAddCommGrp.preimage
    (groupCohomologyCupLeftCyclesAdd G p q r hr)

@[simp]
private lemma groupCohomologyCupLeftCyclesMap_apply (p q r : ℕ) (hr : r = p + q)
    (σ : groupCohomology.cocycles (groupCohomologyTrivialIntRep G) p) :
    groupCohomologyCupLeftCyclesMap G p q r hr σ =
      groupCohomologyCupRightDesc G p q r hr σ := by
  change (groupCohomologyForgetToAddCommGrp.map
      (groupCohomologyForgetToAddCommGrp.preimage
        (groupCohomologyCupLeftCyclesAdd G p q r hr))) σ = _
  rw [groupCohomologyForgetToAddCommGrp.map_preimage]
  rfl

private lemma groupCohomologyCupCyclesToHomology_boundary_left
    (i q r : ℕ) (hr : r = (i + 1) + q)
    (x : (groupCohomologyCanonicalComplex G).X i) :
    groupCohomologyCupCyclesToHomology G (i + 1) q r hr
        ((groupCohomologyCanonicalComplex G).toCycles i (i + 1) x) = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro τ
  rw [groupCohomologyCupCyclesToHomology_apply]
  have hdeg : r = i + q + 1 := by omega
  cases hdeg
  exact groupCohomologyCup_boundary_left G i q x τ

private lemma groupCohomologyCupLeftCyclesMap_boundary
    (i q r : ℕ) (hr : r = (i + 1) + q)
    (x : (groupCohomologyCanonicalComplex G).X i) :
    groupCohomologyCupLeftCyclesMap G (i + 1) q r hr
        ((groupCohomologyCanonicalComplex G).toCycles i (i + 1) x) = 0 := by
  rw [groupCohomologyCupLeftCyclesMap_apply]
  change groupCohomologyCupRightDesc G (i + 1) q r hr
      ((groupCohomologyCanonicalComplex G).toCycles i (i + 1) x) =
    (0 : groupCohomology (groupCohomologyTrivialIntRep G) q ⟶
      groupCohomology (groupCohomologyTrivialIntRep G) r)
  apply (cancel_epi (groupCohomology.π (groupCohomologyTrivialIntRep G) q)).1
  rw [groupCohomologyCupRightDesc_π]
  rw [groupCohomologyCupCyclesToHomology_boundary_left]
  simp

/-- Second homology-quotient descent: the remaining left cocycle variable descends through the
canonical cokernel presentation of ordinary group cohomology. -/
private def groupCohomologyCupLeftDescData (p q r : ℕ) (hr : r = p + q) :
    { l : groupCohomology (groupCohomologyTrivialIntRep G) p ⟶
        groupCohomologyCupHomTarget G q r //
      groupCohomology.π (groupCohomologyTrivialIntRep G) p ≫ l =
        groupCohomologyCupLeftCyclesMap G p q r hr } := by
  cases p with
  | zero =>
      apply CokernelCofork.IsColimit.desc'
        ((groupCohomologyCanonicalComplex G).homologyIsCokernel
          (i := 0) (j := 0) (by simp))
      simpa only [(groupCohomologyCanonicalComplex G).toCycles_eq_zero
        (i := 0) (j := 0) (by simp), zero_comp]
  | succ i =>
      apply CokernelCofork.IsColimit.desc'
        ((groupCohomologyCanonicalComplex G).homologyIsCokernel
          (i := i) (j := i + 1) (by simp))
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      change groupCohomologyCupLeftCyclesMap G (i + 1) q r hr
        ((groupCohomologyCanonicalComplex G).toCycles i (i + 1) x) = 0
      exact groupCohomologyCupLeftCyclesMap_boundary G i q r hr x

private def groupCohomologyCupLeftDesc (p q r : ℕ) (hr : r = p + q) :
    groupCohomology (groupCohomologyTrivialIntRep G) p ⟶
      groupCohomologyCupHomTarget G q r :=
  (groupCohomologyCupLeftDescData G p q r hr).1

private lemma groupCohomologyCupLeftDesc_π (p q r : ℕ) (hr : r = p + q) :
    groupCohomology.π (groupCohomologyTrivialIntRep G) p ≫
        groupCohomologyCupLeftDesc G p q r hr =
      groupCohomologyCupLeftCyclesMap G p q r hr :=
  (groupCohomologyCupLeftDescData G p q r hr).2

private lemma groupCohomologyCupLeftDesc_apply_π (p q r : ℕ) (hr : r = p + q)
    (σ : groupCohomology.cocycles (groupCohomologyTrivialIntRep G) p) :
    groupCohomologyCupLeftDesc G p q r hr
        (groupCohomology.π (groupCohomologyTrivialIntRep G) p σ) =
      groupCohomologyCupRightDesc G p q r hr σ := by
  change ((groupCohomology.π (groupCohomologyTrivialIntRep G) p ≫
    groupCohomologyCupLeftDesc G p q r hr) σ) = _
  rw [groupCohomologyCupLeftDesc_π, groupCohomologyCupLeftCyclesMap_apply]

private lemma groupCohomologyCupRightDesc_apply_π (p q r : ℕ) (hr : r = p + q)
    (σ : groupCohomology.cocycles (groupCohomologyTrivialIntRep G) p)
    (τ : groupCohomology.cocycles (groupCohomologyTrivialIntRep G) q) :
    groupCohomologyCupRightDesc G p q r hr σ
        (groupCohomology.π (groupCohomologyTrivialIntRep G) q τ) =
      groupCohomology.π (groupCohomologyTrivialIntRep G) r
        (groupCohomologyCupCocycleAux G p q r hr σ τ) := by
  change ((groupCohomology.π (groupCohomologyTrivialIntRep G) q ≫
    groupCohomologyCupRightDesc G p q r hr σ) τ) = _
  rw [groupCohomologyCupRightDesc_π, groupCohomologyCupCyclesToHomology_apply]

/-- The all-degree cup product on ordinary integral group cohomology.  The two quotient descents
above produce a morphism `H^p → Hom(H^q,H^r)`; Mathlib's closed symmetric monoidal structure
uncurries it to `H^q ⊗ H^p → H^r`, and the braiding restores the conventional source order. -/
noncomputable def groupCohomologyCupProduct (p q r : ℕ) (hr : r = p + q) :
    (groupCohomology (groupCohomologyTrivialIntRep G) p ⊗
        groupCohomology (groupCohomologyTrivialIntRep G) q) ⟶
      groupCohomology (groupCohomologyTrivialIntRep G) r :=
  (β_ (groupCohomology (groupCohomologyTrivialIntRep G) p)
      (groupCohomology (groupCohomologyTrivialIntRep G) q)).hom ≫
    MonoidalClosed.uncurry (groupCohomologyCupLeftDesc G p q r hr)

@[simp]
lemma groupCohomologyCupProduct_tmul (p q r : ℕ) (hr : r = p + q)
    (x : groupCohomology (groupCohomologyTrivialIntRep G) p)
    (y : groupCohomology (groupCohomologyTrivialIntRep G) q) :
    groupCohomologyCupProduct G p q r hr (x ⊗ₜ[ℤ] y) =
      (groupCohomologyCupLeftDesc G p q r hr x).hom y := by
  simp [groupCohomologyCupProduct, ModuleCat.MonoidalCategory.braiding_hom_apply,
    ModuleCat.monoidalClosed_uncurry]

/-- On classes represented by cocycles, the descended cup product is represented by the
inhomogeneous cochain cup product. -/
lemma groupCohomologyCupProduct_π_tmul_π (p q r : ℕ) (hr : r = p + q)
    (σ : groupCohomology.cocycles (groupCohomologyTrivialIntRep G) p)
    (τ : groupCohomology.cocycles (groupCohomologyTrivialIntRep G) q) :
    groupCohomologyCupProduct G p q r hr
        (groupCohomology.π (groupCohomologyTrivialIntRep G) p σ ⊗ₜ[ℤ]
          groupCohomology.π (groupCohomologyTrivialIntRep G) q τ) =
      groupCohomology.π (groupCohomologyTrivialIntRep G) r
        (groupCohomologyCupCocycleAux G p q r hr σ τ) := by
  rw [groupCohomologyCupProduct_tmul, groupCohomologyCupLeftDesc_apply_π,
    groupCohomologyCupRightDesc_apply_π]

end LeanCategories.Homological
