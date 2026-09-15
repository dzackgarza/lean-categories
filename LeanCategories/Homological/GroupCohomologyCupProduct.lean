/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality
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

end LeanCategories.Homological
