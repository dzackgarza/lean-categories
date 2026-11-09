/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Lattices.Valued.ReductionDiscriminant
public import LeanCategories.Lattices.Valued.IsotropicReductionDiscriminant
public import LeanCategories.Lattices.Valued.IsotropicReductionSchur
public import LeanCategories.Modules.Flags
public import Mathlib.LinearAlgebra.Matrix.SchurComplement
public import Mathlib.Data.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Adapted block data for a primitive isotropic reduction

We choose a complement `Q` of `P` in `P^⊥`, a complement `C` of `P^⊥` in `L`, and bases of the
three pieces. After nondegeneracy identifies the ranks of `P` and `C`, these give a basis of `L`
in block order `(Q, P, C)`. Its Gram matrix therefore has vanishing `P`-`P` and `P`-`Q` blocks.
-/

@[expose] public section

open LeanCategories.Modules.Bilinear.Valued

namespace LeanCategories.Lattices.Valued

universe u

variable {R : Type u} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
  [StrongRankCondition R]

attribute [local instance 10000] Submodule.module
attribute [local instance 10000] Submodule.Quotient.module
attribute [local instance 10000] Prod.instModule

/-- Bases for the three adapted pieces of an isotropic reduction. The index order is `Q`, `P`,
then `C`, with the same rank for the complementary pieces `P` and `C`. -/
structure ReductionBlockData (L : IntegralLatticeCat R)
    (D : IsotropicReductionData L) (hN : L.obj.IsSymmetric) where
  q : Submodule R L.obj.carrier
  c : Submodule R L.obj.carrier
  q_sup : q ⊔ D.submodule = D.perp
  q_inf : q ⊓ D.submodule = ⊥
  c_sup : D.perp ⊔ c = ⊤
  c_inf : D.perp ⊓ c = ⊥
  (m r : ℕ)
  qBasis : Module.Basis (Fin m) R q
  pBasis : Module.Basis (Fin r) R D.submodule
  cBasis : Module.Basis (Fin r) R c
  basis : Module.Basis (Fin m ⊕ (Fin r ⊕ Fin r)) R L.obj.carrier
  basis_q (i : Fin m) : basis (Sum.inl i) = qBasis i
  basis_p (i : Fin r) : basis (Sum.inr (Sum.inl i)) = pBasis i
  basis_c (i : Fin r) : basis (Sum.inr (Sum.inr i)) = cBasis i

/-- The adapted basis of the intermediate module `Q × P`, before identifying the two complement
ranks. -/
noncomputable def reductionIntermediateBasis {L : IntegralLatticeCat R}
    {D : IsotropicReductionData L}
    {q : Submodule R L.obj.carrier} {m r : ℕ}
    (q_sup : q ⊔ D.submodule = D.perp) (q_inf : q ⊓ D.submodule = ⊥)
    (qBasis : Module.Basis (Fin m) R q) (pBasis : Module.Basis (Fin r) R D.submodule) :
    Module.Basis (Fin m ⊕ Fin r) R D.perp :=
  (qBasis.prod pBasis).map
    (LeanCategories.Modules.prodEquivOfIsComplSup q_sup q_inf)

omit [IsDomain R] [IsPrincipalIdealRing R] [StrongRankCondition R] in
@[simp] theorem reductionIntermediateBasis_q {L : IntegralLatticeCat R}
    {D : IsotropicReductionData L}
    {q : Submodule R L.obj.carrier} {m r : ℕ}
    (q_sup : q ⊔ D.submodule = D.perp) (q_inf : q ⊓ D.submodule = ⊥)
    (qBasis : Module.Basis (Fin m) R q) (pBasis : Module.Basis (Fin r) R D.submodule)
    (i : Fin m) :
    ((reductionIntermediateBasis q_sup q_inf qBasis pBasis (Sum.inl i) : D.perp) : L.obj.carrier) =
      qBasis i := by
  simp [reductionIntermediateBasis]

omit [IsDomain R] [IsPrincipalIdealRing R] [StrongRankCondition R] in
@[simp] theorem reductionIntermediateBasis_p {L : IntegralLatticeCat R}
    {D : IsotropicReductionData L}
    {q : Submodule R L.obj.carrier} {m r : ℕ}
    (q_sup : q ⊔ D.submodule = D.perp) (q_inf : q ⊓ D.submodule = ⊥)
    (qBasis : Module.Basis (Fin m) R q) (pBasis : Module.Basis (Fin r) R D.submodule)
    (i : Fin r) :
    ((reductionIntermediateBasis q_sup q_inf qBasis pBasis (Sum.inr i) : D.perp) :
      L.obj.carrier) = pBasis i := by
  simp [reductionIntermediateBasis]

/-- Full adapted basis before the rank equality of the two complementary pieces. -/
noncomputable def reductionPreBasis {L : IntegralLatticeCat R}
    {D : IsotropicReductionData L}
    {q c : Submodule R L.obj.carrier}
    (q_sup : q ⊔ D.submodule = D.perp) (q_inf : q ⊓ D.submodule = ⊥)
    (c_sup : D.perp ⊔ c = ⊤) (c_inf : D.perp ⊓ c = ⊥)
    {m r k : ℕ}
    (qBasis : Module.Basis (Fin m) R q) (pBasis : Module.Basis (Fin r) R D.submodule)
    (cBasis : Module.Basis (Fin k) R c) :
    Module.Basis ((Fin m ⊕ Fin r) ⊕ Fin k) R L.obj.carrier :=
  ((reductionIntermediateBasis q_sup q_inf qBasis pBasis).prod cBasis).map
    ((LeanCategories.Modules.prodEquivOfIsComplSup c_sup c_inf).trans
      (LinearEquiv.ofTop (⊤ : Submodule R L.obj.carrier) rfl))

omit [IsDomain R] [IsPrincipalIdealRing R] [StrongRankCondition R] in
@[simp] theorem reductionPreBasis_q {L : IntegralLatticeCat R}
    {D : IsotropicReductionData L}
    {q c : Submodule R L.obj.carrier}
    (q_sup : q ⊔ D.submodule = D.perp) (q_inf : q ⊓ D.submodule = ⊥)
    (c_sup : D.perp ⊔ c = ⊤) (c_inf : D.perp ⊓ c = ⊥)
    {m r k : ℕ}
    (qBasis : Module.Basis (Fin m) R q) (pBasis : Module.Basis (Fin r) R D.submodule)
    (cBasis : Module.Basis (Fin k) R c) (i : Fin m) :
    reductionPreBasis q_sup q_inf c_sup c_inf qBasis pBasis cBasis (Sum.inl (Sum.inl i)) =
      qBasis i := by
  simp [reductionPreBasis]

omit [IsDomain R] [IsPrincipalIdealRing R] [StrongRankCondition R] in
@[simp] theorem reductionPreBasis_p {L : IntegralLatticeCat R}
    {D : IsotropicReductionData L}
    {q c : Submodule R L.obj.carrier}
    (q_sup : q ⊔ D.submodule = D.perp) (q_inf : q ⊓ D.submodule = ⊥)
    (c_sup : D.perp ⊔ c = ⊤) (c_inf : D.perp ⊓ c = ⊥)
    {m r k : ℕ}
    (qBasis : Module.Basis (Fin m) R q) (pBasis : Module.Basis (Fin r) R D.submodule)
    (cBasis : Module.Basis (Fin k) R c) (i : Fin r) :
    reductionPreBasis q_sup q_inf c_sup c_inf qBasis pBasis cBasis (Sum.inl (Sum.inr i)) =
      pBasis i := by
  simp [reductionPreBasis]

omit [IsDomain R] [IsPrincipalIdealRing R] [StrongRankCondition R] in
@[simp] theorem reductionPreBasis_c {L : IntegralLatticeCat R}
    {D : IsotropicReductionData L}
    {q c : Submodule R L.obj.carrier}
    (q_sup : q ⊔ D.submodule = D.perp) (q_inf : q ⊓ D.submodule = ⊥)
    (c_sup : D.perp ⊔ c = ⊤) (c_inf : D.perp ⊓ c = ⊥)
    {m r k : ℕ}
    (qBasis : Module.Basis (Fin m) R q) (pBasis : Module.Basis (Fin r) R D.submodule)
    (cBasis : Module.Basis (Fin k) R c) (i : Fin k) :
    reductionPreBasis q_sup q_inf c_sup c_inf qBasis pBasis cBasis (Sum.inr i) =
      cBasis i := by
  simp [reductionPreBasis]

/-- Nondegeneracy forces the two complementary ranks to agree. -/
theorem reduction_complement_rank {L : IntegralLatticeCat R}
    (D : IsotropicReductionData L) (hN : L.obj.IsSymmetric)
    {q c : Submodule R L.obj.carrier}
    (q_sup : q ⊔ D.submodule = D.perp) (q_inf : q ⊓ D.submodule = ⊥)
    (c_sup : D.perp ⊔ c = ⊤) (c_inf : D.perp ⊓ c = ⊥)
    {m r k : ℕ}
    (qBasis : Module.Basis (Fin m) R q) (pBasis : Module.Basis (Fin r) R D.submodule)
    (cBasis : Module.Basis (Fin k) R c) : r = k := by
  let _ : Module.Finite R c := Module.Finite.of_basis cBasis
  let _ : Module.Finite R D.submodule := Module.Finite.of_basis pBasis
  let b := reductionPreBasis q_sup q_inf c_sup c_inf qBasis pBasis cBasis
  have hq_perp (qi : Fin m) : (qBasis qi : L.obj.carrier) ∈ D.perp := by
    rw [← q_sup]
    exact Submodule.mem_sup_left (qBasis qi).2
  let pd : ↥D.submodule →ₗ[R] (↥c →ₗ[R] R) :=
    L.obj.bilinMap.compl₁₂ D.submodule.subtype c.subtype
  let cd : ↥c →ₗ[R] (↥D.submodule →ₗ[R] R) :=
    L.obj.bilinMap.compl₁₂ c.subtype D.submodule.subtype
  have hPC : Function.Injective pd := by
    intro p₁ p₂ hp
    apply Subtype.ext
    apply sub_eq_zero.mp
    apply D.nondegenerate.1
    intro y
    rw [← b.sum_repr y, map_sum]
    apply Finset.sum_eq_zero
    intro i _
    rw [map_smul]
    have hz : L.obj.pairing ((p₁ : L.obj.carrier) - p₂) (b i) = 0 := by
      cases i with
      | inl j =>
        cases j with
        | inl qi =>
          rw [show b (Sum.inl (Sum.inl qi)) = qBasis qi from
            reductionPreBasis_q q_sup q_inf c_sup c_inf qBasis pBasis cBasis qi]
          have hp₁ : L.obj.pairing (p₁ : L.obj.carrier) (qBasis qi) = 0 :=
            (L.obj.mem_orthogonalSubmodule_iff _ _).mp (hq_perp qi) _ p₁.2
          change L.obj.bilinMap (p₁ : L.obj.carrier) (qBasis qi) = 0 at hp₁
          have hp₂ : L.obj.pairing (p₂ : L.obj.carrier) (qBasis qi) = 0 :=
            (L.obj.mem_orthogonalSubmodule_iff _ _).mp (hq_perp qi) _ p₂.2
          change L.obj.bilinMap (p₂ : L.obj.carrier) (qBasis qi) = 0 at hp₂
          change L.obj.bilinMap ((p₁ : L.obj.carrier) - p₂) (qBasis qi) = 0
          rw [map_sub, LinearMap.sub_apply, hp₁, hp₂, sub_self]
        | inr pi =>
          rw [show b (Sum.inl (Sum.inr pi)) = pBasis pi from
            reductionPreBasis_p q_sup q_inf c_sup c_inf qBasis pBasis cBasis pi]
          have hp₁ := D.submodule_le_perp (pBasis pi).2
          have hz₁ := (L.obj.mem_orthogonalSubmodule_iff _ _).mp hp₁ _ p₁.2
          have hz₂ := (L.obj.mem_orthogonalSubmodule_iff _ _).mp hp₁ _ p₂.2
          change L.obj.bilinMap (p₁ : L.obj.carrier) (pBasis pi) = 0 at hz₁
          change L.obj.bilinMap (p₂ : L.obj.carrier) (pBasis pi) = 0 at hz₂
          change L.obj.bilinMap ((p₁ : L.obj.carrier) - p₂) (pBasis pi) = 0
          rw [map_sub, LinearMap.sub_apply, hz₁, hz₂, sub_self]
      | inr ci =>
        rw [show b (Sum.inr ci) = cBasis ci from
          reductionPreBasis_c q_sup q_inf c_sup c_inf qBasis pBasis cBasis ci]
        have hh := DFunLike.congr_fun hp (cBasis ci)
        change L.obj.pairing (p₁ : L.obj.carrier) (cBasis ci) =
          L.obj.pairing (p₂ : L.obj.carrier) (cBasis ci) at hh
        change L.obj.bilinMap (p₁ : L.obj.carrier) (cBasis ci) =
          L.obj.bilinMap (p₂ : L.obj.carrier) (cBasis ci) at hh
        change L.obj.pairing ((p₁ : L.obj.carrier) - p₂) (cBasis ci) = 0
        change L.obj.bilinMap ((p₁ : L.obj.carrier) - p₂) (cBasis ci) = 0
        rw [map_sub, LinearMap.sub_apply, hh, sub_self]
    have hz' : L.obj.bilinMap ((p₁ : L.obj.carrier) - p₂) (b i) = 0 := hz
    exact mul_eq_zero_of_right ((b.repr y) i) hz'
  have hCP : Function.Injective cd := by
    intro c₁ c₂ hc
    apply Subtype.ext
    apply sub_eq_zero.mp
    have hmem : ((c₁ : L.obj.carrier) - c₂) ∈ D.perp ⊓ c := by
      refine ⟨?_, c.sub_mem c₁.2 c₂.2⟩
      change ∀ p ∈ D.submodule, L.obj.pairing p ((c₁ : L.obj.carrier) - c₂) = 0
      intro p hp
      rw [hN]
      have hh := DFunLike.congr_fun hc ⟨p, hp⟩
      change L.obj.pairing (c₁ : L.obj.carrier) p = L.obj.pairing (c₂ : L.obj.carrier) p at hh
      change L.obj.bilinMap (c₁ : L.obj.carrier) p = L.obj.bilinMap (c₂ : L.obj.carrier) p at hh
      change L.obj.bilinMap ((c₁ : L.obj.carrier) - c₂) p = 0
      rw [map_sub, LinearMap.sub_apply, hh, sub_self]
    rw [c_inf] at hmem
    exact hmem
  have hrk : Module.finrank R D.submodule ≤ Module.finrank R c :=
    (LinearMap.finrank_le_finrank_of_injective (R := R) (M := ↥D.submodule)
      (M' := (↥c →ₗ[R] R)) (f := pd) hPC).trans_eq
      ((Module.finrank_eq_card_basis cBasis.dualBasis).trans
        (Module.finrank_eq_card_basis cBasis).symm)
  have hkr : Module.finrank R c ≤ Module.finrank R D.submodule :=
    (LinearMap.finrank_le_finrank_of_injective (R := R) (M := ↥c)
      (M' := (↥D.submodule →ₗ[R] R)) (f := cd) hCP).trans_eq
      ((Module.finrank_eq_card_basis pBasis.dualBasis).trans
        (Module.finrank_eq_card_basis pBasis).symm)
  rw [Module.finrank_eq_card_basis pBasis, Module.finrank_eq_card_basis cBasis] at hrk hkr
  simp [Fintype.card_fin] at hrk hkr
  exact Nat.le_antisymm hrk hkr

/-- Construct adapted block data for a primitive isotropic reduction over `R`. -/
noncomputable def reductionBlockData (L : IntegralLatticeCat R) [Module.Free R L.obj.carrier]
    (D : IsotropicReductionData L) (hN : L.obj.IsSymmetric) : ReductionBlockData L D hN := by
  letI : Module.Finite R L.obj.carrier := D.finite
  letI : Module.Projective R (L.obj.carrier ⧸ D.submodule) :=
    LeanCategories.Modules.saturatedProjective D.submodule D.primitive
  let hq := Classical.choose (LeanCategories.Modules.existsFlagComplement
    D.submodule D.perp D.submodule_le_perp)
  have hq_sup := (Classical.choose_spec (LeanCategories.Modules.existsFlagComplement
    D.submodule D.perp D.submodule_le_perp)).1
  have hq_inf := (Classical.choose_spec (LeanCategories.Modules.existsFlagComplement
    D.submodule D.perp D.submodule_le_perp)).2
  have hq_sup' : hq ⊔ D.submodule = D.perp := by rw [sup_comm]; exact hq_sup
  have hq_inf' : hq ⊓ D.submodule = ⊥ := by rw [inf_comm]; exact hq_inf
  letI : Module.Projective R (L.obj.carrier ⧸ D.perp) :=
    LeanCategories.Modules.saturatedProjective D.perp (orthogonal_isPrimitive L D.submodule)
  let c := Classical.choose (LeanCategories.Modules.existsSaturatedComplement D.perp)
  have hc_sup := (Classical.choose_spec
    (LeanCategories.Modules.existsSaturatedComplement D.perp)).1
  have hc_inf := (Classical.choose_spec
    (LeanCategories.Modules.existsSaturatedComplement D.perp)).2
  let b := Module.Free.chooseBasis R L.obj.carrier
  let qPack := Submodule.basisOfPid b hq
  let pPack := Submodule.basisOfPid b D.submodule
  let cPack := Submodule.basisOfPid b c
  let m := qPack.1
  let r := pPack.1
  let k := cPack.1
  let qBasis := qPack.2
  let pBasis := pPack.2
  let cBasis := cPack.2
  have hrk := reduction_complement_rank D hN hq_sup' hq_inf' hc_sup hc_inf qBasis pBasis cBasis
  change r = cPack.1 at hrk
  let cBasisR := cBasis.reindex (finCongr hrk.symm)
  let pre := reductionPreBasis hq_sup' hq_inf' hc_sup hc_inf qBasis pBasis cBasisR
  exact
    { q := hq
      c := c
      q_sup := hq_sup'
      q_inf := hq_inf'
      c_sup := hc_sup
      c_inf := hc_inf
      m := m
      r := r
      qBasis := qBasis
      pBasis := pBasis
      cBasis := cBasisR
      basis := pre.reindex (Equiv.sumAssoc (Fin m) (Fin r) (Fin r))
      basis_q := by
        intro i
        rw [Module.Basis.reindex_apply, Equiv.sumAssoc_symm_apply_inl]
        dsimp [pre]
        exact reductionPreBasis_q hq_sup' hq_inf' hc_sup hc_inf qBasis pBasis cBasisR i
      basis_p := by
        intro i
        rw [Module.Basis.reindex_apply, Equiv.sumAssoc_symm_apply_inr_inl]
        dsimp [pre]
        exact reductionPreBasis_p hq_sup' hq_inf' hc_sup hc_inf qBasis pBasis cBasisR i
      basis_c := by
        intro i
        rw [Module.Basis.reindex_apply, Equiv.sumAssoc_symm_apply_inr_inr]
        dsimp [pre]
        exact reductionPreBasis_c hq_sup' hq_inf' hc_sup hc_inf qBasis pBasis cBasisR i }

namespace ReductionBlockData

variable {L : IntegralLatticeCat ℤ} {D : IsotropicReductionData L} {hN : L.obj.IsSymmetric}
  (B : ReductionBlockData L D hN)

/-- The quotient complement lies in the orthogonal of the primitive isotropic submodule. -/
theorem q_le_perp : B.q ≤ D.perp := by
  intro x hx
  rw [← B.q_sup]
  exact Submodule.mem_sup_left hx

/-- The map from the quotient complement to `P^⊥/P`. -/
noncomputable def quotientLinear : ↥B.q →ₗ[ℤ] (D.reduction hN).carrier where
  toFun x := Submodule.Quotient.mk (⟨x, B.q_le_perp x.2⟩ : D.perp)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem quotientLinear_apply (x : ↥B.q) :
    B.quotientLinear x = Submodule.Quotient.mk (⟨x, B.q_le_perp x.2⟩ : D.perp) := rfl

/-- The quotient complement maps bijectively onto `P^⊥/P`. -/
noncomputable def quotientEquiv : ↥B.q ≃ₗ[ℤ] (D.reduction hN).carrier := by
  apply LinearEquiv.ofBijective B.quotientLinear
  constructor
  · intro x y hxy
    apply Subtype.ext
    apply sub_eq_zero.mp
    have hk : B.quotientLinear (x - y) = 0 := by rw [map_sub, hxy, sub_self]
    have hmem : (⟨x - y, B.q_le_perp (B.q.sub_mem x.2 y.2)⟩ : D.perp) ∈
      D.kernel := by
      exact (Submodule.Quotient.mk_eq_zero _).mp hk
    have hP : ((x : L.obj.carrier) - y) ∈ D.submodule :=
      (IsotropicReductionData.mem_kernel_iff (D := D) _).mp hmem
    have hmem' : ((x : L.obj.carrier) - y) ∈ B.q ⊓ D.submodule :=
      ⟨B.q.sub_mem x.2 y.2, hP⟩
    simpa only [B.q_inf, Submodule.mem_bot] using hmem'
  · intro q
    induction q using Submodule.Quotient.induction_on with
    | _ w =>
      have hw' : (w : L.obj.carrier) ∈ B.q ⊔ D.submodule := by
        rw [B.q_sup]
        exact w.2
      obtain ⟨x, hx, p, hp, hw⟩ := Submodule.mem_sup.mp hw'
      refine ⟨⟨x, hx⟩, ?_⟩
      apply (Submodule.Quotient.eq _).mpr
      apply (IsotropicReductionData.mem_kernel_iff (D := D) _).mpr
      have hP : x - (w : L.obj.carrier) ∈ D.submodule := by
        rw [← hw]
        have heq : x - (x + p) = -p := by abel
        rw [heq]
        exact D.submodule.neg_mem hp
      simpa only [Submodule.coe_sub, Submodule.coe_mk] using hP

@[simp] theorem quotientEquiv_apply (x : ↥B.q) :
    B.quotientEquiv x = B.quotientLinear x := by
  change B.quotientLinear x = B.quotientLinear x
  rfl

/-- The induced basis of the reduced lattice. -/
noncomputable def reductionBasis : Module.Basis (Fin B.m) ℤ
    (D.reduction hN).carrier :=
  B.qBasis.map B.quotientEquiv

@[simp] theorem reductionBasis_apply (i : Fin B.m) :
    B.reductionBasis i = B.quotientEquiv (B.qBasis i) := rfl

/-- The `Q`-`P`- and `P`-`P` entries of the adapted Gram matrix vanish. -/
theorem pairing_p_q (i : Fin B.r) (j : Fin B.m) :
    L.obj.pairing (B.pBasis i) (B.qBasis j) = 0 := by
  have hp := B.q_le_perp (B.qBasis j).2
  exact (L.obj.mem_orthogonalSubmodule_iff _ _).mp hp _ (B.pBasis i).2

/-- The `Q`-`P` Gram entries vanish by symmetry. -/
theorem pairing_q_p (i : Fin B.m) (j : Fin B.r) :
    L.obj.pairing (B.qBasis i) (B.pBasis j) = 0 := by
  rw [hN]
  exact B.pairing_p_q j i

/-- Two vectors of the primitive isotropic submodule pair to zero. -/
theorem pairing_p_p (i j : Fin B.r) :
    L.obj.pairing (B.pBasis i) (B.pBasis j) = 0 := by
  have hp := D.submodule_le_perp (B.pBasis i).2
  rw [hN]
  exact (L.obj.mem_orthogonalSubmodule_iff _ _).mp hp _ (B.pBasis j).2

/-- The duality block between `P` and its complement. -/
noncomputable def dualityMatrix : Matrix (Fin B.r) (Fin B.r) ℤ :=
  fun i j => L.obj.pairing (B.pBasis i) (B.cBasis j)

/-- The cross terms between the two quotient-type complements. -/
noncomputable def crossMatrix : Matrix (Fin B.m) (Fin B.r) ℤ :=
  fun i j => L.obj.pairing (B.qBasis i) (B.cBasis j)

/-- The quadratic block on the complement of `P^⊥`. -/
noncomputable def complementMatrix : Matrix (Fin B.r) (Fin B.r) ℤ :=
  fun i j => L.obj.pairing (B.cBasis i) (B.cBasis j)

/-- The Gram inheritance from the quotient-complement basis to the reduced basis. -/
theorem pairing_reduction (i j : Fin B.m) :
    (D.reduction hN).pairing (B.reductionBasis i) (B.reductionBasis j) =
      L.obj.pairing (B.qBasis i) (B.qBasis j) := by
  simp [reductionBasis_apply, quotientEquiv_apply, quotientLinear_apply, D.reduction_pairing_mk]

/-- The duality block between `P` and its complement, with rational entries. -/
noncomputable def dualityMatrixQ : Matrix (Fin B.r) (Fin B.r) ℚ :=
  B.dualityMatrix.map (Int.castRingHom ℚ)

/-- The reduced Gram matrix, with rational entries. -/
noncomputable def reductionGramMatrixQ : Matrix (Fin B.m) (Fin B.m) ℚ :=
  (gramMatrix (D.reductionLattice hN) B.reductionBasis).map (Int.castRingHom ℚ)

/-- The cross terms between the two quotient-type complements, with rational entries. -/
noncomputable def crossMatrixQ : Matrix (Fin B.m) (Fin B.r) ℚ :=
  B.crossMatrix.map (Int.castRingHom ℚ)

/-- The quadratic block on the complement of `P^⊥`, with rational entries. -/
noncomputable def complementMatrixQ : Matrix (Fin B.r) (Fin B.r) ℚ :=
  B.complementMatrix.map (Int.castRingHom ℚ)

/-- The adapted Gram matrix in Schur form. -/
noncomputable def blockGramMatrix : Matrix (Fin B.m ⊕ (Fin B.r ⊕ Fin B.r))
    (Fin B.m ⊕ (Fin B.r ⊕ Fin B.r)) ℚ :=
  Schur.blockGram B.dualityMatrixQ B.reductionGramMatrixQ B.crossMatrixQ B.complementMatrixQ

/-- The adapted Gram matrix really is the Schur block data. -/
theorem blockGramMatrix_eq_gramMatrix :
    B.blockGramMatrix = (gramMatrix L B.basis).map (Int.castRingHom ℚ) := by
  ext (i | pi | ci) (j | pj | cj)
  · change B.reductionGramMatrixQ i j =
      ((gramMatrix L B.basis).map (Int.castRingHom ℚ)) (Sum.inl i) (Sum.inl j)
    simp [reductionGramMatrixQ, gramMatrix, B.basis_q, Matrix.map_apply, BilinModuleCat.bilinMap_apply]
    exact (LinearMap.BilinForm.toMatrix_apply B.reductionBasis (D.reduction hN).bilinMap i j).trans
      (B.pairing_reduction i j)
  · change (0 : ℚ) =
      ((gramMatrix L B.basis).map (Int.castRingHom ℚ)) (Sum.inl i) (Sum.inr (Sum.inl pj))
    simp [gramMatrix, LinearMap.BilinForm.toMatrix_apply, B.basis_p, B.basis_q]
    simpa using congrArg (fun z : ℤ => (z : ℚ)) (B.pairing_q_p i pj).symm
  · change (B.crossMatrixQ i cj : ℚ) =
      ((gramMatrix L B.basis).map (Int.castRingHom ℚ)) (Sum.inl i) (Sum.inr (Sum.inr cj))
    simp [crossMatrixQ, crossMatrix, gramMatrix, LinearMap.BilinForm.toMatrix_apply,
      B.basis_q, B.basis_c]
  · change (0 : ℚ) =
      ((gramMatrix L B.basis).map (Int.castRingHom ℚ)) (Sum.inr (Sum.inl pi)) (Sum.inl j)
    simp [gramMatrix, LinearMap.BilinForm.toMatrix_apply, B.basis_p, B.basis_q]
    simpa using congrArg (fun z : ℤ => (z : ℚ)) (B.pairing_p_q pi j).symm
  · change (0 : ℚ) =
      ((gramMatrix L B.basis).map (Int.castRingHom ℚ))
        (Sum.inr (Sum.inl pi)) (Sum.inr (Sum.inl pj))
    simp [gramMatrix, LinearMap.BilinForm.toMatrix_apply, B.basis_p, B.pairing_p_p]
  · change (B.dualityMatrixQ pi cj : ℚ) =
      ((gramMatrix L B.basis).map (Int.castRingHom ℚ))
        (Sum.inr (Sum.inl pi)) (Sum.inr (Sum.inr cj))
    simp [dualityMatrixQ, dualityMatrix, gramMatrix, LinearMap.BilinForm.toMatrix_apply,
      B.basis_p, B.basis_c, Matrix.map_apply, BilinModuleCat.bilinMap_apply]
  · change (B.crossMatrixQ j ci : ℚ) =
      ((gramMatrix L B.basis).map (Int.castRingHom ℚ)) (Sum.inr (Sum.inr ci)) (Sum.inl j)
    simp [crossMatrixQ, crossMatrix, gramMatrix, LinearMap.BilinForm.toMatrix_apply,
      B.basis_q, B.basis_c, Matrix.map_apply, BilinModuleCat.bilinMap_apply]
    exact hN _ _
  · change (B.dualityMatrixQ pj ci : ℚ) =
      ((gramMatrix L B.basis).map (Int.castRingHom ℚ))
        (Sum.inr (Sum.inr ci)) (Sum.inr (Sum.inl pj))
    simp [dualityMatrixQ, dualityMatrix, gramMatrix, LinearMap.BilinForm.toMatrix_apply,
      B.basis_p, B.basis_c, Matrix.map_apply, BilinModuleCat.bilinMap_apply]
    exact hN _ _
  · change (B.complementMatrixQ ci cj : ℚ) =
      ((gramMatrix L B.basis).map (Int.castRingHom ℚ))
        (Sum.inr (Sum.inr ci)) (Sum.inr (Sum.inr cj))
    simp [complementMatrixQ, complementMatrix, gramMatrix, LinearMap.BilinForm.toMatrix_apply,
      B.basis_c]

/-- The reduced Gram determinant is nonzero, so the Schur complement exists. -/
theorem reductionGramMatrixQ_det_ne_zero : B.reductionGramMatrixQ.det ≠ 0 := by
  have hQ := D.reductionLattice_isFractionFieldPerfect hN
  have hZ : (gramMatrix (D.reductionLattice hN) B.reductionBasis).det ≠ 0 :=
    (isFractionFieldPerfect_iff_determinant_ne_zero ℤ (D.reductionLattice hN)
      B.reductionBasis).mp hQ
  have hc : B.reductionGramMatrixQ.det =
      ((gramMatrix (D.reductionLattice hN) B.reductionBasis).det : ℚ) := by
    rw [reductionGramMatrixQ]
    exact (RingHom.map_det (Int.castRingHom ℚ) _).symm
  rw [hc]
  exact_mod_cast hZ

/-- The absolute determinant splits into the reduced factor and the square of the level block. -/
theorem abs_det_blockGramMatrix :
    |B.blockGramMatrix.det| = |B.reductionGramMatrixQ.det| *
      (|B.dualityMatrixQ.det| * |B.dualityMatrixQ.det|) :=
  Schur.abs_det_blockGram B.dualityMatrixQ B.reductionGramMatrixQ B.crossMatrixQ
    B.complementMatrixQ B.reductionGramMatrixQ_det_ne_zero

end ReductionBlockData

end LeanCategories.Lattices.Valued
