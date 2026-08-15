/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Lattices.Valued.Jordan
public import LeanCategories.Lattices.Valued.OrthogonalSummand
public import Mathlib.LinearAlgebra.TensorProduct.Prod

@[expose] public section

open CategoryTheory
open LeanCategories.Modules.Bilinear.Valued

namespace LeanCategories.Lattices.Valued

universe u

variable {R : Type u} [CommRing R]

section Scale

/-- A sublattice has a smaller scale than the ambient lattice.

Every pairing of two elements of the sublattice is a pairing in `L`, and the scale is the
span of all pairings. -/
theorem scaleIdeal_formedSublattice_le (L : IntegralLatticeCat R)
    (P : Submodule R L.obj.carrier) [Module.Projective R ↥P] :
    scaleIdeal (formedSublattice L P) ≤ scaleIdeal L := by
  rw [← isIIntegral_iff_scaleIdeal_le, isIIntegral_iff_pairing_mem]
  intro x y
  exact pairing_mem_scaleIdeal L x.1 y.1

/-- The scale of an orthogonal complement is contained in the scale of the lattice.

This is the ordering input of the Jordan recursion: peeling a line off `L` can only shrink
the scale, so the exponents produced by repeated splitting do not decrease. -/
theorem scaleIdeal_orthogonalComplement_le (L : IntegralLatticeCat R)
    (P : Submodule R L.obj.carrier)
    [Module.Projective R ↥(orthogonalSubmodule L P)] :
    scaleIdeal (orthogonalComplement L P) ≤ scaleIdeal L :=
  scaleIdeal_formedSublattice_le L (orthogonalSubmodule L P)

end Scale

section Dual

/-- The canonical map into the rational span is tensoring with `1`. -/
@[simp]
theorem toRationalSpan_apply (L : IntegralLatticeCat R) (y : L.obj.carrier) :
    toRationalSpan R L y = (1 : FractionRing R) ⊗ₜ[R] y :=
  rfl

variable (L₁ L₂ : IntegralLatticeCat R)

/-- The rational span of an orthogonal sum splits as a product of rational spans. -/
noncomputable def rationalSpanProdEquiv :
    RationalSpan R (orthogonalSum L₁ L₂) ≃ₗ[R]
      RationalSpan R L₁ × RationalSpan R L₂ :=
  TensorProduct.prodRight R R (FractionRing R) L₁.obj.carrier L₂.obj.carrier

@[simp]
theorem rationalSpanProdEquiv_tmul (a : FractionRing R)
    (x : L₁.obj.carrier × L₂.obj.carrier) :
    rationalSpanProdEquiv L₁ L₂ (a ⊗ₜ[R] x) = (a ⊗ₜ[R] x.1, a ⊗ₜ[R] x.2) :=
  TensorProduct.prodRight_tmul R R (FractionRing R) L₁.obj.carrier L₂.obj.carrier a x

/-- The rationalized form of an orthogonal sum is the sum of the rationalized forms. -/
theorem rationalizedForm_orthogonalSum (z : RationalSpan R (orthogonalSum L₁ L₂))
    (y : (orthogonalSum L₁ L₂).obj.carrier) :
    rationalizedForm R (orthogonalSum L₁ L₂) z (toRationalSpan R (orthogonalSum L₁ L₂) y) =
      rationalizedForm R L₁ (rationalSpanProdEquiv L₁ L₂ z).1
          (toRationalSpan R L₁ y.1) +
        rationalizedForm R L₂ (rationalSpanProdEquiv L₁ L₂ z).2
          (toRationalSpan R L₂ y.2) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
    simp only [rationalSpanProdEquiv_tmul, toRationalSpan_apply, rationalizedForm_tmul,
      orthogonalSum_pairing, map_add]
    ring
  | add z w hz hw =>
    simp only [map_add, LinearMap.add_apply, Prod.fst_add, Prod.snd_add, hz, hw]
    ring

/-- The metric dual of an orthogonal sum is the orthogonal sum of the metric duals. -/
theorem fractionalIdealDual_orthogonalSum (I : FractionalRIdeal R) :
    fractionalIdealDual R (orthogonalSum L₁ L₂) I =
      Submodule.comap (rationalSpanProdEquiv L₁ L₂).toLinearMap
        ((fractionalIdealDual R L₁ I).prod (fractionalIdealDual R L₂ I)) := by
  refine Submodule.ext fun z ↦ ?_
  rw [Submodule.mem_comap, Submodule.mem_prod, mem_fractionalIdealDual_iff,
    mem_fractionalIdealDual_iff, mem_fractionalIdealDual_iff]
  constructor
  · refine fun h ↦ ⟨fun y₁ ↦ ?_, fun y₂ ↦ ?_⟩
    · have hy := h ((y₁, 0) : L₁.obj.carrier × L₂.obj.carrier)
      rw [rationalizedForm_orthogonalSum] at hy
      simpa using hy
    · have hy := h ((0, y₂) : L₁.obj.carrier × L₂.obj.carrier)
      rw [rationalizedForm_orthogonalSum] at hy
      simpa using hy
  · rintro ⟨h₁, h₂⟩ y
    rw [rationalizedForm_orthogonalSum, ← FractionalIdeal.mem_coe]
    exact Submodule.add_mem _ (FractionalIdeal.mem_coe.mpr (h₁ y.1))
      (FractionalIdeal.mem_coe.mpr (h₂ y.2))

/-- The integral image of an orthogonal sum is the product of the integral images. -/
theorem integralImage_orthogonalSum :
    integralImage R (orthogonalSum L₁ L₂) =
      Submodule.comap (rationalSpanProdEquiv L₁ L₂).toLinearMap
        ((integralImage R L₁).prod (integralImage R L₂)) := by
  refine Submodule.ext fun z ↦ ?_
  rw [Submodule.mem_comap, Submodule.mem_prod]
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨⟨y.1, by simp⟩, ⟨y.2, by simp⟩⟩
  · rintro ⟨⟨y₁, hy₁⟩, ⟨y₂, hy₂⟩⟩
    refine ⟨((y₁, y₂) : L₁.obj.carrier × L₂.obj.carrier), ?_⟩
    refine (rationalSpanProdEquiv L₁ L₂).injective ?_
    rw [toRationalSpan_apply, rationalSpanProdEquiv_tmul]
    exact Prod.ext hy₁ hy₂

/-- An orthogonal sum of fractional-`I`-modular lattices is fractional-`I`-modular. -/
theorem isFractionalIModular_orthogonalSum (I : FractionalRIdeal R)
    (h₁ : IsFractionalIModular R L₁ I) (h₂ : IsFractionalIModular R L₂ I) :
    IsFractionalIModular R (orthogonalSum L₁ L₂) I := by
  change fractionalIdealDual R (orthogonalSum L₁ L₂) I
    = integralImage R (orthogonalSum L₁ L₂)
  rw [fractionalIdealDual_orthogonalSum, integralImage_orthogonalSum, h₁, h₂]

/-- An orthogonal sum of `I`-modular lattices is `I`-modular.

This is the merge step of the Jordan recursion: lines of equal scale exponent are bundled
into a single modular component. -/
theorem isIModular_orthogonalSum (I : Ideal R)
    (h₁ : IsIModular R L₁ I) (h₂ : IsIModular R L₂ I) :
    IsIModular R (orthogonalSum L₁ L₂) I :=
  isFractionalIModular_orthogonalSum L₁ L₂ (integralFractionalIdeal R I) h₁ h₂

end Dual

section Assembly

variable {W : Type u} [AddCommGroup W] [Module R W]

/-- Build an isomorphism of finite projective lattices from a form-preserving equivalence. -/
noncomputable def finiteProjectiveLatticeIsoMk {L M : FiniteProjectiveLatticeCat R W}
    (f : L.obj.obj.carrier ≃ₗ[R] M.obj.obj.carrier)
    (h : ∀ x y, M.obj.obj.pairing (f x) (f y) = L.obj.obj.pairing x y) : L ≅ M :=
  ObjectProperty.isoMk (P := isFiniteProjectiveLattice R W)
    (ObjectProperty.isoMk (P := isLattice R W) (BilinModuleCat.isoMk f h))

/-- The carrier equivalence underlying an isomorphism of finite projective lattices. -/
noncomputable def finiteProjectiveLatticeLinearEquiv
    {L M : FiniteProjectiveLatticeCat R W} (e : L ≅ M) :
    L.obj.obj.carrier ≃ₗ[R] M.obj.obj.carrier :=
  BilinModuleCat.linearEquivOfIso
    ((ObjectProperty.ι (isLattice R W)).mapIso
      ((ObjectProperty.ι (isFiniteProjectiveLattice R W)).mapIso e))

/-- Isomorphisms of finite projective lattices preserve the pairing. -/
theorem finiteProjectiveLatticeLinearEquiv_pairing
    {L M : FiniteProjectiveLatticeCat R W} (e : L ≅ M) (x y : L.obj.obj.carrier) :
    M.obj.obj.pairing (finiteProjectiveLatticeLinearEquiv e x)
        (finiteProjectiveLatticeLinearEquiv e y) = L.obj.obj.pairing x y :=
  BilinModuleCat.linearEquivOfIso_pairing _ x y

/-- Orthogonal sums respect isomorphisms in each argument. -/
noncomputable def finiteProjectiveOrthogonalSumCongr
    {A A' B B' : FiniteProjectiveLatticeCat R W} (eA : A ≅ A') (eB : B ≅ B') :
    finiteProjectiveOrthogonalSum A B ≅ finiteProjectiveOrthogonalSum A' B' :=
  finiteProjectiveLatticeIsoMk
    ((finiteProjectiveLatticeLinearEquiv eA).prodCongr
      (finiteProjectiveLatticeLinearEquiv eB))
    fun x y ↦ congrArg₂ (· + ·)
      (finiteProjectiveLatticeLinearEquiv_pairing eA x.1 y.1)
      (finiteProjectiveLatticeLinearEquiv_pairing eB x.2 y.2)

/-- Orthogonal sums are associative. -/
noncomputable def finiteProjectiveOrthogonalSumAssoc
    (A B C : FiniteProjectiveLatticeCat R W) :
    finiteProjectiveOrthogonalSum A (finiteProjectiveOrthogonalSum B C) ≅
      finiteProjectiveOrthogonalSum (finiteProjectiveOrthogonalSum A B) C :=
  finiteProjectiveLatticeIsoMk
    (LinearEquiv.prodAssoc R A.obj.obj.carrier B.obj.obj.carrier C.obj.obj.carrier).symm
    fun _ _ ↦ add_assoc _ _ _

/-- An indexed orthogonal sum splits off its first summand. -/
noncomputable def finiteProjectiveIndexedOrthogonalSumConsIso {n : ℕ}
    (D : Fin (n + 1) → FiniteProjectiveLatticeCat R W) :
    finiteProjectiveIndexedOrthogonalSum D ≅
      finiteProjectiveOrthogonalSum (D 0)
        (finiteProjectiveIndexedOrthogonalSum fun i : Fin n ↦ D i.succ) :=
  finiteProjectiveLatticeIsoMk
    (Fin.consLinearEquiv R fun i ↦ (D i).obj.obj.carrier).symm
    fun x y ↦ (Fin.sum_univ_succ (f := fun i : Fin (n + 1) ↦
      (D i).obj.obj.pairing (x i) (y i))).symm

/-- The orthogonal sum of an empty family is isomorphic to a lattice of rank zero. -/
noncomputable def emptyOrthogonalSumIso (L : FiniteProjectiveLatticeCat R W)
    [Subsingleton L.obj.obj.carrier] :
    finiteProjectiveIndexedOrthogonalSum (fun _ : Fin 0 ↦ L) ≅ L := by
  letI : Subsingleton
      ((finiteProjectiveIndexedOrthogonalSum (fun _ : Fin 0 ↦ L)).obj.obj.carrier) := by
    change Subsingleton ((_ : Fin 0) → L.obj.obj.carrier)
    infer_instance
  refine finiteProjectiveLatticeIsoMk (LinearEquiv.ofSubsingleton _ _) fun x y ↦ ?_
  rw [Subsingleton.elim (LinearEquiv.ofSubsingleton _ L.obj.obj.carrier x) 0,
    BilinModuleCat.pairing_zero_left]
  change (0 : W) = ∑ i : Fin 0, L.obj.obj.pairing (x i) (y i)
  simp

/-- Prepending a smaller value to a strictly monotone family keeps it strictly monotone. -/
theorem strictMono_fin_cons {n : ℕ} (a : ℕ) (f : Fin n → ℕ) (hf : StrictMono f)
    (h : ∀ i, a < f i) : StrictMono (Fin.cons a f : Fin (n + 1) → ℕ) := by
  intro i j hij
  rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨k, rfl⟩
  · rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨l, rfl⟩
    · exact absurd hij (lt_irrefl _)
    · simpa using h l
  · rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨l, rfl⟩
    · exact absurd hij (Fin.not_lt_zero _)
    · simpa using hf (Fin.succ_lt_succ_iff.mp hij)

end Assembly

section Nondegeneracy

/-- An orthogonal complement of a complemented sublattice inherits nondegeneracy.

A vector of the complement orthogonal to the whole complement is also orthogonal to the
sublattice, hence to the whole lattice. -/
theorem isNondegenerate_orthogonalComplement (L : IntegralLatticeCat R)
    (P : Submodule R L.obj.carrier)
    [Module.Projective R ↥(orthogonalSubmodule L P)]
    (hcompl : IsCompl P (orthogonalSubmodule L P))
    (hL : L.obj.IsNondegenerate) :
    (orthogonalComplement L P).obj.IsNondegenerate := by
  refine ((orthogonalComplement L P).obj.isNondegenerate_iff_adjoint_injective_of_isSymmetric
    (orthogonalComplement L P).property.2).mpr ?_
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro x hx
  have hx' : ∀ y : ↥(orthogonalSubmodule L P), L.obj.pairing x.1 y.1 = 0 := fun y ↦
    LinearMap.congr_fun (LinearMap.mem_ker.mp hx) y
  have hzero : ∀ z : L.obj.carrier, L.obj.pairing x.1 z = 0 := by
    intro z
    have hz : z ∈ P ⊔ orthogonalSubmodule L P := hcompl.sup_eq_top ▸ Submodule.mem_top
    obtain ⟨p, hp, q, hq, rfl⟩ := Submodule.mem_sup.mp hz
    rw [BilinModuleCat.pairing_add_right, L.property.2 x.1 p,
      (mem_orthogonalSubmodule_iff L P x.1).mp x.2 p hp, hx' ⟨q, hq⟩, add_zero]
  have hmem : x.1 ∈ LinearMap.ker L.obj.adjoint := LinearMap.ext hzero
  have hxadj : L.obj.adjoint x.1 = 0 := LinearMap.mem_ker.mp hmem
  have hxzero : (x.1 : L.obj.carrier) = 0 :=
    (L.obj.isNondegenerate_iff_adjoint_injective_of_isSymmetric L.property.2).mp hL (by
      rw [map_zero]
      exact hxadj)
  exact Subtype.ext hxzero

/-- A nondegenerate lattice with trivial scale has no nonzero vectors. -/
theorem subsingleton_of_scaleIdeal_eq_bot (L : IntegralLatticeCat R)
    (hL : L.obj.IsNondegenerate) (h : scaleIdeal L = ⊥) :
    Subsingleton L.obj.carrier := by
  have hzero : ∀ z : L.obj.carrier, z = 0 := by
    intro z
    refine (L.obj.isNondegenerate_iff_adjoint_injective_of_isSymmetric L.property.2).mp hL
      (LinearMap.ext fun w ↦ ?_)
    have hmem : L.obj.pairing z w ∈ scaleIdeal L := pairing_mem_scaleIdeal L z w
    rw [h] at hmem
    have hpair : L.obj.pairing z w = 0 := hmem
    simpa using hpair
  exact ⟨fun x y ↦ by rw [hzero x, hzero y]⟩

end Nondegeneracy

section Recursion

variable [IsDomain R] [IsDiscreteValuationRing R]

/-- A lattice with no nonzero vectors is the empty orthogonal sum. -/
noncomputable def subsingletonJordanDecomposition (L : FiniteProjectiveLatticeCat R R)
    [Subsingleton L.obj.obj.carrier] (π : R) (hπ : Irreducible π) :
    JordanDecomposition L π 0 where
  uniformizer_isIrreducible := hπ
  component := fun _ ↦ L
  exponent := fun _ ↦ 0
  component_isModular := fun i ↦ i.elim0
  component_nontrivial := fun i ↦ i.elim0
  exponent_strictMono := fun i ↦ i.elim0
  decomposition := emptyOrthogonalSumIso L

variable [Invertible (2 : R)]

/-- The Jordan recursion, with a lower bound on the exponents.

The bound is what keeps the exponents strictly increasing: the line peeled off a lattice
carries its whole scale, so every component of the orthogonal complement has a larger
exponent, and components of equal exponent are merged. -/
theorem exists_jordanDecomposition_of_finrank_le (π : R) (hπ : Irreducible π) :
    ∀ (k : ℕ) (L : FiniteProjectiveLatticeCat R R),
      Module.finrank R L.obj.obj.carrier ≤ k →
      L.obj.obj.IsNondegenerate →
      ∀ e : ℕ, scaleIdeal L.obj ≤ Ideal.span {π ^ e} →
        ∃ (n : ℕ) (J : JordanDecomposition L π n), ∀ i, e ≤ J.exponent i := by
  intro k
  induction k with
  | zero =>
    intro L hrank _ _ _
    letI : Module.Finite R L.obj.obj.carrier := L.property
    letI : Module.Free R L.obj.obj.carrier := L.carrier_free
    letI : Subsingleton L.obj.obj.carrier :=
      Module.finrank_zero_iff.mp (Nat.le_zero.mp hrank)
    exact ⟨0, subsingletonJordanDecomposition L π hπ, fun i ↦ i.elim0⟩
  | succ k ih =>
    intro L hrank hnd e he
    by_cases hbot : scaleIdeal L.obj = ⊥
    · letI : Subsingleton L.obj.obj.carrier :=
        subsingleton_of_scaleIdeal_eq_bot L.obj hnd hbot
      exact ⟨0, subsingletonJordanDecomposition L π hπ, fun i ↦ i.elim0⟩
    letI : Module.Finite R L.obj.obj.carrier := L.property
    obtain ⟨v, e₀, hline, hperp, hscale, hmod, hrk, hcompl⟩ :=
      exists_orthogonal_decomposition L.obj hbot π hπ
    letI := hline
    letI := hperp
    letI hfin : Module.Finite R ↥(R ∙ v) :=
      Module.Finite.iff_fg.mpr (Submodule.fg_span_singleton v)
    have hspan_ne : (R ∙ v) ≠ ⊥ := by
      intro h0
      rw [h0] at hrk hcompl
      have hsup : orthogonalSubmodule L.obj ⊥ = ⊤ := by
        simpa using hcompl.sup_eq_top
      rw [hsup, finrank_top] at hrk
      omega
    letI hline_nontrivial : Nontrivial ↥(R ∙ v) :=
      Submodule.nontrivial_iff_ne_bot.mpr hspan_ne
    let A : FiniteProjectiveLatticeCat R R :=
      ⟨formedSublattice L.obj (R ∙ v), hfin⟩
    have hBfin : Module.Finite R ↥(orthogonalSubmodule L.obj (R ∙ v)) := inferInstance
    let B : FiniteProjectiveLatticeCat R R :=
      ⟨orthogonalComplement L.obj (R ∙ v), hBfin⟩
    have hAB : finiteProjectiveOrthogonalSum A B ≅ L :=
      ObjectProperty.isoMk (P := isFiniteProjectiveLattice R R)
        (sublatticeOrthogonalSumIso L.obj (R ∙ v) hcompl)
    have hee₀ : e ≤ e₀ := by
      rw [hscale] at he
      exact (pow_dvd_pow_iff hπ.ne_zero hπ.not_isUnit).mp
        (Ideal.span_singleton_le_span_singleton.mp he)
    have hBrank : Module.finrank R B.obj.obj.carrier ≤ k := by
      change Module.finrank R ↥(orthogonalSubmodule L.obj (R ∙ v)) ≤ k
      omega
    have hBnd : B.obj.obj.IsNondegenerate :=
      isNondegenerate_orthogonalComplement L.obj (R ∙ v) hcompl hnd
    have hBscale : scaleIdeal B.obj ≤ Ideal.span {π ^ e₀} := by
      rw [← hscale]
      exact scaleIdeal_orthogonalComplement_le L.obj (R ∙ v)
    obtain ⟨n, J, hJ⟩ := ih B hBrank hBnd e₀ hBscale
    by_cases hlt : ∀ i, e₀ < J.exponent i
    · refine ⟨n + 1, ?_, ?_⟩
      · refine
          { uniformizer_isIrreducible := hπ
            component := Fin.cons A J.component
            exponent := Fin.cons e₀ J.exponent
            component_isModular := ?_
            component_nontrivial := ?_
            exponent_strictMono :=
              strictMono_fin_cons e₀ J.exponent J.exponent_strictMono hlt
            decomposition :=
              finiteProjectiveIndexedOrthogonalSumConsIso (Fin.cons A J.component) ≪≫
                finiteProjectiveOrthogonalSumCongr (Iso.refl A) J.decomposition ≪≫ hAB }
        · intro i
          rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩
          · exact hmod
          · exact J.component_isModular j
        · intro i
          rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩
          · exact hline_nontrivial
          · exact J.component_nontrivial j
      · intro i
        rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩
        · exact hee₀
        · exact hee₀.trans (hJ j)
    · push Not at hlt
      obtain ⟨i₀, hi₀⟩ := hlt
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := by
        cases n with
        | zero => exact Fin.elim0 i₀
        | succ m => exact ⟨m, rfl⟩
      have hzero : J.exponent 0 = e₀ :=
        le_antisymm ((J.exponent_strictMono.monotone (Fin.zero_le i₀)).trans hi₀) (hJ 0)
      refine ⟨m + 1, ?_, ?_⟩
      · refine
          { uniformizer_isIrreducible := hπ
            component := Fin.cons (finiteProjectiveOrthogonalSum A (J.component 0))
              fun i : Fin m ↦ J.component i.succ
            exponent := J.exponent
            component_isModular := ?_
            component_nontrivial := ?_
            exponent_strictMono := J.exponent_strictMono
            decomposition :=
              finiteProjectiveIndexedOrthogonalSumConsIso _ ≪≫
                (finiteProjectiveOrthogonalSumAssoc A (J.component 0)
                  (finiteProjectiveIndexedOrthogonalSum fun i : Fin m ↦
                    J.component i.succ)).symm ≪≫
                  finiteProjectiveOrthogonalSumCongr (Iso.refl A)
                    ((finiteProjectiveIndexedOrthogonalSumConsIso J.component).symm ≪≫
                      J.decomposition) ≪≫ hAB }
        · intro i
          rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩
          · rw [hzero]
            exact isIModular_orthogonalSum A.obj (J.component 0).obj _ hmod
              (hzero ▸ J.component_isModular 0)
          · exact J.component_isModular j.succ
        · intro i
          rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩
          · letI := J.component_nontrivial 0
            change Nontrivial (A.obj.obj.carrier × (J.component 0).obj.obj.carrier)
            infer_instance
          · exact J.component_nontrivial j.succ
      · exact fun i ↦ hee₀.trans (hJ i)

/-- Every nondegenerate finite lattice over a discrete valuation ring with `2` invertible
has a Jordan decomposition. -/
theorem exists_jordanDecomposition (L : FiniteProjectiveLatticeCat R R)
    (hnd : L.obj.obj.IsNondegenerate) (π : R) (hπ : Irreducible π) :
    HasJordanDecomposition L := by
  obtain ⟨n, J, _⟩ := exists_jordanDecomposition_of_finrank_le π hπ
    (Module.finrank R L.obj.obj.carrier) L le_rfl hnd 0
    (by simp)
  exact ⟨π, n, ⟨J⟩⟩

end Recursion

end LeanCategories.Lattices.Valued
