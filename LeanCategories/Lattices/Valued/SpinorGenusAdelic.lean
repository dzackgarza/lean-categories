/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Lattices.Valued.LocalGlobal
public import LeanCategories.Lattices.Valued.ReflectionGeneration

/-!
# The spinor genus on the adelic genus

The genus of `LocalGlobal.lean` is the ring-adelic genus. This file refines it to the spinor
genus: two lattices in one genus lie in one spinor genus when the local isometries can be
chosen to differ from a single rational isometry by elements of the local spinor kernel.

The spinor kernel used here is the subgroup of products of reflections whose values multiply
to a square. That subgroup needs no spinor norm, so the definition of the spinor genus makes
no choice at any place. When a spinor norm exists it is unique, and the subgroup is exactly
its kernel.

Reference: O'Meara, *Introduction to Quadratic Forms*, §101-102.
-/

@[expose] public section

open CategoryTheory
open LeanCategories.Modules.Bilinear.Valued

namespace LeanCategories.Lattices.Valued

universe u

variable {K : Type u} [Field K]

/-- A vector of nonzero value, the datum of one reflection. -/
abbrev AnisotropicVector (L : FiniteFormCat K K) :=
  { v : L.obj.carrier // L.obj.pairing v v ≠ 0 }

/-- The reflection in an anisotropic vector. -/
noncomputable def reflectionOf (L : FiniteFormCat K K) (v : AnisotropicVector L) :
    BilinModuleCat.OrthogonalGroup L.obj :=
  finiteFormReflectionElement L v.1 v.2

/-- The value of an anisotropic vector, as a unit. -/
def anisotropicValue (L : FiniteFormCat K K) (v : AnisotropicVector L) : Kˣ :=
  Units.mk0 (L.obj.pairing v.1 v.1) v.2

/-- A reflection is its own inverse. -/
theorem reflectionOf_inv (L : FiniteFormCat K K) (v : AnisotropicVector L) :
    (reflectionOf L v)⁻¹ = reflectionOf L v := by
  refine inv_eq_of_mul_eq_one_left (Subtype.ext (LinearEquiv.ext fun x ↦ ?_))
  exact Module.involutive_reflection (reflectionFunctional_apply_self L v.1 v.2) x

/-- Reversing a list of reflections inverts the product. -/
theorem prod_map_reflectionOf_reverse (L : FiniteFormCat K K)
    (l : List (AnisotropicVector L)) :
    (l.reverse.map (reflectionOf L)).prod = ((l.map (reflectionOf L)).prod)⁻¹ := by
  induction l with
  | nil => simp
  | cons v l ih =>
    rw [List.map_reverse] at ih
    simp [ih, reflectionOf_inv]

/-- An isometry is a product of reflections whose values multiply to a square. -/
def IsSpinorTrivial (L : FiniteFormCat K K)
    (g : BilinModuleCat.OrthogonalGroup L.obj) : Prop :=
  ∃ l : List (AnisotropicVector L),
    g = (l.map (reflectionOf L)).prod ∧
      fieldSquareClass (l.map (anisotropicValue L)).prod = 1

/-- The spinor kernel: products of reflections of square total value.

This is the kernel of the spinor norm, defined without reference to one. -/
noncomputable def spinorKernelSubgroup (L : FiniteFormCat K K) :
    Subgroup (BilinModuleCat.OrthogonalGroup L.obj) where
  carrier := {g | IsSpinorTrivial L g}
  one_mem' := ⟨[], by simp, by simp [fieldSquareClass]⟩
  mul_mem' := by
    rintro g h ⟨l, rfl, hl⟩ ⟨m, rfl, hm⟩
    refine ⟨l ++ m, by simp, ?_⟩
    rw [List.map_append, List.prod_append, fieldSquareClass_mul, hl, hm, one_mul]
  inv_mem' := by
    rintro g ⟨l, rfl, hl⟩
    refine ⟨l.reverse, (prod_map_reflectionOf_reverse L l).symm, ?_⟩
    rw [List.map_reverse, (List.reverse_perm _).prod_eq]
    exact hl

theorem mem_spinorKernelSubgroup_iff (L : FiniteFormCat K K)
    (g : BilinModuleCat.OrthogonalGroup L.obj) :
    g ∈ spinorKernelSubgroup L ↔ IsSpinorTrivial L g :=
  Iff.rfl

/-! ### Transport of the spinor kernel along an isometry -/

/-- The carrier equivalence of an isometry of finite symmetric forms. -/
noncomputable abbrev finiteFormEquiv {L M : FiniteFormCat K K} (e : L ≅ M) :
    L.obj.carrier ≃ₗ[K] M.obj.carrier :=
  BilinModuleCat.linearEquivOfIso ((ObjectProperty.ι (isFiniteForm K K)).mapIso e)

/-- An isometry identifies the orthogonal groups of its source and target. -/
noncomputable def orthogonalCongr {L M : FiniteFormCat K K} (e : L ≅ M) :
    BilinModuleCat.OrthogonalGroup L.obj ≃* BilinModuleCat.OrthogonalGroup M.obj :=
  BilinModuleCat.OrthogonalGroup.congr ((ObjectProperty.ι (isFiniteForm K K)).mapIso e)

/-- The image of an anisotropic vector under an isometry. -/
noncomputable def anisotropicCongr {L M : FiniteFormCat K K} (e : L ≅ M)
    (v : AnisotropicVector L) : AnisotropicVector M :=
  ⟨finiteFormEquiv e v.1, by
    rw [BilinModuleCat.linearEquivOfIso_pairing]
    exact v.2⟩

/-- An isometry preserves the value of an anisotropic vector. -/
theorem anisotropicValue_congr {L M : FiniteFormCat K K} (e : L ≅ M)
    (v : AnisotropicVector L) :
    anisotropicValue M (anisotropicCongr e v) = anisotropicValue L v :=
  Units.ext (BilinModuleCat.linearEquivOfIso_pairing _ _ _)

/-- An isometry carries a reflection to the reflection in the image vector. -/
theorem orthogonalCongr_reflectionOf {L M : FiniteFormCat K K} (e : L ≅ M)
    (v : AnisotropicVector L) :
    orthogonalCongr e (reflectionOf L v) = reflectionOf M (anisotropicCongr e v) := by
  refine Subtype.ext (LinearEquiv.ext fun x ↦ ?_)
  have hφ : ∀ y : L.obj.carrier,
      reflectionFunctional M (finiteFormEquiv e v.1) (anisotropicCongr e v).2
          (finiteFormEquiv e y) =
        reflectionFunctional L v.1 v.2 y := by
    intro y
    simp only [reflectionFunctional, LinearMap.smul_apply, BilinModuleCat.bilinMap_apply,
      smul_eq_mul, BilinModuleCat.linearEquivOfIso_pairing]
  change finiteFormEquiv e (finiteFormReflection L v.1 v.2 ((finiteFormEquiv e).symm x)) =
    finiteFormReflection M (finiteFormEquiv e v.1) (anisotropicCongr e v).2 x
  rw [finiteFormReflection_apply, map_sub, map_smul, LinearEquiv.apply_symm_apply,
    finiteFormReflection_apply, ← hφ, LinearEquiv.apply_symm_apply]

/-- The spinor kernel is stable under transport along an isometry. -/
theorem spinorKernelSubgroup_congr {L M : FiniteFormCat K K} (e : L ≅ M)
    {g : BilinModuleCat.OrthogonalGroup L.obj} (hg : g ∈ spinorKernelSubgroup L) :
    orthogonalCongr e g ∈ spinorKernelSubgroup M := by
  obtain ⟨l, rfl, hl⟩ := hg
  refine ⟨l.map (anisotropicCongr e), ?_, ?_⟩
  · rw [List.map_map, map_list_prod, List.map_map]
    exact congrArg List.prod (List.map_congr_left fun v _ ↦ orthogonalCongr_reflectionOf e v)
  · rw [List.map_map]
    rw [show (anisotropicValue M ∘ anisotropicCongr e) = anisotropicValue L from
      funext fun v ↦ anisotropicValue_congr e v]
    exact hl

/-- A spinor norm sends a product of reflections to the class of the product of the values. -/
theorem spinorNorm_prod_reflections (L : FiniteFormCat K K) (ν : SpinorNorm L)
    (l : List (AnisotropicVector L)) :
    ν.1 (l.map (reflectionOf L)).prod =
      fieldSquareClass (l.map (anisotropicValue L)).prod := by
  induction l with
  | nil => simp [fieldSquareClass]
  | cons v l ih =>
    rw [List.map_cons, List.prod_cons, map_mul, ih, List.map_cons, List.prod_cons,
      fieldSquareClass_mul, reflectionOf, ν.2 v.1 v.2]
    rfl

/-- The spinor kernel lies in the kernel of every spinor norm. -/
theorem spinorKernelSubgroup_le_spinorKernel (L : FiniteFormCat K K) (ν : SpinorNorm L) :
    spinorKernelSubgroup L ≤ spinorKernel L ν := by
  rintro g ⟨l, rfl, hl⟩
  exact MonoidHom.mem_ker.mpr ((spinorNorm_prod_reflections L ν l).trans hl)

variable [Invertible (2 : K)]

/-- On a nondegenerate form every isometry is a product of reflections. -/
theorem exists_list_reflectionOf (L : FiniteFormCat K K) (hL : L.obj.IsLeftNondegenerate)
    (g : BilinModuleCat.OrthogonalGroup L.obj) :
    ∃ l : List (AnisotropicVector L), g = (l.map (reflectionOf L)).prod := by
  have hmem : g ∈ Subgroup.closure (finiteFormReflections L) := by
    rw [reflectionsGenerate L hL]
    trivial
  induction hmem using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨v, hv, rfl⟩ := hx
    exact ⟨[⟨v, hv⟩], by simp [reflectionOf]⟩
  | one => exact ⟨[], by simp⟩
  | mul x y _ _ hx hy =>
    obtain ⟨l, rfl⟩ := hx
    obtain ⟨m, rfl⟩ := hy
    exact ⟨l ++ m, by simp⟩
  | inv x _ hx =>
    obtain ⟨l, rfl⟩ := hx
    exact ⟨l.reverse, (prod_map_reflectionOf_reverse L l).symm⟩

/-- On a nondegenerate form the spinor kernel is the kernel of any spinor norm.

The subgroup is defined without choosing a spinor norm, so this identifies the classical
kernel independently of the existence question for spinor norms. -/
theorem spinorKernelSubgroup_eq_spinorKernel (L : FiniteFormCat K K)
    (hL : L.obj.IsLeftNondegenerate) (ν : SpinorNorm L) :
    spinorKernelSubgroup L = spinorKernel L ν := by
  refine le_antisymm (spinorKernelSubgroup_le_spinorKernel L ν) fun g hg ↦ ?_
  obtain ⟨l, hl⟩ := exists_list_reflectionOf L hL g
  refine ⟨l, hl, ?_⟩
  rw [← spinorNorm_prod_reflections L ν l, ← hl]
  exact MonoidHom.mem_ker.mp hg

/-! ### The automorphism element of a composite isometry -/

omit [Invertible (2 : K)] in
/-- Transport of an automorphism element along an isometry conjugates the isometry. -/
theorem orthogonalCongr_finiteFormAutomorphismElement {L M : FiniteFormCat K K} (e : L ≅ M)
    (X : L ≅ L) :
    orthogonalCongr e (finiteFormAutomorphismElement L X) =
      finiteFormAutomorphismElement M (e.symm ≪≫ X ≪≫ e) :=
  rfl

omit [Invertible (2 : K)] in
/-- The inverse automorphism element is the element of the inverse isometry. -/
theorem finiteFormAutomorphismElement_symm {L : FiniteFormCat K K} (X : L ≅ L) :
    (finiteFormAutomorphismElement L X)⁻¹ = finiteFormAutomorphismElement L X.symm :=
  rfl

omit [Invertible (2 : K)] in
/-- The product of automorphism elements is the element of the composite isometry. -/
theorem finiteFormAutomorphismElement_mul {L : FiniteFormCat K K} (X Y : L ≅ L) :
    finiteFormAutomorphismElement L X * finiteFormAutomorphismElement L Y =
      finiteFormAutomorphismElement L (Y ≪≫ X) :=
  rfl

/-! ## Scalar extension through an intermediate ring -/

section CancelBaseChange

variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
  {P Q : Type u} [AddCommGroup P] [Module R P] [AddCommGroup Q] [Module R Q]

/-- The comparison of the direct scalar extension with the iterated one. -/
noncomputable abbrev cancelBaseChangeEquiv (R A B : Type u) [CommRing R] [CommRing A]
    [CommRing B] [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
    (P : Type u) [AddCommGroup P] [Module R P] :
    TensorProduct A B (TensorProduct R A P) ≃ₗ[B] TensorProduct R B P :=
  TensorProduct.AlgebraTensorModule.cancelBaseChange R A B B P

/-- A map of direct scalar extensions which agrees with an intermediate map on the generators
`1 ⊗ₜ x` agrees with it on every element of the intermediate extension. -/
theorem cancelBaseChange_tmul_comm
    (e : TensorProduct R A P →ₗ[A] TensorProduct R A Q)
    (f : TensorProduct R B P →ₗ[B] TensorProduct R B Q)
    (h : ∀ x : P, f (1 ⊗ₜ[R] x) = cancelBaseChangeEquiv R A B Q (1 ⊗ₜ[A] e (1 ⊗ₜ[R] x)))
    (w : TensorProduct R A P) :
    f (cancelBaseChangeEquiv R A B P (1 ⊗ₜ[A] w)) =
      cancelBaseChangeEquiv R A B Q (1 ⊗ₜ[A] e w) := by
  have key : ∀ (b : B) (u : TensorProduct R A Q),
      cancelBaseChangeEquiv R A B Q (b ⊗ₜ[A] u) =
        b • cancelBaseChangeEquiv R A B Q (1 ⊗ₜ[A] u) := by
    intro b u
    have hb : (b ⊗ₜ[A] u : TensorProduct A B (TensorProduct R A Q)) = b • (1 ⊗ₜ[A] u) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [hb, map_smul]
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
    have hP : (a ⊗ₜ[R] x : TensorProduct R A P) = a • (1 ⊗ₜ[R] x) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    have hB : ((a • (1 : B)) ⊗ₜ[R] x : TensorProduct R B P) =
        (a • (1 : B)) • (1 ⊗ₜ[R] x) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul, hB, map_smul, h x, hP,
      map_smul, ← TensorProduct.smul_tmul]
    conv_rhs => rw [key]
  | add w₁ w₂ h₁ h₂ => rw [TensorProduct.tmul_add, map_add, map_add, h₁, h₂, map_add,
      TensorProduct.tmul_add, map_add]

end CancelBaseChange

/-! ## The spinor genus of a finite integral lattice -/

/-- The rational scalar extension of a finite integral lattice. -/
noncomputable abbrev RationalLattice (L : FiniteProjectiveLatticeCat ℤ ℤ) :=
  (baseChangeFiniteIntegral ℤ ℚ).obj L

/-- The direct scalar extension of a finite integral lattice to `ℚ_[p]`. -/
noncomputable abbrev PadicFieldLattice (p : ℕ) [Fact p.Prime]
    (L : FiniteProjectiveLatticeCat ℤ ℤ) :=
  (extendFiniteIntegralToPadicField p).obj L

/-- The completion of a finite integral lattice over `ℤ_[p]`. -/
noncomputable abbrev PadicIntegralLattice (p : ℕ) [Fact p.Prime]
    (L : FiniteProjectiveLatticeCat ℤ ℤ) :=
  (completeFiniteIntegralAtPrime p).obj L

/-- The finite symmetric form under a direct `p`-adic field extension. -/
noncomputable abbrev PadicFieldForm (p : ℕ) [Fact p.Prime]
    (L : FiniteProjectiveLatticeCat ℤ ℤ) :=
  (finiteProjectiveToFiniteForm ℚ_[p] ℚ_[p]).obj (PadicFieldLattice p L)

/-- A direct `p`-adic isometry is the scalar extension of a rational isometry. -/
noncomputable def IsPadicScalarExtensionOf (p : ℕ) [Fact p.Prime]
    {L M : FiniteProjectiveLatticeCat ℤ ℤ}
    (e : RationalLattice L ≅ RationalLattice M)
    (eₚ : PadicFieldLattice p L ≅ PadicFieldLattice p M) : Prop :=
  ∀ x : L.obj.obj.carrier,
    ((finiteProjectiveForget ℚ_[p] ℚ_[p]).mapIso eₚ).toLinearEquiv (1 ⊗ₜ[ℤ] x) =
      TensorProduct.AlgebraTensorModule.cancelBaseChange
        ℤ ℚ ℚ_[p] ℚ_[p] M.obj.obj.carrier
        (1 ⊗ₜ[ℚ] ((finiteProjectiveForget ℚ ℚ).mapIso e).toLinearEquiv (1 ⊗ₜ[ℤ] x))

/-- A direct `p`-adic field isometry extends an isometry of completed lattices. -/
noncomputable def IsPadicCompletionExtensionOf (p : ℕ) [Fact p.Prime]
    {L M : FiniteProjectiveLatticeCat ℤ ℤ}
    (e : PadicIntegralLattice p L ≅ PadicIntegralLattice p M)
    (eₚ : PadicFieldLattice p L ≅ PadicFieldLattice p M) : Prop :=
  ∀ x : L.obj.obj.carrier,
    ((finiteProjectiveForget ℚ_[p] ℚ_[p]).mapIso eₚ).toLinearEquiv (1 ⊗ₜ[ℤ] x) =
      TensorProduct.AlgebraTensorModule.cancelBaseChange
        ℤ ℤ_[p] ℚ_[p] ℚ_[p] M.obj.obj.carrier
        (1 ⊗ₜ[ℤ_[p]]
          ((finiteProjectiveForget ℤ_[p] ℤ_[p]).mapIso e).toLinearEquiv (1 ⊗ₜ[ℤ] x))

/-- The automorphism of the `p`-adic space comparing two `p`-adic isometries. -/
noncomputable def padicComparison (p : ℕ) [Fact p.Prime]
    {L M : FiniteProjectiveLatticeCat ℤ ℤ}
    (reference current : PadicFieldLattice p L ≅ PadicFieldLattice p M) :
    BilinModuleCat.OrthogonalGroup (PadicFieldForm p L).obj :=
  finiteFormAutomorphismElement (PadicFieldForm p L)
    ((finiteProjectiveToFiniteForm ℚ_[p] ℚ_[p]).mapIso current ≪≫
      ((finiteProjectiveToFiniteForm ℚ_[p] ℚ_[p]).mapIso reference).symm)

/-- Local data at one prime: an integral isometry which differs from the rational isometry by
an element of the spinor kernel of the `p`-adic space. -/
structure PadicSpinorWitness (L M : FiniteProjectiveLatticeCat ℤ ℤ)
    (rational : RationalLattice L ≅ RationalLattice M) (p : ℕ) [Fact p.Prime] where
  /-- An isometry of the `p`-adic completions. -/
  integral : PadicIntegralLattice p L ≅ PadicIntegralLattice p M
  /-- The `p`-adic isometry induced by the rational one. -/
  reference : PadicFieldLattice p L ≅ PadicFieldLattice p M
  /-- The `p`-adic isometry induced by the integral one. -/
  current : PadicFieldLattice p L ≅ PadicFieldLattice p M
  /-- `reference` is the scalar extension of the rational isometry. -/
  reference_isScalarExtension : IsPadicScalarExtensionOf p rational reference
  /-- `current` is the scalar extension of the integral isometry. -/
  current_isCompletionExtension : IsPadicCompletionExtensionOf p integral current
  /-- The two `p`-adic isometries differ by a spinor-kernel element. -/
  spinorTrivial : padicComparison p reference current ∈ spinorKernelSubgroup (PadicFieldForm p L)

/-- A rational isometry together with local integral isometries which differ from it by
spinor-kernel elements at every prime. -/
structure SpinorGenusWitness (L M : FiniteProjectiveLatticeCat ℤ ℤ) where
  /-- The two lattices lie in one genus. -/
  genus : SameGenus L M
  /-- A rational isometry of the ambient quadratic spaces. -/
  rational : RationalLattice L ≅ RationalLattice M
  /-- Local spinor data at every prime. -/
  atPrime : ∀ (p : ℕ) (hp : p.Prime),
    letI : Fact p.Prime := ⟨hp⟩
    PadicSpinorWitness L M rational p

/-- Two finite integral lattices lie in the same spinor genus.

The relation refines the ring-adelic genus of `LocalGlobal.lean`. It uses the choice-free
spinor kernel, so no spinor norm is chosen at any place; `padicComparison_spinorNorm_eq_one`
records that any spinor norm of the `p`-adic form takes the value one on the comparison
element, and `spinorKernelSubgroup_eq_spinorKernel` shows the two conditions agree for
nondegenerate forms. A spinor norm is unique by `subsingleton_spinorNorm_of_nondegenerate`,
so no such statement depends on a choice. -/
noncomputable def SameSpinorGenus (L M : FiniteProjectiveLatticeCat ℤ ℤ) : Prop :=
  Nonempty (SpinorGenusWitness L M)

/-- A common spinor genus is contained in one genus. -/
theorem sameGenus_of_sameSpinorGenus {L M : FiniteProjectiveLatticeCat ℤ ℤ}
    (h : SameSpinorGenus L M) : SameGenus L M := by
  obtain ⟨w⟩ := h
  exact w.genus

/-- Lattices in one spinor genus are isometric over the reals.

The real place needs no separate field in the witness: the ring-adelic genus already carries
it. -/
theorem isRealIsometric_of_sameSpinorGenus {L M : FiniteProjectiveLatticeCat ℤ ℤ}
    (h : SameSpinorGenus L M) : IsRealIsometric L.obj M.obj :=
  ((sameGenus_iff_isClassicallyLocallyIsometric L M).mp (sameGenus_of_sameSpinorGenus h)).1

/-- Every spinor norm of the `p`-adic form vanishes on the comparison element.

This is the statement that the definition above does not depend on a spinor norm: it implies
the condition used by the earlier witness structure, for every spinor norm at once. -/
theorem padicComparison_spinorNorm_eq_one {L M : FiniteProjectiveLatticeCat ℤ ℤ}
    {rational : RationalLattice L ≅ RationalLattice M} {p : ℕ} [Fact p.Prime]
    (w : PadicSpinorWitness L M rational p) (ν : SpinorNorm (PadicFieldForm p L)) :
    ν.1 (padicComparison p w.reference w.current) = 1 :=
  MonoidHom.mem_ker.mp
    (spinorKernelSubgroup_le_spinorKernel (PadicFieldForm p L) ν w.spinorTrivial)

/-- The identity is the scalar extension of the identity. -/
theorem isPadicScalarExtensionOf_refl (p : ℕ) [Fact p.Prime]
    (L : FiniteProjectiveLatticeCat ℤ ℤ) :
    IsPadicScalarExtensionOf p (Iso.refl (RationalLattice L))
      (Iso.refl (PadicFieldLattice p L)) := by
  intro x
  simp

/-- The identity is the completion extension of the identity. -/
theorem isPadicCompletionExtensionOf_refl (p : ℕ) [Fact p.Prime]
    (L : FiniteProjectiveLatticeCat ℤ ℤ) :
    IsPadicCompletionExtensionOf p (Iso.refl (PadicIntegralLattice p L))
      (Iso.refl (PadicFieldLattice p L)) := by
  intro x
  simp

/-- Composites of scalar extensions are scalar extensions of composites. -/
theorem isPadicScalarExtensionOf_trans (p : ℕ) [Fact p.Prime]
    {L M N : FiniteProjectiveLatticeCat ℤ ℤ}
    {e₁ : RationalLattice L ≅ RationalLattice M}
    {f₁ : PadicFieldLattice p L ≅ PadicFieldLattice p M}
    {e₂ : RationalLattice M ≅ RationalLattice N}
    {f₂ : PadicFieldLattice p M ≅ PadicFieldLattice p N}
    (h₁ : IsPadicScalarExtensionOf p e₁ f₁) (h₂ : IsPadicScalarExtensionOf p e₂ f₂) :
    IsPadicScalarExtensionOf p (e₁ ≪≫ e₂) (f₁ ≪≫ f₂) := by
  intro x
  change ((finiteProjectiveForget ℚ_[p] ℚ_[p]).mapIso f₂).toLinearEquiv
      (((finiteProjectiveForget ℚ_[p] ℚ_[p]).mapIso f₁).toLinearEquiv (1 ⊗ₜ[ℤ] x)) = _
  rw [h₁ x]
  exact cancelBaseChange_tmul_comm
    ((finiteProjectiveForget ℚ ℚ).mapIso e₂).toLinearEquiv.toLinearMap
    ((finiteProjectiveForget ℚ_[p] ℚ_[p]).mapIso f₂).toLinearEquiv.toLinearMap h₂ _

/-- Composites of completion extensions are completion extensions of composites. -/
theorem isPadicCompletionExtensionOf_trans (p : ℕ) [Fact p.Prime]
    {L M N : FiniteProjectiveLatticeCat ℤ ℤ}
    {e₁ : PadicIntegralLattice p L ≅ PadicIntegralLattice p M}
    {f₁ : PadicFieldLattice p L ≅ PadicFieldLattice p M}
    {e₂ : PadicIntegralLattice p M ≅ PadicIntegralLattice p N}
    {f₂ : PadicFieldLattice p M ≅ PadicFieldLattice p N}
    (h₁ : IsPadicCompletionExtensionOf p e₁ f₁) (h₂ : IsPadicCompletionExtensionOf p e₂ f₂) :
    IsPadicCompletionExtensionOf p (e₁ ≪≫ e₂) (f₁ ≪≫ f₂) := by
  intro x
  change ((finiteProjectiveForget ℚ_[p] ℚ_[p]).mapIso f₂).toLinearEquiv
      (((finiteProjectiveForget ℚ_[p] ℚ_[p]).mapIso f₁).toLinearEquiv (1 ⊗ₜ[ℤ] x)) = _
  rw [h₁ x]
  exact cancelBaseChange_tmul_comm
    ((finiteProjectiveForget ℤ_[p] ℤ_[p]).mapIso e₂).toLinearEquiv.toLinearMap
    ((finiteProjectiveForget ℚ_[p] ℚ_[p]).mapIso f₂).toLinearEquiv.toLinearMap h₂ _

/-- Inverses of scalar extensions are scalar extensions of inverses. -/
theorem isPadicScalarExtensionOf_symm (p : ℕ) [Fact p.Prime]
    {L M : FiniteProjectiveLatticeCat ℤ ℤ}
    {e : RationalLattice L ≅ RationalLattice M}
    {f : PadicFieldLattice p L ≅ PadicFieldLattice p M}
    (h : IsPadicScalarExtensionOf p e f) :
    IsPadicScalarExtensionOf p e.symm f.symm := by
  intro y
  have hf : ((finiteProjectiveForget ℚ_[p] ℚ_[p]).mapIso f.symm).toLinearEquiv =
    ((finiteProjectiveForget ℚ_[p] ℚ_[p]).mapIso f).toLinearEquiv.symm := rfl
  have he : ((finiteProjectiveForget ℚ ℚ).mapIso e.symm).toLinearEquiv =
    ((finiteProjectiveForget ℚ ℚ).mapIso e).toLinearEquiv.symm := rfl
  rw [hf, he, LinearEquiv.symm_apply_eq]
  refine ((cancelBaseChange_tmul_comm
    ((finiteProjectiveForget ℚ ℚ).mapIso e).toLinearEquiv.toLinearMap
    ((finiteProjectiveForget ℚ_[p] ℚ_[p]).mapIso f).toLinearEquiv.toLinearMap h
    (((finiteProjectiveForget ℚ ℚ).mapIso e).toLinearEquiv.symm (1 ⊗ₜ[ℤ] y))).trans ?_).symm
  have happ : ((finiteProjectiveForget ℚ ℚ).mapIso e).toLinearEquiv
      (((finiteProjectiveForget ℚ ℚ).mapIso e).toLinearEquiv.symm (1 ⊗ₜ[ℤ] y)) = 1 ⊗ₜ[ℤ] y :=
    LinearEquiv.apply_symm_apply _ _
  change cancelBaseChangeEquiv ℤ ℚ ℚ_[p] M.obj.obj.carrier
      (1 ⊗ₜ[ℚ] ((finiteProjectiveForget ℚ ℚ).mapIso e).toLinearEquiv
        (((finiteProjectiveForget ℚ ℚ).mapIso e).toLinearEquiv.symm (1 ⊗ₜ[ℤ] y))) = 1 ⊗ₜ[ℤ] y
  rw [happ, TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul, one_smul]

/-- Inverses of completion extensions are completion extensions of inverses. -/
theorem isPadicCompletionExtensionOf_symm (p : ℕ) [Fact p.Prime]
    {L M : FiniteProjectiveLatticeCat ℤ ℤ}
    {e : PadicIntegralLattice p L ≅ PadicIntegralLattice p M}
    {f : PadicFieldLattice p L ≅ PadicFieldLattice p M}
    (h : IsPadicCompletionExtensionOf p e f) :
    IsPadicCompletionExtensionOf p e.symm f.symm := by
  intro y
  have hf : ((finiteProjectiveForget ℚ_[p] ℚ_[p]).mapIso f.symm).toLinearEquiv =
    ((finiteProjectiveForget ℚ_[p] ℚ_[p]).mapIso f).toLinearEquiv.symm := rfl
  have he : ((finiteProjectiveForget ℤ_[p] ℤ_[p]).mapIso e.symm).toLinearEquiv =
    ((finiteProjectiveForget ℤ_[p] ℤ_[p]).mapIso e).toLinearEquiv.symm := rfl
  rw [hf, he, LinearEquiv.symm_apply_eq]
  refine ((cancelBaseChange_tmul_comm
    ((finiteProjectiveForget ℤ_[p] ℤ_[p]).mapIso e).toLinearEquiv.toLinearMap
    ((finiteProjectiveForget ℚ_[p] ℚ_[p]).mapIso f).toLinearEquiv.toLinearMap h
    (((finiteProjectiveForget ℤ_[p] ℤ_[p]).mapIso e).toLinearEquiv.symm (1 ⊗ₜ[ℤ] y))).trans ?_).symm
  have happ : ((finiteProjectiveForget ℤ_[p] ℤ_[p]).mapIso e).toLinearEquiv
      (((finiteProjectiveForget ℤ_[p] ℤ_[p]).mapIso e).toLinearEquiv.symm (1 ⊗ₜ[ℤ] y)) =
      1 ⊗ₜ[ℤ] y :=
    LinearEquiv.apply_symm_apply _ _
  change cancelBaseChangeEquiv ℤ ℤ_[p] ℚ_[p] M.obj.obj.carrier
      (1 ⊗ₜ[ℤ_[p]] ((finiteProjectiveForget ℤ_[p] ℤ_[p]).mapIso e).toLinearEquiv
        (((finiteProjectiveForget ℤ_[p] ℤ_[p]).mapIso e).toLinearEquiv.symm (1 ⊗ₜ[ℤ] y))) =
    1 ⊗ₜ[ℤ] y
  rw [happ, TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul, one_smul]

/-- Comparing an isometry with itself gives the identity. -/
theorem padicComparison_self (p : ℕ) [Fact p.Prime]
    {L M : FiniteProjectiveLatticeCat ℤ ℤ}
    (e : PadicFieldLattice p L ≅ PadicFieldLattice p M) :
    padicComparison p e e = 1 := by
  refine Subtype.ext (LinearEquiv.ext fun x ↦ ?_)
  simp only [padicComparison, finiteFormAutomorphismElement, Iso.self_symm_id, Functor.mapIso_refl]
  rfl

/-- Comparing inverse isometries conjugates the comparison element by the current isometry. -/
theorem padicComparison_symm (p : ℕ) [Fact p.Prime]
    {L M : FiniteProjectiveLatticeCat ℤ ℤ}
    (reference current : PadicFieldLattice p L ≅ PadicFieldLattice p M) :
    padicComparison p reference.symm current.symm =
      orthogonalCongr ((finiteProjectiveToFiniteForm ℚ_[p] ℚ_[p]).mapIso current)
        (padicComparison p reference current)⁻¹ := by
  simp only [padicComparison, Functor.mapIso_symm, Iso.symm_symm_eq,
    finiteFormAutomorphismElement_symm, orthogonalCongr_finiteFormAutomorphismElement]
  congr 1
  simp [Iso.trans_assoc]

/-- Comparing composite isometries multiplies the comparison elements. -/
theorem padicComparison_trans (p : ℕ) [Fact p.Prime]
    {L M N : FiniteProjectiveLatticeCat ℤ ℤ}
    (reference₁ current₁ : PadicFieldLattice p L ≅ PadicFieldLattice p M)
    (reference₂ current₂ : PadicFieldLattice p M ≅ PadicFieldLattice p N) :
    padicComparison p (reference₁ ≪≫ reference₂) (current₁ ≪≫ current₂) =
      orthogonalCongr ((finiteProjectiveToFiniteForm ℚ_[p] ℚ_[p]).mapIso reference₁).symm
          (padicComparison p reference₂ current₂) *
        padicComparison p reference₁ current₁ := by
  simp only [padicComparison, Functor.mapIso_trans, Iso.trans_symm, Iso.symm_symm_eq,
    orthogonalCongr_finiteFormAutomorphismElement, finiteFormAutomorphismElement_mul]
  congr 1
  simp [Iso.trans_assoc]

/-- Every lattice lies in its own spinor genus. -/
theorem sameSpinorGenus_refl (L : FiniteProjectiveLatticeCat ℤ ℤ) :
    SameSpinorGenus L L :=
  ⟨{ genus := sameGenus_refl L
     rational := Iso.refl _
     atPrime := fun p hp ↦
       letI : Fact p.Prime := ⟨hp⟩
       { integral := Iso.refl _
         reference := Iso.refl _
         current := Iso.refl _
         reference_isScalarExtension := isPadicScalarExtensionOf_refl p L
         current_isCompletionExtension := isPadicCompletionExtensionOf_refl p L
         spinorTrivial := by
           rw [padicComparison_self]
           exact Subgroup.one_mem _ } }⟩

/-- The spinor genus relation is symmetric. -/
theorem sameSpinorGenus_symm {L M : FiniteProjectiveLatticeCat ℤ ℤ}
    (h : SameSpinorGenus L M) : SameSpinorGenus M L := by
  obtain ⟨w⟩ := h
  refine ⟨{ genus := sameGenus_symm w.genus
            rational := w.rational.symm
            atPrime := fun p hp ↦ ?_ }⟩
  letI : Fact p.Prime := ⟨hp⟩
  exact
    { integral := (w.atPrime p hp).integral.symm
      reference := (w.atPrime p hp).reference.symm
      current := (w.atPrime p hp).current.symm
      reference_isScalarExtension :=
        isPadicScalarExtensionOf_symm p (w.atPrime p hp).reference_isScalarExtension
      current_isCompletionExtension :=
        isPadicCompletionExtensionOf_symm p (w.atPrime p hp).current_isCompletionExtension
      spinorTrivial := by
        rw [padicComparison_symm]
        exact spinorKernelSubgroup_congr _
          (Subgroup.inv_mem _ (w.atPrime p hp).spinorTrivial) }

/-- The spinor genus relation is transitive. -/
theorem sameSpinorGenus_trans {L M N : FiniteProjectiveLatticeCat ℤ ℤ}
    (hLM : SameSpinorGenus L M) (hMN : SameSpinorGenus M N) : SameSpinorGenus L N := by
  obtain ⟨v⟩ := hLM
  obtain ⟨w⟩ := hMN
  refine ⟨{ genus := sameGenus_trans v.genus w.genus
            rational := v.rational ≪≫ w.rational
            atPrime := fun p hp ↦ ?_ }⟩
  letI : Fact p.Prime := ⟨hp⟩
  exact
    { integral := (v.atPrime p hp).integral ≪≫ (w.atPrime p hp).integral
      reference := (v.atPrime p hp).reference ≪≫ (w.atPrime p hp).reference
      current := (v.atPrime p hp).current ≪≫ (w.atPrime p hp).current
      reference_isScalarExtension := isPadicScalarExtensionOf_trans p
        (v.atPrime p hp).reference_isScalarExtension
        (w.atPrime p hp).reference_isScalarExtension
      current_isCompletionExtension := isPadicCompletionExtensionOf_trans p
        (v.atPrime p hp).current_isCompletionExtension
        (w.atPrime p hp).current_isCompletionExtension
      spinorTrivial := by
        rw [padicComparison_trans]
        exact Subgroup.mul_mem _
          (spinorKernelSubgroup_congr _ (w.atPrime p hp).spinorTrivial)
          (v.atPrime p hp).spinorTrivial }

/-- The spinor genus as an equivalence relation on finite integral lattices. -/
noncomputable def spinorGenusSetoid : Setoid (FiniteProjectiveLatticeCat ℤ ℤ) where
  r := SameSpinorGenus
  iseqv := ⟨sameSpinorGenus_refl, sameSpinorGenus_symm, sameSpinorGenus_trans⟩

/-- Lattices in the spinor genus of `L`. -/
noncomputable def spinorGenusProperty (L : FiniteProjectiveLatticeCat ℤ ℤ) :
    ObjectProperty (FiniteProjectiveLatticeCat ℤ ℤ) :=
  SameSpinorGenus L

/-- Finite integral lattices in a fixed spinor genus. -/
noncomputable abbrev SpinorGenusCat (L : FiniteProjectiveLatticeCat ℤ ℤ) :=
  (spinorGenusProperty L).FullSubcategory

end LeanCategories.Lattices.Valued
