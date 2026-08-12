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

/-! ## The spinor genus of a finite integral lattice

The declarations below live in `AdelicSpinor` while `SpinorGenus.lean` still exports the
provisional names.
-/

namespace AdelicSpinor

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

/-- Comparing an isometry with itself gives the identity. -/
theorem padicComparison_self (p : ℕ) [Fact p.Prime]
    {L M : FiniteProjectiveLatticeCat ℤ ℤ}
    (e : PadicFieldLattice p L ≅ PadicFieldLattice p M) :
    padicComparison p e e = 1 := by
  refine Subtype.ext (LinearEquiv.ext fun x ↦ ?_)
  simp only [padicComparison, finiteFormAutomorphismElement, Iso.self_symm_id, Functor.mapIso_refl]
  rfl

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

end AdelicSpinor

end LeanCategories.Lattices.Valued
