/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Lattices.Valued.Arithmetic
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal

@[expose] public section

open CategoryTheory
open LeanCategories.Modules.Bilinear.Valued

namespace LeanCategories.Modules.Bilinear.Valued.BilinModuleCat

universe u

variable {R : Type u} [CommRing R]
variable {W : Type u} [AddCommGroup W] [Module R W]

/-- A formed embedding is primitive when it is injective and has torsion-free cokernel. -/
def IsPrimitiveEmbedding {L M : BilinModuleCat R W} (f : L ⟶ M) : Prop :=
  Function.Injective (underlyingMap f) ∧
    Module.IsTorsionFree R
      (M.carrier ⧸ LinearMap.range (underlyingMap f))

/-- A formed embedding has finite index when it is injective with finite cokernel. -/
def IsFiniteIndexEmbedding {L M : BilinModuleCat R W} (f : L ⟶ M) : Prop :=
  Function.Injective (underlyingMap f) ∧
    Finite (M.carrier ⧸ LinearMap.range (underlyingMap f))

end LeanCategories.Modules.Bilinear.Valued.BilinModuleCat

namespace LeanCategories.Lattices.Valued

universe u

variable {R : Type u} [CommRing R]
variable {W : Type u} [AddCommGroup W] [Module R W]

/-- A submodule is primitive when its quotient is torsion-free. -/
def IsPrimitiveSubmodule {M : Type u} [AddCommGroup M] [Module R M]
    (P : Submodule R M) : Prop :=
  Module.IsTorsionFree R (M ⧸ P)

/-- A submodule has finite index when its quotient has finitely many elements. -/
def IsFiniteIndexSubmodule {M : Type u} [AddCommGroup M] [Module R M]
    (P : Submodule R M) : Prop :=
  Finite (M ⧸ P)

/-- The saturation of a submodule over an integral domain. -/
def saturation {M : Type u} [AddCommGroup M] [Module R M] [IsDomain R]
    (P : Submodule R M) : Submodule R M where
  carrier := {x | ∃ a : R, a ≠ 0 ∧ a • x ∈ P}
  zero_mem' := ⟨1, one_ne_zero, by simp⟩
  add_mem' := by
    rintro x y ⟨a, ha, hax⟩ ⟨b, hb, hby⟩
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    rw [smul_add]
    exact P.add_mem
      (by
        rw [mul_comm a b, mul_smul]
        exact P.smul_mem b hax)
      (by
        rw [mul_smul]
        exact P.smul_mem a hby)
  smul_mem' := by
    rintro r x ⟨a, ha, hax⟩
    refine ⟨a, ha, ?_⟩
    rw [smul_comm]
    exact P.smul_mem r hax

@[simp]
theorem mem_saturation_iff {M : Type u} [AddCommGroup M] [Module R M]
    [IsDomain R] (P : Submodule R M) (x : M) :
    x ∈ saturation P ↔ ∃ a : R, a ≠ 0 ∧ a • x ∈ P :=
  Iff.rfl

/-- Every submodule lies in its saturation. -/
theorem le_saturation {M : Type u} [AddCommGroup M] [Module R M]
    [IsDomain R] (P : Submodule R M) : P ≤ saturation P := by
  intro x hx
  exact ⟨1, one_ne_zero, by simpa using hx⟩

/-- The saturation has torsion-free quotient. -/
theorem saturation_isPrimitive {M : Type u} [AddCommGroup M] [Module R M]
    [IsDomain R] (P : Submodule R M) :
    IsPrimitiveSubmodule (saturation P) := by
  rw [IsPrimitiveSubmodule, Module.isTorsionFree_iff_smul_eq_zero]
  intro a x hx
  induction x using Quotient.inductionOn with
  | _ x =>
      by_cases ha : a = 0
      · exact Or.inl ha
      · right
        change (Submodule.Quotient.mk x : M ⧸ saturation P) = 0
        rw [Submodule.Quotient.mk_eq_zero]
        have hax : a • x ∈ saturation P := by
          rw [← Submodule.Quotient.mk_eq_zero,
            Submodule.Quotient.mk_smul]
          exact hx
        obtain ⟨b, hb, hbax⟩ := hax
        refine ⟨b * a, mul_ne_zero hb ha, ?_⟩
        simpa [mul_smul] using hbax

/-- A submodule is primitive exactly when it contains its saturation. -/
theorem isPrimitiveSubmodule_iff_saturation_le
    {M : Type u} [AddCommGroup M] [Module R M] [IsDomain R]
    (P : Submodule R M) :
    IsPrimitiveSubmodule P ↔ saturation P ≤ P := by
  constructor
  · intro hP x hx
    letI : Module.IsTorsionFree R (M ⧸ P) := hP
    obtain ⟨a, ha, hax⟩ := hx
    have hzero : a • (P.mkQ x) = 0 := by
      rw [← map_smul, Submodule.mkQ_apply,
        Submodule.Quotient.mk_eq_zero]
      exact hax
    have hxzero : P.mkQ x = 0 :=
      (smul_eq_zero.mp hzero).resolve_left ha
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hxzero
    exact hxzero
  · intro h
    have hEq : saturation P = P :=
      le_antisymm h (le_saturation P)
    rw [← hEq]
    exact saturation_isPrimitive P

/-- A submodule is primitive exactly when saturation does not enlarge it. -/
theorem isPrimitiveSubmodule_iff_saturation_eq
    {M : Type u} [AddCommGroup M] [Module R M] [IsDomain R]
    (P : Submodule R M) :
    IsPrimitiveSubmodule P ↔ saturation P = P := by
  rw [isPrimitiveSubmodule_iff_saturation_le]
  exact ⟨fun h ↦ le_antisymm h (le_saturation P), fun h ↦ h.le⟩

/-- A projective submodule with the restricted form. -/
def formedSublattice (L : LatticeCat R W) (P : Submodule R L.obj.carrier)
    [Module.Projective R P] : LatticeCat R W := by
  refine ⟨L.obj.restrict P, ?_, ?_⟩
  · change Module.Projective R P
    infer_instance
  · intro x y
    change P at x y
    exact L.property.2 x y

/-- The primitive closure of a formed sublattice. -/
def saturatedFormedSublattice [IsDomain R] (L : LatticeCat R W)
    (P : Submodule R L.obj.carrier)
    [Module.Projective R (saturation P)] : LatticeCat R W :=
  formedSublattice L (saturation P)

/-- The inclusion of a formed sublattice. -/
def formedSublatticeInclusion (L : LatticeCat R W)
    (P : Submodule R L.obj.carrier) [Module.Projective R P] :
    formedSublattice L P ⟶ L :=
  ObjectProperty.homMk (L.obj.restrictInclusion P)

/-- A formed-sublattice inclusion is primitive exactly when its submodule is primitive. -/
theorem formedSublatticeInclusion_isPrimitive_iff
    (L : LatticeCat R W) (P : Submodule R L.obj.carrier)
    [Module.Projective R P] :
    BilinModuleCat.IsPrimitiveEmbedding
        (formedSublatticeInclusion L P).hom ↔
      IsPrimitiveSubmodule P := by
  constructor
  · intro h
    have hCokernel := h.2
    change Module.IsTorsionFree R
      (L.obj.carrier ⧸ LinearMap.range P.subtype) at hCokernel
    rw [Submodule.range_subtype] at hCokernel
    exact hCokernel
  · intro h
    constructor
    · exact Subtype.val_injective
    · change Module.IsTorsionFree R
        (L.obj.carrier ⧸ LinearMap.range P.subtype)
      rw [Submodule.range_subtype]
      exact h

/-- A formed-sublattice inclusion has finite index exactly when its submodule does. -/
theorem formedSublatticeInclusion_isFiniteIndex_iff
    (L : LatticeCat R W) (P : Submodule R L.obj.carrier)
    [Module.Projective R P] :
    BilinModuleCat.IsFiniteIndexEmbedding
        (formedSublatticeInclusion L P).hom ↔
      IsFiniteIndexSubmodule P := by
  constructor
  · intro h
    have hCokernel := h.2
    change Finite
      (L.obj.carrier ⧸ LinearMap.range P.subtype) at hCokernel
    rw [Submodule.range_subtype] at hCokernel
    exact hCokernel
  · intro h
    constructor
    · exact Subtype.val_injective
    · change Finite
        (L.obj.carrier ⧸ LinearMap.range P.subtype)
      rw [Submodule.range_subtype]
      exact h

/-- Sublattice inclusion followed by quotient is exact. -/
theorem formedSublattice_exact
    (L : LatticeCat R W) (P : Submodule R L.obj.carrier) :
    Function.Exact P.subtype P.mkQ :=
  LinearMap.exact_subtype_mkQ P

/-- The submodule orthogonal to `P` inside an integral lattice. -/
def orthogonalSubmodule (L : IntegralLatticeCat R)
    (P : Submodule R L.obj.carrier) : Submodule R L.obj.carrier :=
  LinearMap.BilinForm.orthogonal L.obj.bilinMap P

@[simp]
theorem mem_orthogonalSubmodule_iff (L : IntegralLatticeCat R)
    (P : Submodule R L.obj.carrier) (x : L.obj.carrier) :
    x ∈ orthogonalSubmodule L P ↔ ∀ p ∈ P, L.obj.pairing p x = 0 :=
  Iff.rfl

/-- The orthogonal complement with its restricted form. -/
def orthogonalComplement (L : IntegralLatticeCat R)
    (P : Submodule R L.obj.carrier)
    [Module.Projective R (orthogonalSubmodule L P)] : IntegralLatticeCat R :=
  formedSublattice L (orthogonalSubmodule L P)

/-- The inclusion of an orthogonal complement. -/
def orthogonalComplementInclusion (L : IntegralLatticeCat R)
    (P : Submodule R L.obj.carrier)
    [Module.Projective R (orthogonalSubmodule L P)] :
    orthogonalComplement L P ⟶ L :=
  formedSublatticeInclusion L (orthogonalSubmodule L P)

end LeanCategories.Lattices.Valued
