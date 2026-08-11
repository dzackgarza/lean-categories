/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Algebra.IntegralAdeleRing
public import LeanCategories.Lattices.Valued.BaseChange

/-!
# Adelic scalar extension of integral lattices

Adelization is scalar extension to the ring adele ring. The existing base-change functor transports
the carrier, value module, and bilinear form together.
-/

@[expose] public section

noncomputable section

open CategoryTheory
open IsDedekindDomain NumberField
open scoped NumberField

namespace LeanCategories.Lattices.Valued

universe u

variable (K : Type u) [Field K] [NumberField K]

/-- Scalar extension of integral lattices from `𝓞 K` to its ring adele ring. -/
def ringAdeleBaseChange :
    IntegralLatticeCat (𝓞 K) ⥤ IntegralLatticeCat (RingAdeleRing K) :=
  baseChangeIntegral (𝓞 K) (RingAdeleRing K)

/-- Scalar extension of finite projective lattices to the ring adele ring. -/
def finiteRingAdeleBaseChange :
    FiniteProjectiveLatticeCat (𝓞 K) (𝓞 K) ⥤
      FiniteProjectiveLatticeCat (RingAdeleRing K) (RingAdeleRing K) :=
  baseChangeFiniteIntegral (𝓞 K) (RingAdeleRing K)

/-- The finite local scalar extensions of a finite projective lattice. -/
abbrev FiniteAdeleModuleProduct
    (L : FiniteProjectiveLatticeCat (𝓞 K) (𝓞 K)) :=
  FiniteIntegralAdeleRing.ModuleProduct (𝓞 K) K L.obj.obj.carrier

/-- The finite part of adelic scalar extension is the product of all completed local scalar
extensions. -/
def finiteAdeleCarrierEquiv
    (L : FiniteProjectiveLatticeCat (𝓞 K) (𝓞 K)) :
    TensorProduct (𝓞 K) (FiniteIntegralAdeleRing (𝓞 K) K) L.obj.obj.carrier ≃ₗ[𝓞 K]
      FiniteAdeleModuleProduct K L := by
  letI : Module.Finite (𝓞 K) L.obj.obj.carrier := L.property
  letI : Module.Projective (𝓞 K) L.obj.obj.carrier := L.obj.property.1
  exact (TensorProduct.comm (𝓞 K) (FiniteIntegralAdeleRing (𝓞 K) K)
    L.obj.obj.carrier).trans
      (FiniteIntegralAdeleRing.tensorProductEquivModuleProduct
        (𝓞 K) K L.obj.obj.carrier)

@[simp]
theorem finiteAdeleCarrierEquiv_tmul
    (L : FiniteProjectiveLatticeCat (𝓞 K) (𝓞 K))
    (a : FiniteIntegralAdeleRing (𝓞 K) K) (x : L.obj.obj.carrier) :
    finiteAdeleCarrierEquiv K L (a ⊗ₜ[𝓞 K] x) =
      fun v ↦ x ⊗ₜ[𝓞 K] a v := by
  letI : Module.Finite (𝓞 K) L.obj.obj.carrier := L.property
  letI : Module.Projective (𝓞 K) L.obj.obj.carrier := L.obj.property.1
  change FiniteIntegralAdeleRing.tensorProductEquivModuleProduct
    (𝓞 K) K L.obj.obj.carrier
      ((TensorProduct.comm (𝓞 K) (FiniteIntegralAdeleRing (𝓞 K) K)
        L.obj.obj.carrier) (a ⊗ₜ[𝓞 K] x)) = _
  rw [TensorProduct.comm_tmul,
    FiniteIntegralAdeleRing.tensorProductEquivModuleProduct_tmul]

/-- Two finite projective integral lattices have the same genus when their adelic scalar
extensions are isometric. -/
def SameAdeleGenus
    (L M : FiniteProjectiveLatticeCat (𝓞 K) (𝓞 K)) : Prop :=
  Nonempty ((finiteRingAdeleBaseChange K).obj L ≅
    (finiteRingAdeleBaseChange K).obj M)

theorem sameAdeleGenus_refl
    (L : FiniteProjectiveLatticeCat (𝓞 K) (𝓞 K)) :
    SameAdeleGenus K L L :=
  ⟨Iso.refl _⟩

theorem sameAdeleGenus_symm
    {L M : FiniteProjectiveLatticeCat (𝓞 K) (𝓞 K)}
    (h : SameAdeleGenus K L M) : SameAdeleGenus K M L := by
  obtain ⟨e⟩ := h
  exact ⟨e.symm⟩

theorem sameAdeleGenus_trans
    {L M N : FiniteProjectiveLatticeCat (𝓞 K) (𝓞 K)}
    (hLM : SameAdeleGenus K L M) (hMN : SameAdeleGenus K M N) :
    SameAdeleGenus K L N := by
  obtain ⟨e⟩ := hLM
  obtain ⟨f⟩ := hMN
  exact ⟨e ≪≫ f⟩

/-- Adelic genus is an equivalence relation on finite projective integral lattices. -/
def adeleGenusSetoid : Setoid (FiniteProjectiveLatticeCat (𝓞 K) (𝓞 K)) where
  r := SameAdeleGenus K
  iseqv := ⟨sameAdeleGenus_refl K, sameAdeleGenus_symm K,
    sameAdeleGenus_trans K⟩

end LeanCategories.Lattices.Valued
