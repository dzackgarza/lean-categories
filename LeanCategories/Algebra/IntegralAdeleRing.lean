/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.RingTheory.LocalRing.Pullback

/-!
# Integral adele rings

This file defines the product of the completed local integer rings of a Dedekind domain.
For a number field, it also defines the full ring adele ring. Its infinite coordinates are
field completions, while all finite coordinates remain integral.
-/

@[expose] public section

noncomputable section

open IsDedekindDomain
open scoped RestrictedProduct

namespace LeanCategories

universe u

variable (R K : Type u) [CommRing R] [IsDedekindDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K]

/-- The product of the completed local integer rings at all finite places. -/
abbrev FiniteIntegralAdeleRing :=
  (v : HeightOneSpectrum R) → v.adicCompletionIntegers K

namespace FiniteIntegralAdeleRing

/-- The canonical inclusion of integral finite adeles into finite field adeles. -/
def inclusion : FiniteIntegralAdeleRing R K →A[R] FiniteAdeleRing R K where
  toAlgHom :=
    { toFun := RestrictedProduct.structureMap
        (fun v : HeightOneSpectrum R ↦ v.adicCompletion K)
        (fun v : HeightOneSpectrum R ↦ (v.adicCompletionIntegers K : Set _))
        Filter.cofinite
      map_one' := rfl
      map_mul' _ _ := rfl
      map_zero' := rfl
      map_add' _ _ := rfl
      commutes' _ := rfl }
  cont := RestrictedProduct.isEmbedding_structureMap.continuous

@[simp]
theorem inclusion_apply (x : FiniteIntegralAdeleRing R K) (v : HeightOneSpectrum R) :
    inclusion R K x v = x v :=
  rfl

/-- The integral finite adele inclusion is injective. -/
theorem inclusion_injective : Function.Injective (inclusion R K) :=
  RestrictedProduct.isEmbedding_structureMap.injective

/-- A finite field adele is in the integral image exactly when every coordinate is integral. -/
theorem mem_range_inclusion_iff (x : FiniteAdeleRing R K) :
    x ∈ Set.range (inclusion R K) ↔ ∀ v, x v ∈ v.adicCompletionIntegers K := by
  constructor
  · rintro ⟨y, rfl⟩ v
    exact (y v).property
  · intro hx
    refine ⟨fun v ↦ ⟨x v, hx v⟩, ?_⟩
    apply RestrictedProduct.ext
    intro v
    rfl

end FiniteIntegralAdeleRing

/-- The adele ring of a number ring: field completions at infinite places and integral
completions at finite places. -/
abbrev RingAdeleRing [NumberField K] :=
  NumberField.InfiniteAdeleRing K × FiniteIntegralAdeleRing R K

namespace RingAdeleRing

variable [NumberField K]

protected def diagonalRingHom : R →+* RingAdeleRing R K where
  toFun r :=
    (algebraMap K (NumberField.InfiniteAdeleRing K) (algebraMap R K r),
      algebraMap R (FiniteIntegralAdeleRing R K) r)
  map_one' := by change (_, _) = (_, _); simp
  map_mul' _ _ := by change (_, _) = (_, _); simp
  map_zero' := by change (_, _) = (_, _); simp
  map_add' _ _ := by change (_, _) = (_, _); simp

instance : Algebra R (RingAdeleRing R K) :=
  (RingAdeleRing.diagonalRingHom R K).toAlgebra

protected def fieldAdeleDiagonalRingHom : R →+* NumberField.AdeleRing R K :=
  (algebraMap K (NumberField.AdeleRing R K)).comp (algebraMap R K)

instance : Algebra R (NumberField.AdeleRing R K) :=
  (RingAdeleRing.fieldAdeleDiagonalRingHom R K).toAlgebra

/-- The canonical inclusion of ring adeles into the field adele ring. -/
def inclusion : RingAdeleRing R K →A[R] NumberField.AdeleRing R K where
  toAlgHom :=
    { toFun x := (x.1, FiniteIntegralAdeleRing.inclusion R K x.2)
      map_one' := rfl
      map_mul' _ _ := rfl
      map_zero' := rfl
      map_add' _ _ := rfl
      commutes' _ := by
        apply Prod.ext
        · rfl
        · apply RestrictedProduct.ext
          intro v
          rfl }
  cont := continuous_fst.prodMk
    ((FiniteIntegralAdeleRing.inclusion R K).cont.comp continuous_snd)

@[simp]
theorem inclusion_fst (x : RingAdeleRing R K) :
    (inclusion R K x).1 = x.1 :=
  by rfl

@[simp]
theorem inclusion_snd_apply (x : RingAdeleRing R K) (v : HeightOneSpectrum R) :
    (inclusion R K x).2 v = x.2 v :=
  by rfl

/-- The full ring adele inclusion is injective. -/
theorem inclusion_injective : Function.Injective (inclusion R K) := fun x y h ↦ by
  change (x.1, x.2) = (y.1, y.2)
  apply Prod.ext
  · simpa only [inclusion_fst] using congrArg Prod.fst h
  · apply FiniteIntegralAdeleRing.inclusion_injective R K
    change (FiniteIntegralAdeleRing.inclusion R K) x.2 =
      (FiniteIntegralAdeleRing.inclusion R K) y.2
    exact congrArg Prod.snd h

/-- A field adele comes from the ring adele ring exactly when each finite coordinate is integral. -/
theorem mem_range_inclusion_iff (x : NumberField.AdeleRing R K) :
    x ∈ Set.range (inclusion R K) ↔ ∀ v, x.2 v ∈ v.adicCompletionIntegers K := by
  constructor
  · rintro ⟨y, rfl⟩ v
    simpa only [inclusion_snd_apply] using (y.2 v).property
  · intro hx
    let y : RingAdeleRing R K := (x.1, fun v ↦ ⟨x.2 v, hx v⟩)
    refine ⟨y, Prod.ext (inclusion_fst R K y) ?_⟩
    apply RestrictedProduct.ext
    intro v
    rfl

/-- The finite projection from the field adele ring. -/
def finiteProjection : NumberField.AdeleRing R K →ₐ[R] FiniteAdeleRing R K where
  toFun := Prod.snd
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

/-- The algebraic pullback of the finite projection and the integral finite inclusion. -/
abbrev Pullback := AlgHom.pullback (finiteProjection R K)
  (FiniteIntegralAdeleRing.inclusion R K).toAlgHom

/-- The product presentation of ring adeles is the intrinsic pullback presentation. -/
def pullbackAlgEquiv : RingAdeleRing R K ≃ₐ[R] Pullback R K where
  toFun x := ⟨(inclusion R K x, x.2), rfl⟩
  invFun x := (x.1.1.1, x.1.2)
  left_inv _ := rfl
  right_inv x := by
    apply Subtype.ext
    apply Prod.ext
    · apply Prod.ext
      · rfl
      · exact x.2.symm
    · rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
  commutes' _ := by
    apply Subtype.ext
    apply Prod.ext
    · exact (inclusion R K).commutes _
    · rfl

@[simp]
theorem pullbackAlgEquiv_apply_fst (x : RingAdeleRing R K) :
    (pullbackAlgEquiv R K x).1.1 = inclusion R K x :=
  rfl

@[simp]
theorem pullbackAlgEquiv_apply_snd (x : RingAdeleRing R K) :
    (pullbackAlgEquiv R K x).1.2 = x.2 :=
  rfl

end RingAdeleRing

end LeanCategories
