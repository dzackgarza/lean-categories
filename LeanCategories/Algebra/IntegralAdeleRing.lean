/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.LocalRing.Pullback

/-!
# Integral adele rings

This file defines the product of the completed local integer rings of a Dedekind domain.
For a number field, it also defines the full ring adele ring. Its infinite coordinates are
field completions, while all finite coordinates remain integral.
-/

@[expose] public section

noncomputable section

open IsDedekindDomain NumberField
open scoped NumberField
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

/-- The adele ring of the full ring of integers of a number field. Its infinite factors are
field completions, and its finite factors are completed integer rings. -/
abbrev RingAdeleRing (K : Type u) [Field K] [NumberField K] :=
  NumberField.InfiniteAdeleRing K × FiniteIntegralAdeleRing (𝓞 K) K

namespace RingAdeleRing

variable (K : Type u) [Field K] [NumberField K]

protected def diagonalRingHom : (𝓞 K) →+* RingAdeleRing K where
  toFun r :=
    (algebraMap K (NumberField.InfiniteAdeleRing K) (algebraMap (𝓞 K) K r),
      algebraMap (𝓞 K) (FiniteIntegralAdeleRing (𝓞 K) K) r)
  map_one' := by change (_, _) = (_, _); simp
  map_mul' _ _ := by change (_, _) = (_, _); simp
  map_zero' := by change (_, _) = (_, _); simp
  map_add' _ _ := by change (_, _) = (_, _); simp

instance : Algebra (𝓞 K) (RingAdeleRing K) :=
  (RingAdeleRing.diagonalRingHom K).toAlgebra

protected def fieldAdeleDiagonalRingHom : (𝓞 K) →+* NumberField.AdeleRing (𝓞 K) K :=
  (algebraMap K (NumberField.AdeleRing (𝓞 K) K)).comp (algebraMap (𝓞 K) K)

instance : Algebra (𝓞 K) (NumberField.AdeleRing (𝓞 K) K) :=
  (RingAdeleRing.fieldAdeleDiagonalRingHom K).toAlgebra

/-- The canonical inclusion of ring adeles into the field adele ring. -/
def inclusion : RingAdeleRing K →A[𝓞 K] NumberField.AdeleRing (𝓞 K) K where
  toAlgHom :=
    { toFun x := (x.1, FiniteIntegralAdeleRing.inclusion (𝓞 K) K x.2)
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
    ((FiniteIntegralAdeleRing.inclusion (𝓞 K) K).cont.comp continuous_snd)

@[simp]
theorem inclusion_fst (x : RingAdeleRing K) :
    (inclusion K x).1 = x.1 :=
  by rfl

@[simp]
theorem inclusion_snd_apply (x : RingAdeleRing K) (v : HeightOneSpectrum (𝓞 K)) :
    (inclusion K x).2 v = x.2 v :=
  by rfl

/-- The full ring adele inclusion is injective. -/
theorem inclusion_injective : Function.Injective (inclusion K) := fun x y h ↦ by
  change (x.1, x.2) = (y.1, y.2)
  apply Prod.ext
  · simpa only [inclusion_fst] using congrArg Prod.fst h
  · apply FiniteIntegralAdeleRing.inclusion_injective (𝓞 K) K
    change (FiniteIntegralAdeleRing.inclusion (𝓞 K) K) x.2 =
      (FiniteIntegralAdeleRing.inclusion (𝓞 K) K) y.2
    exact congrArg Prod.snd h

/-- A field adele comes from the ring adele ring exactly when each finite coordinate is integral. -/
theorem mem_range_inclusion_iff (x : NumberField.AdeleRing (𝓞 K) K) :
    x ∈ Set.range (inclusion K) ↔ ∀ v, x.2 v ∈ v.adicCompletionIntegers K := by
  constructor
  · rintro ⟨y, rfl⟩ v
    simpa only [inclusion_snd_apply] using (y.2 v).property
  · intro hx
    let y : RingAdeleRing K := (x.1, fun v ↦ ⟨x.2 v, hx v⟩)
    refine ⟨y, Prod.ext (inclusion_fst K y) ?_⟩
    apply RestrictedProduct.ext
    intro v
    rfl

/-- The finite projection from the field adele ring. -/
def finiteProjection :
    NumberField.AdeleRing (𝓞 K) K →ₐ[𝓞 K] FiniteAdeleRing (𝓞 K) K where
  toFun := Prod.snd
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

/-- The algebraic pullback of the finite projection and the integral finite inclusion. -/
abbrev Pullback := AlgHom.pullback (finiteProjection K)
  (FiniteIntegralAdeleRing.inclusion (𝓞 K) K).toAlgHom

/-- The product presentation of ring adeles is the intrinsic pullback presentation. -/
def pullbackAlgEquiv : RingAdeleRing K ≃ₐ[𝓞 K] Pullback K where
  toFun x := ⟨(inclusion K x, x.2), rfl⟩
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
    · exact (inclusion K).commutes _
    · rfl

@[simp]
theorem pullbackAlgEquiv_apply_fst (x : RingAdeleRing K) :
    (pullbackAlgEquiv K x).1.1 = inclusion K x :=
  rfl

@[simp]
theorem pullbackAlgEquiv_apply_snd (x : RingAdeleRing K) :
    (pullbackAlgEquiv K x).1.2 = x.2 :=
  rfl

/-- The diagonal map from the number field to its finite adele ring, as an algebra map over
the ring of integers. -/
def fieldFiniteDiagonal : K →ₐ[𝓞 K] FiniteAdeleRing (𝓞 K) K :=
  IsScalarTower.toAlgHom (𝓞 K) K (FiniteAdeleRing (𝓞 K) K)

/-- The pullback expressing the intersection of the number field and all integral finite
components inside the finite adele ring. -/
abbrev IntegerIntersectionPullback := AlgHom.pullback (fieldFiniteDiagonal K)
  (FiniteIntegralAdeleRing.inclusion (𝓞 K) K).toAlgHom

/-- The canonical map from the ring of integers into the adelic intersection pullback. -/
def integerIntersectionMap :
    (𝓞 K) →ₐ[𝓞 K] IntegerIntersectionPullback K where
  toFun r := ⟨(algebraMap (𝓞 K) K r,
    algebraMap (𝓞 K) (FiniteIntegralAdeleRing (𝓞 K) K) r), rfl⟩
  map_one' := by apply Subtype.ext; apply Prod.ext <;> simp
  map_mul' _ _ := by apply Subtype.ext; apply Prod.ext <;> simp
  map_zero' := by apply Subtype.ext; apply Prod.ext <;> simp
  map_add' _ _ := by apply Subtype.ext; apply Prod.ext <;> simp
  commutes' _ := rfl

/-- The ring of integers is the intersection of the number field with the integral finite
adeles inside the finite field adeles. -/
def integerIntersectionAlgEquiv :
    (𝓞 K) ≃ₐ[𝓞 K] IntegerIntersectionPullback K :=
  AlgEquiv.ofBijective (integerIntersectionMap K) ⟨
    fun x y h ↦ by
      apply RingOfIntegers.ext
      simpa [integerIntersectionMap] using congrArg (fun z ↦ z.1.1) h,
    fun x ↦ by
      have hIntegral : ∀ v : HeightOneSpectrum (𝓞 K), v.valuation K x.1.1 ≤ 1 := by
        intro v
        rw [← HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (v := v)]
        have hcoord := congrArg (fun a : FiniteAdeleRing (𝓞 K) K ↦ a v) x.2
        change (x.1.1 : v.adicCompletion K) = (x.1.2 v : v.adicCompletion K) at hcoord
        rw [hcoord]
        exact (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 K) K v).1
          (x.1.2 v).property
      obtain ⟨r, hr⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one
        K x.1.1 hIntegral
      refine ⟨r, ?_⟩
      apply Subtype.ext
      change (algebraMap (𝓞 K) K r,
        algebraMap (𝓞 K) (FiniteIntegralAdeleRing (𝓞 K) K) r) = x.1
      apply Prod.ext
      · exact hr
      · apply funext
        intro v
        have hcoord := congrArg (fun a : FiniteAdeleRing (𝓞 K) K ↦ a v) x.2
        change (x.1.1 : v.adicCompletion K) = (x.1.2 v : v.adicCompletion K) at hcoord
        apply Subtype.ext
        change (algebraMap (𝓞 K) K r : v.adicCompletion K) =
          (x.1.2 v : v.adicCompletion K)
        rw [hr, hcoord]⟩

end RingAdeleRing

end LeanCategories
