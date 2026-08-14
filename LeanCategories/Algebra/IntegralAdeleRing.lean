/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.Padics.HeightOneSpectrum
public import Mathlib.RingTheory.LocalRing.Pullback
public import Mathlib.Topology.Homeomorph.Lemmas
public import LeanCategories.Modules.TensorProduct.Pi
public import LeanCategories.ForMathlib.AdicCompletionLocallyCompact

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

/-- The product of the local scalar extensions of an `R`-module. -/
abbrev ModuleProduct (M : Type u) [AddCommGroup M] [Module R M] :=
  (v : HeightOneSpectrum R) → TensorProduct R M (v.adicCompletionIntegers K)

/-- For a finite projective module, scalar extension to the integral finite adeles is the
product of its scalar extensions to the completed local integer rings. -/
def tensorProductEquivModuleProduct
    (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M]
    [Module.Projective R M] :
    TensorProduct R M (FiniteIntegralAdeleRing R K) ≃ₗ[R] ModuleProduct R K M :=
  TensorProduct.piRightOfFiniteProjective R
    (fun v : HeightOneSpectrum R ↦ v.adicCompletionIntegers K) M

@[simp]
theorem tensorProductEquivModuleProduct_tmul
    (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M]
    [Module.Projective R M] (x : M) (a : FiniteIntegralAdeleRing R K) :
    tensorProductEquivModuleProduct R K M (x ⊗ₜ[R] a) =
      fun v ↦ x ⊗ₜ[R] a v :=
  rfl

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

/-- The everywhere-integral finite adeles form an open subset of the finite adeles. -/
theorem isOpen_range_inclusion : IsOpen (Set.range (inclusion R K)) := by
  letI : Fact (∀ v : HeightOneSpectrum R,
      IsOpen (v.adicCompletionIntegers K : Set (v.adicCompletion K))) :=
    ⟨fun _ => Valued.isOpen_valuationSubring _⟩
  exact (RestrictedProduct.isOpenEmbedding_structureMap
    (R := fun v : HeightOneSpectrum R => v.adicCompletion K)
    (A := fun v : HeightOneSpectrum R =>
      (v.adicCompletionIntegers K : Set (v.adicCompletion K)))
    (fun _ => Valued.isOpen_valuationSubring _)).isOpen_range

/-- For a number ring, the everywhere-integral finite adeles form a compact subset. -/
theorem isCompact_range_inclusion_numberField
    (K : Type u) [Field K] [NumberField K] :
    IsCompact (Set.range (inclusion (𝓞 K) K)) := by
  letI (v : HeightOneSpectrum (𝓞 K)) :
      CompactSpace (v.adicCompletionIntegers K) := by
    exact HeightOneSpectrum.compactSpaceAdicCompletionIntegers K v
  rw [← Set.image_univ]
  exact isCompact_univ.image (inclusion (𝓞 K) K).continuous

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

namespace Rat

local instance (p : Nat.Primes) : Fact p.1.Prime := ⟨p.2⟩

/-- The standard product presentation of the integral finite adeles of `ℚ`. -/
abbrev PadicIntegerProduct := (p : Nat.Primes) → ℤ_[p]

/-- The local integer completion at a prime ideal of `ℤ` is the corresponding `ℤ_p`. -/
def adicCompletionIntegersEquivPadicInt (v : HeightOneSpectrum ℤ) :
    v.adicCompletionIntegers ℚ ≃+* ℤ_[Rat.HeightOneSpectrum.primesEquiv v] := by
  let e := Rat.HeightOneSpectrum.adicCompletionIntegers.padicIntEquiv v
  exact @AlgEquiv.toRingEquiv ℤ _ _ _ _ _
    (Ring.toIntAlgebra _)
    (Ring.toIntAlgebra _)
    (@ContinuousAlgEquiv.toAlgEquiv ℤ _ _ _ _ _ _ _
      (Ring.toIntAlgebra _)
      (Ring.toIntAlgebra _) e)

theorem continuous_adicCompletionIntegersEquivPadicInt (v : HeightOneSpectrum ℤ) :
    Continuous (adicCompletionIntegersEquivPadicInt v) := by
  let e := Rat.HeightOneSpectrum.adicCompletionIntegers.padicIntEquiv v
  exact @ContinuousAlgEquiv.continuous ℤ _ _ _ _ _ _ _
    (Ring.toIntAlgebra _) (Ring.toIntAlgebra _) e

theorem continuous_adicCompletionIntegersEquivPadicInt_symm (v : HeightOneSpectrum ℤ) :
    Continuous (adicCompletionIntegersEquivPadicInt v).symm := by
  let e := Rat.HeightOneSpectrum.adicCompletionIntegers.padicIntEquiv v
  exact @ContinuousAlgEquiv.continuous_invFun ℤ _ _ _ _ _ _ _
    (Ring.toIntAlgebra _) (Ring.toIntAlgebra _) e

/-- The local integer completion at `v` is homeomorphic to the corresponding `ℤ_p`. -/
def adicCompletionIntegersHomeomorphPadicInt (v : HeightOneSpectrum ℤ) :
    v.adicCompletionIntegers ℚ ≃ₜ ℤ_[Rat.HeightOneSpectrum.primesEquiv v] where
  toEquiv := (adicCompletionIntegersEquivPadicInt v).toEquiv
  continuous_toFun := continuous_adicCompletionIntegersEquivPadicInt v
  continuous_invFun := continuous_adicCompletionIntegersEquivPadicInt_symm v

/-- The integral finite adeles of `ℚ` are the product of the rings `ℤ_p` over all primes. -/
def finiteIntegralAdeleRingEquivPadicIntegerProduct :
    FiniteIntegralAdeleRing ℤ ℚ ≃+* PadicIntegerProduct :=
  (RingEquiv.piCongrRight fun v ↦
    adicCompletionIntegersEquivPadicInt v).trans
    (RingEquiv.piCongrLeft (fun p : Nat.Primes ↦ ℤ_[p])
      (Rat.HeightOneSpectrum.primesEquiv (R := ℤ)))

/-- The standard p-adic product presentation is an equivalence of topological `ℤ`-algebras. -/
def finiteIntegralAdeleRingContinuousAlgEquivPadicIntegerProduct :
    FiniteIntegralAdeleRing ℤ ℚ ≃A[ℤ] PadicIntegerProduct where
  toAlgEquiv :=
    { toRingEquiv := finiteIntegralAdeleRingEquivPadicIntegerProduct
      commutes' := by
        intro n
        simp }
  continuous_toFun := by
    let h : FiniteIntegralAdeleRing ℤ ℚ ≃ₜ PadicIntegerProduct :=
      Homeomorph.piCongr (Rat.HeightOneSpectrum.primesEquiv (R := ℤ)) fun v ↦
        adicCompletionIntegersHomeomorphPadicInt v
    convert h.continuous using 1
    rfl
  continuous_invFun := by
    let h : FiniteIntegralAdeleRing ℤ ℚ ≃ₜ PadicIntegerProduct :=
      Homeomorph.piCongr (Rat.HeightOneSpectrum.primesEquiv (R := ℤ)) fun v ↦
        adicCompletionIntegersHomeomorphPadicInt v
    convert h.symm.continuous using 1
    rfl

/-- The integral finite adeles of the ring of integers of `ℚ` are the product of all `ℤ_p`. -/
def ringOfIntegersFiniteIntegralAdeleRingEquiv :
    FiniteIntegralAdeleRing (𝓞 ℚ) ℚ ≃+* PadicIntegerProduct :=
  (RingEquiv.piCongrRight fun v ↦
    @AlgEquiv.toRingEquiv ℤ _ _ _ _ _ (Ring.toIntAlgebra _) (Ring.toIntAlgebra _)
      (@ContinuousAlgEquiv.toAlgEquiv ℤ _ _ _ _ _ _ _ (Ring.toIntAlgebra _)
        (Ring.toIntAlgebra _)
        (Rat.HeightOneSpectrum.adicCompletionIntegers.padicIntEquiv v))).trans
    (RingEquiv.piCongrLeft (fun p : Nat.Primes ↦ ℤ_[p])
      (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)))

/-- The integral finite adeles of `𝓞 ℚ` are topologically the product of all `ℤ_p`. -/
def ringOfIntegersFiniteIntegralAdeleRingContinuousAlgEquiv :
    FiniteIntegralAdeleRing (𝓞 ℚ) ℚ ≃A[ℤ] PadicIntegerProduct where
  toAlgEquiv :=
    { toRingEquiv := ringOfIntegersFiniteIntegralAdeleRingEquiv
      commutes' := by
        intro n
        simp }
  continuous_toFun := by
    let h : FiniteIntegralAdeleRing (𝓞 ℚ) ℚ ≃ₜ PadicIntegerProduct :=
      Homeomorph.piCongr (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)) fun v ↦
        (Rat.HeightOneSpectrum.adicCompletionIntegers.padicIntEquiv v).toHomeomorph
    exact h.continuous
  continuous_invFun := by
    let h : FiniteIntegralAdeleRing (𝓞 ℚ) ℚ ≃ₜ PadicIntegerProduct :=
      Homeomorph.piCongr (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)) fun v ↦
        (Rat.HeightOneSpectrum.adicCompletionIntegers.padicIntEquiv v).toHomeomorph
    exact h.symm.continuous

/-- The infinite adele ring of `ℚ` is its real completion. -/
def infiniteAdeleRingEquivReal : NumberField.InfiniteAdeleRing ℚ ≃+* ℝ :=
  (RingEquiv.piUnique fun v : NumberField.InfinitePlace ℚ ↦ v.Completion).trans
    (NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal
      Rat.isReal_infinitePlace)

/-- The infinite adele ring of `ℚ` is topologically equivalent to `ℝ`. -/
def infiniteAdeleRingContinuousAlgEquivReal :
    NumberField.InfiniteAdeleRing ℚ ≃A[ℤ] ℝ where
  toAlgEquiv :=
    { toRingEquiv := infiniteAdeleRingEquivReal
      commutes' := by intro n; simp }
  continuous_toFun := by
    let h : NumberField.InfiniteAdeleRing ℚ ≃ₜ ℝ :=
      (Homeomorph.piUnique
        (fun v : NumberField.InfinitePlace ℚ ↦ v.Completion)).trans
          (NumberField.InfinitePlace.Completion.isometryEquivRealOfIsReal
            Rat.isReal_infinitePlace).toHomeomorph
    exact h.continuous
  continuous_invFun := by
    let h : NumberField.InfiniteAdeleRing ℚ ≃ₜ ℝ :=
      (Homeomorph.piUnique
        (fun v : NumberField.InfinitePlace ℚ ↦ v.Completion)).trans
          (NumberField.InfinitePlace.Completion.isometryEquivRealOfIsReal
            Rat.isReal_infinitePlace).toHomeomorph
    exact h.symm.continuous

/-- The standard product model `ℝ × ∏_p ℤ_p` for the ring adeles of `ℚ`. -/
abbrev RingAdeleModel := ℝ × PadicIntegerProduct

end Rat

/-- The adele ring of the full ring of integers of a number field. Its infinite factors are
field completions, and its finite factors are completed integer rings. -/
abbrev RingAdeleRing (K : Type u) [Field K] [NumberField K] :=
  NumberField.InfiniteAdeleRing K × FiniteIntegralAdeleRing (𝓞 K) K

/-- The full ring adele ring attached to a Dedekind domain `R` in a number field `K`.

The finite factor is the product of completed integral local rings.  This is the
integral ring-adelic coefficient object, not Mathlib's field adele ring.
-/
abbrev RingAdeleRingOf (R K : Type u) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] [NumberField K] :=
  NumberField.InfiniteAdeleRing K × FiniteIntegralAdeleRing R K

namespace RingAdeleRingOf

variable (R K : Type u) [CommRing R] [IsDedekindDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K] [NumberField K]

/-- The diagonal embedding of `R` into its full ring adele ring. -/
protected def diagonalRingHom : R →+* RingAdeleRingOf R K where
  toFun r :=
    (algebraMap K (NumberField.InfiniteAdeleRing K) (algebraMap R K r),
      algebraMap R (FiniteIntegralAdeleRing R K) r)
  map_one' := by change (_, _) = (_, _); simp
  map_mul' _ _ := by change (_, _) = (_, _); simp
  map_zero' := by change (_, _) = (_, _); simp
  map_add' _ _ := by change (_, _) = (_, _); simp

instance : Algebra R (RingAdeleRingOf R K) := by
  letI : Algebra R (NumberField.InfiniteAdeleRing K) :=
    Algebra.compHom (NumberField.InfiniteAdeleRing K) (algebraMap R K)
  exact Prod.algebra R (NumberField.InfiniteAdeleRing K)
    (FiniteIntegralAdeleRing R K)

end RingAdeleRingOf

/-- The ring adeles of `ℚ` have the standard presentation `ℝ × ∏_p ℤ_p`. -/
def Rat.ringAdeleRingEquivModel : RingAdeleRing ℚ ≃+* Rat.RingAdeleModel :=
  RingEquiv.prodCongr Rat.infiniteAdeleRingEquivReal
    Rat.ringOfIntegersFiniteIntegralAdeleRingEquiv

/-- The standard model `ℝ × ∏_p ℤ_p` is a topological `ℤ`-algebra presentation. -/
def Rat.ringAdeleRingContinuousAlgEquivModel :
    RingAdeleRing ℚ ≃A[ℤ] Rat.RingAdeleModel where
  toAlgEquiv :=
    { toRingEquiv := Rat.ringAdeleRingEquivModel
      commutes' := by intro n; simp }
  continuous_toFun :=
    (Rat.infiniteAdeleRingContinuousAlgEquivReal.toHomeomorph.prodCongr
      Rat.ringOfIntegersFiniteIntegralAdeleRingContinuousAlgEquiv.toHomeomorph).continuous
  continuous_invFun :=
    (Rat.infiniteAdeleRingContinuousAlgEquivReal.toHomeomorph.prodCongr
      Rat.ringOfIntegersFiniteIntegralAdeleRingContinuousAlgEquiv.toHomeomorph).symm.continuous

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
  Prod.algebra (𝓞 K) (NumberField.InfiniteAdeleRing K)
    (FiniteIntegralAdeleRing (𝓞 K) K)

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

/-- The intrinsic pullback presentation has the same topology as the product presentation. -/
def pullbackContinuousAlgEquiv : RingAdeleRing K ≃A[𝓞 K] Pullback K where
  toAlgEquiv := pullbackAlgEquiv K
  continuous_toFun :=
    ((inclusion K).cont.prodMk continuous_snd).subtype_mk _
  continuous_invFun :=
    (continuous_subtype_val.fst.fst).prodMk continuous_subtype_val.snd

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
