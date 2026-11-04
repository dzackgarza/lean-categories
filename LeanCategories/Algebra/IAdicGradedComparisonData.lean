/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Algebra.AssociatedGraded
public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.LinearAlgebra.TensorProduct.Basic

/-!
# I-adic graded comparison-map data

Definition-level realization of Matsumura FC13-C08-U004.

For an ideal `I ⊲ A` and an `A`-module `M`, Matsumura uses the
homogeneous maps

`(I^n / I^(n+1)) ⊗_{A/I} (M / IM) → I^n M / I^(n+1) M`

and assembles them to

`gr_I(A) ⊗_{A/I} (M/IM) → gr_I(M)`.

The routed associated-graded pieces are quotients by the explicitly embedded
submodules `I^(n+1) ⊆ I^n`.  Mathlib's native `A/I`-module instance is
instead available on the definitionally useful presentation
`I^n / (I • I^n)`.  This file uses that presentation only as the tensor
carrier.  The denominator equality `I • I^n = I^(n+1)` inside `I^n` is proved
(`iAdicTensorRingLower_eq_associatedGradedLower`), both canonical comparison maps are linear by
construction, and data satisfying the representative graph is constructed and exhibited
(`iAdicGradedComparisonMapData`, `isIAdicGradedComparisonMapData_canonical`,
`iAdicGradedComparisonData`), with concrete nonvacuity witnesses over `ℤ` at `I = ⊥`.
Bijectivity of the comparison, its transport to an arbitrary presentation of the graded pieces,
and the comparison theorem at that generality remain Sweep-IV result work.

The tensor product in this file is literally over `A/I`; statements identifying an arbitrary
carrier presentation with the routed associated graded object are still open.
-/

@[expose] public noncomputable section

open DirectSum
open scoped TensorProduct

namespace LeanCategories.Algebra

universe u v

variable {A : Type u} [CommRing A]

/-- The degree-`n` quotient presentation
`I^n / (I • I^n)`.

Unlike the routed `I^n/I^(n+1)` presentation, this carrier receives
Mathlib's native `A/I`-module instance without any local scalar-descent
proof. -/
abbrev IAdicTensorRingPieceData (I : Ideal A) (n : ℕ) :=
  let P : Submodule A A := (I ^ n : Ideal A)
  P ⧸ I • (⊤ : Submodule A P)

/-- The homogeneous direct sum of the tensor-friendly ring-piece
presentations.  This is the proof-free `A/I`-module model used for the
left factor of Matsumura's comparison tensor product. -/
abbrev IAdicTensorRingData (I : Ideal A) :=
  ⨁ n : ℕ, IAdicTensorRingPieceData I n

/-- Matsumura's degree-zero module `M₀=M/IM`, in the native quotient
presentation carrying its `A/I`-module structure. -/
abbrev IAdicTensorModuleZeroData (I : Ideal A) (M : Type v)
    [AddCommGroup M] [Module A M] :=
  M ⧸ I • (⊤ : Submodule A M)

/-- Literal tensor carrier over `A₀=A/I` for the graded comparison map. -/
abbrev IAdicGradedComparisonTensorData (I : Ideal A) (M : Type v)
    [AddCommGroup M] [Module A M] :=
  IAdicTensorRingData I ⊗[A ⧸ I] IAdicTensorModuleZeroData I M

/-- The tensor-friendly denominator `I • I^n` is exactly the routed
`I^(n+1)` denominator inside `I^n`. -/
lemma iAdicTensorRingLower_eq_associatedGradedLower
    (I : Ideal A) (n : ℕ) :
    I • (⊤ : Submodule A ↥((I ^ n : Ideal A) : Submodule A A)) =
      Ideal.associatedGradedRingLower I n := by
  ext a
  rw [Submodule.mem_smul_top_iff]
  change a.1 ∈ (I : Submodule A A) • (I ^ n : Ideal A) ↔ a.1 ∈ I ^ (n + 1)
  rw [Ideal.smul_eq_mul, pow_succ, mul_comm]

/-- Canonical identification of the tensor-friendly degree-`n` quotient
with the degree-`n` associated-graded piece. -/
noncomputable def iAdicTensorRingPieceEquiv
    (I : Ideal A) (n : ℕ) :
    IAdicTensorRingPieceData I n ≃ₗ[A]
      Ideal.IAdicAssociatedGradedPiece I n :=
  Submodule.quotEquivOfEq _ _
    (iAdicTensorRingLower_eq_associatedGradedLower I n)

/-- Degreewise assembly of the canonical quotient identifications. -/
noncomputable def iAdicTensorRingToAssociatedGraded
    (I : Ideal A) :
    IAdicTensorRingData I →ₗ[A] Ideal.IAdicAssociatedGraded I :=
  DirectSum.toModule A ℕ (Ideal.IAdicAssociatedGraded I)
    (fun n =>
      (DirectSum.lof A ℕ (Ideal.IAdicAssociatedGradedPiece I) n).comp
        (iAdicTensorRingPieceEquiv I n).toLinearMap)

/-- The degree-zero map `A → gr_I(A)`. -/
noncomputable def iAdicAssociatedGradedDegreeZeroRingHom
    (I : Ideal A) : A →+* Ideal.AssociatedGradedRing I where
  toFun a :=
    DirectSum.of (Ideal.AssociatedGradedRingPiece I) 0
      (Ideal.associatedGradedRingMk I 0 ⟨a, by simp⟩)
  map_zero' := by
    change DirectSum.of _ 0
        (Ideal.associatedGradedRingMk I 0 ⟨0, by simp⟩) = 0
    rw [show Ideal.associatedGradedRingMk I 0 ⟨0, by simp⟩ = 0 by
      exact map_zero _]
    exact DFinsupp.single_zero 0
  map_one' := by rfl
  map_add' a b := by
    change DirectSum.of _ 0
      (Ideal.associatedGradedRingMk I 0 ⟨a + b, by simp⟩) = _
    rw [← map_add]
    rfl
  map_mul' a b := by
    rw [← DirectSum.of_zero_mul]
    congr 1

/-- The canonical ring homomorphism `A/I → gr_I(A)` induced in degree zero. -/
noncomputable def iAdicQuotientToAssociatedGradedRing
    (I : Ideal A) : (A ⧸ I) →+* Ideal.AssociatedGradedRing I :=
  Ideal.Quotient.lift I (iAdicAssociatedGradedDegreeZeroRingHom I) (by
    intro a ha
    change DirectSum.of _ 0
        (Ideal.associatedGradedRingMk I 0 ⟨a, by simp⟩) = 0
    have hq : Ideal.associatedGradedRingMk I 0 ⟨a, by simp⟩ = 0 := by
      change (Submodule.Quotient.mk _ :
        Ideal.AssociatedGradedRingPiece I 0) = 0
      rw [Submodule.Quotient.mk_eq_zero]
      simpa using ha
    rw [hq]
    exact DFinsupp.single_zero 0)

/-- The degreewise ring-model comparison, now linear over the actual
degree-zero quotient ring `A/I`. -/
noncomputable def iAdicTensorRingToAssociatedGradedQuotientLinear
    (I : Ideal A) :
    letI : Module (A ⧸ I) (Ideal.IAdicAssociatedGraded I) :=
      Module.compHom _ (iAdicQuotientToAssociatedGradedRing I)
    IAdicTensorRingData I →ₗ[A ⧸ I] Ideal.IAdicAssociatedGraded I := by
  letI : Module (A ⧸ I) (Ideal.IAdicAssociatedGraded I) :=
    Module.compHom _ (iAdicQuotientToAssociatedGradedRing I)
  refine
    { toFun := iAdicTensorRingToAssociatedGraded I
      map_add' := (iAdicTensorRingToAssociatedGraded I).map_add
      map_smul' := ?_ }
  intro c x
  induction x using DirectSum.induction_on with
  | zero => simp
  | of n x =>
      induction c using Quotient.inductionOn' with
      | _ r =>
          induction x using Submodule.Quotient.induction_on with
          | _ a =>
              change iAdicTensorRingToAssociatedGraded I
                  (Ideal.Quotient.mk I r •
                    DirectSum.of (IAdicTensorRingPieceData I) n
                      (Submodule.Quotient.mk a)) = _
              rw [← DirectSum.of_smul]
              simp only [iAdicTensorRingToAssociatedGraded,
                ← DirectSum.lof_eq_of (R := A),
                DirectSum.toModule_lof, LinearMap.comp_apply]
              change DirectSum.of _ n
                  (iAdicTensorRingPieceEquiv I n
                    (Ideal.Quotient.mk I r • Submodule.Quotient.mk a)) =
                iAdicQuotientToAssociatedGradedRing I
                    (Ideal.Quotient.mk I r) *
                  DirectSum.of _ n
                    (iAdicTensorRingPieceEquiv I n
                      (Submodule.Quotient.mk a))
              rw [show iAdicQuotientToAssociatedGradedRing I
                    (Ideal.Quotient.mk I r) =
                  iAdicAssociatedGradedDegreeZeroRingHom I r by rfl]
              change DirectSum.of _ n
                  (iAdicTensorRingPieceEquiv I n
                    (Ideal.Quotient.mk I r • Submodule.Quotient.mk a)) =
                DirectSum.of _ 0
                    (Ideal.associatedGradedRingMk I 0 ⟨r, by simp⟩) *
                  DirectSum.of _ n
                    (Ideal.associatedGradedRingMk I n a)
              rw [DirectSum.of_mul_of]
              change _ = DirectSum.of _ (0 + n)
                (Ideal.associatedGradedRingMul I 0 n
                  (Ideal.associatedGradedRingMk I 0 ⟨r, by simp⟩)
                  (Ideal.associatedGradedRingMk I n a))
              rw [Ideal.associatedGradedRingMul_mk']
              have hpiece :
                  iAdicTensorRingPieceEquiv I n
                      (Ideal.Quotient.mk I r • Submodule.Quotient.mk a) =
                    Ideal.associatedGradedRingMk I n
                      ⟨r * a.1, by exact (I ^ n).mul_mem_left r a.2⟩ := by
                change r • Submodule.Quotient.mk a =
                  Submodule.Quotient.mk
                    (p := Ideal.associatedGradedRingLower I n)
                    ⟨r * a.1, by exact (I ^ n).mul_mem_left r a.2⟩
                rfl
              rw [hpiece]
              apply DirectSum.of_eq_of_gradedMonoid_eq
              exact Sigma.ext (zero_add n).symm
                (Ideal.associatedGradedRingMk_heq_of_eq I
                  (zero_add n).symm rfl
                  ((I ^ n).mul_mem_left r a.2)
                  (by simpa using (I ^ n).mul_mem_left r a.2))
  | add x y hx hy =>
      rw [smul_add, map_add, hx, hy, map_add, smul_add]

/-- The degree-zero numerator of the stable filtration is canonically `M`. -/
noncomputable def iAdicDegreeZeroNumeratorEquiv
    (I : Ideal A) (M : Type v) [AddCommGroup M] [Module A M] :
    (I.stableFiltration (⊤ : Submodule A M)).N 0 ≃ₗ[A] M where
  toFun x := x.1
  invFun m := ⟨m, by simp [Ideal.stableFiltration]⟩
  left_inv x := Subtype.ext rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma iAdicDegreeZeroLower_map
    (I : Ideal A) (M : Type v) [AddCommGroup M] [Module A M] :
    Submodule.map (iAdicDegreeZeroNumeratorEquiv I M).toLinearMap
        ((I.stableFiltration (⊤ : Submodule A M)).associatedGradedModuleLower 0) =
      I • (⊤ : Submodule A M) := by
  ext m
  constructor
  · rintro ⟨x, hx, rfl⟩
    change x.1 ∈ I ^ (0 + 1) • (⊤ : Submodule A M) at hx
    change x.1 ∈ I • (⊤ : Submodule A M)
    simpa using hx
  · intro hm
    refine ⟨⟨m, by simp [Ideal.stableFiltration]⟩, ?_, rfl⟩
    change m ∈ I ^ (0 + 1) • (⊤ : Submodule A M)
    simpa using hm

/-- Canonical identification `gr_I(M)_0 ≃ M/IM`. -/
noncomputable def iAdicDegreeZeroModuleEquiv
    (I : Ideal A) (M : Type v) [AddCommGroup M] [Module A M] :
    Ideal.IAdicAssociatedGradedModulePiece I M 0 ≃ₗ[A]
      IAdicTensorModuleZeroData I M :=
  Submodule.Quotient.equiv
    ((I.stableFiltration (⊤ : Submodule A M)).associatedGradedModuleLower 0)
    (I • (⊤ : Submodule A M))
    (iAdicDegreeZeroNumeratorEquiv I M)
    (iAdicDegreeZeroLower_map I M)

/-- The canonical inclusion of `M/IM` into degree zero of `gr_I(M)`. -/
noncomputable def iAdicModuleZeroToAssociatedGraded
    (I : Ideal A) (M : Type v) [AddCommGroup M] [Module A M] :
    IAdicTensorModuleZeroData I M →ₗ[A]
      Ideal.IAdicAssociatedGradedModule I M :=
  (DirectSum.lof A ℕ (Ideal.IAdicAssociatedGradedModulePiece I M) 0).comp
    (iAdicDegreeZeroModuleEquiv I M).symm.toLinearMap

/-- The degree-zero inclusion, linear over `A/I`. -/
noncomputable def iAdicModuleZeroToAssociatedGradedQuotientLinear
    (I : Ideal A) (M : Type v) [AddCommGroup M] [Module A M] :
    letI : Module (A ⧸ I) (Ideal.IAdicAssociatedGradedModule I M) :=
      Module.compHom _ (iAdicQuotientToAssociatedGradedRing I)
    IAdicTensorModuleZeroData I M →ₗ[A ⧸ I]
      Ideal.IAdicAssociatedGradedModule I M := by
  letI : Module (A ⧸ I) (Ideal.IAdicAssociatedGradedModule I M) :=
    Module.compHom _ (iAdicQuotientToAssociatedGradedRing I)
  refine
    { toFun := iAdicModuleZeroToAssociatedGraded I M
      map_add' := (iAdicModuleZeroToAssociatedGraded I M).map_add
      map_smul' := ?_ }
  intro c x
  induction c using Quotient.inductionOn' with
  | _ r =>
      induction x using Submodule.Quotient.induction_on with
      | _ m =>
          change iAdicModuleZeroToAssociatedGraded I M
              (Ideal.Quotient.mk I r • Submodule.Quotient.mk m) = _
          change iAdicModuleZeroToAssociatedGraded I M
              (Submodule.Quotient.mk (r • m)) = _
          simp only [iAdicModuleZeroToAssociatedGraded]
          change DirectSum.of _ 0
              ((I.stableFiltration (⊤ : Submodule A M)).associatedGradedModuleMk 0
                ⟨r • m, by simp⟩) =
            iAdicQuotientToAssociatedGradedRing I (Ideal.Quotient.mk I r) •
              DirectSum.of _ 0
                ((I.stableFiltration (⊤ : Submodule A M)).associatedGradedModuleMk 0
                  ⟨m, by simp⟩)
          rw [show iAdicQuotientToAssociatedGradedRing I
                (Ideal.Quotient.mk I r) =
              iAdicAssociatedGradedDegreeZeroRingHom I r by rfl]
          rw [show iAdicAssociatedGradedDegreeZeroRingHom I r =
              DirectSum.of (Ideal.AssociatedGradedRingPiece I) 0
                (Ideal.associatedGradedRingMk I 0 ⟨r, by simp⟩) by rfl]
          rw [DirectSum.Gmodule.of_smul_of]
          change DirectSum.of _ 0
              ((I.stableFiltration (⊤ : Submodule A M)).associatedGradedModuleMk 0
                ⟨r • m, by simp⟩) =
            DirectSum.of _ (0 + 0)
              ((I.stableFiltration (⊤ : Submodule A M)).associatedGradedModuleSMul 0 0
                (Ideal.associatedGradedRingMk I 0 ⟨r, by simp⟩)
                ((I.stableFiltration (⊤ : Submodule A M)).associatedGradedModuleMk 0
                  ⟨m, by simp⟩))
          rw [(I.stableFiltration (⊤ : Submodule A M)).associatedGradedModuleSMul_mk']

/-- Bilinear form underlying Matsumura's comparison map. -/
noncomputable def iAdicGradedComparisonBilinear
    (I : Ideal A) (M : Type v) [AddCommGroup M] [Module A M] :
    letI : Module (A ⧸ I) (Ideal.IAdicAssociatedGraded I) :=
      Module.compHom _ (iAdicQuotientToAssociatedGradedRing I)
    letI : Module (A ⧸ I) (Ideal.IAdicAssociatedGradedModule I M) :=
      Module.compHom _ (iAdicQuotientToAssociatedGradedRing I)
    IAdicTensorRingData I →ₗ[A ⧸ I]
      IAdicTensorModuleZeroData I M →ₗ[A ⧸ I]
        Ideal.IAdicAssociatedGradedModule I M := by
  letI : Module (A ⧸ I) (Ideal.IAdicAssociatedGraded I) :=
    Module.compHom _ (iAdicQuotientToAssociatedGradedRing I)
  letI : Module (A ⧸ I) (Ideal.IAdicAssociatedGradedModule I M) :=
    Module.compHom _ (iAdicQuotientToAssociatedGradedRing I)
  exact LinearMap.mk₂ (A ⧸ I)
    (fun x y =>
      iAdicTensorRingToAssociatedGradedQuotientLinear I x •
        iAdicModuleZeroToAssociatedGradedQuotientLinear I M y)
    (fun x x' y => by rw [map_add, add_smul])
    (fun c x y => by
      rw [map_smul]
      change
        (iAdicQuotientToAssociatedGradedRing I c *
          iAdicTensorRingToAssociatedGradedQuotientLinear I x) •
            iAdicModuleZeroToAssociatedGradedQuotientLinear I M y =
          iAdicQuotientToAssociatedGradedRing I c •
            (iAdicTensorRingToAssociatedGradedQuotientLinear I x •
              iAdicModuleZeroToAssociatedGradedQuotientLinear I M y)
      rw [mul_smul])
    (fun x y y' => by rw [map_add, smul_add])
    (fun c x y => by
      rw [map_smul]
      change
        iAdicTensorRingToAssociatedGradedQuotientLinear I x •
            (iAdicQuotientToAssociatedGradedRing I c •
              iAdicModuleZeroToAssociatedGradedQuotientLinear I M y) =
          iAdicQuotientToAssociatedGradedRing I c •
            (iAdicTensorRingToAssociatedGradedQuotientLinear I x •
              iAdicModuleZeroToAssociatedGradedQuotientLinear I M y)
      rw [← mul_smul, ← mul_smul, mul_comm])

/-- Matsumura's actual graded comparison map
`gr_I(A) ⊗_{A/I} M/IM → gr_I(M)` in the tensor-friendly presentation. -/
noncomputable def iAdicGradedComparisonMap
    (I : Ideal A) (M : Type v) [AddCommGroup M] [Module A M] :
    letI : Module (A ⧸ I) (Ideal.IAdicAssociatedGradedModule I M) :=
      Module.compHom _ (iAdicQuotientToAssociatedGradedRing I)
    IAdicGradedComparisonTensorData I M →ₗ[A ⧸ I]
      Ideal.IAdicAssociatedGradedModule I M := by
  letI : Module (A ⧸ I) (Ideal.IAdicAssociatedGraded I) :=
    Module.compHom _ (iAdicQuotientToAssociatedGradedRing I)
  letI : Module (A ⧸ I) (Ideal.IAdicAssociatedGradedModule I M) :=
    Module.compHom _ (iAdicQuotientToAssociatedGradedRing I)
  exact TensorProduct.lift (iAdicGradedComparisonBilinear I M)

/-- Raw construction data for Matsumura's graded comparison map.

The first two functions record the canonical comparison of the tensor-friendly
quotient presentations with the routed associated-graded pieces.  The final
function has the literal source tensor product over `A/I` and the routed
associated-graded module as target.

The first two canonical maps are already linear, and the tensor-friendly denominator equality
`I • I^n = I^(n+1)` inside `I^n` is proved (`iAdicTensorRingLower_eq_associatedGradedLower`), so
descent and linearity for these fields are established, not open. The representative graph
`IsIAdicGradedComparisonMapData` is also proved for the canonical data
(`isIAdicGradedComparisonMapData_canonical`). What remains open is specialization: the map is
built on the tensor-friendly quotient presentation, and transporting it to a general
presentation, together with representative independence of the quotient/scalar descent for
arbitrary presentations, are still obligations. -/
structure IAdicGradedComparisonMapData (I : Ideal A) (M : Type v)
    [AddCommGroup M] [Module A M] where
  ringModelToGraded :
    IAdicTensorRingData I → Ideal.IAdicAssociatedGraded I
  moduleZeroToGraded :
    IAdicTensorModuleZeroData I M →
      Ideal.IAdicAssociatedGradedModulePiece I M 0
  comparison :
    IAdicGradedComparisonTensorData I M →
      Ideal.IAdicAssociatedGradedModule I M

/-- The tensor-friendly piece equivalence is the identity on representatives: both it and
`associatedGradedRingMk` are the quotient map. -/
theorem iAdicTensorRingPieceEquiv_mk (I : Ideal A) (n : ℕ)
    (a : ↥((I ^ n : Ideal A) : Submodule A A)) :
    iAdicTensorRingPieceEquiv I n (Submodule.Quotient.mk a) =
      Ideal.associatedGradedRingMk I n a := by
  rfl

/-- The comparison data built from the canonical maps already constructed above:
`iAdicTensorRingToAssociatedGraded`, the degree-zero equivariance
`(iAdicDegreeZeroModuleEquiv I M).symm`, and Matsumura's `iAdicGradedComparisonMap`.

All three are already linear maps (`→ₗ[A]`, `≃ₗ[A]`, and `→ₗ[A ⧸ I]`), so quotient/scalar
descent and linearity are established by those constructions, not left open; what remains for
this row is the representative graph `IsIAdicGradedComparisonMapData`. Source, target and
universes are exactly those of the existing maps. -/
noncomputable def iAdicGradedComparisonMapData
    (I : Ideal A) (M : Type v) [AddCommGroup M] [Module A M] :
    IAdicGradedComparisonMapData I M where
  ringModelToGraded := iAdicTensorRingToAssociatedGraded I
  moduleZeroToGraded := (iAdicDegreeZeroModuleEquiv I M).symm
  comparison := iAdicGradedComparisonMap I M

/-- Second graph clause of `IsIAdicGradedComparisonMapData` for the canonical data: the
degree-zero component is the quotient map on representatives. -/
theorem iAdicGradedComparisonMapData_zero_clause
    (I : Ideal A) (M : Type v) [AddCommGroup M] [Module A M] (m : M) :
    (iAdicGradedComparisonMapData I M).moduleZeroToGraded
        (Submodule.Quotient.mk (p := I • (⊤ : Submodule A M)) m) =
      (I.stableFiltration (⊤ : Submodule A M)).associatedGradedModuleMk 0
        ⟨m, by
          change m ∈ I ^ 0 • (⊤ : Submodule A M)
          simp⟩ := by
  rfl

/-- The degree-zero component of the comparison on a quotient representative. -/
theorem iAdicModuleZeroToAssociatedGraded_of
    (I : Ideal A) (M : Type v) [AddCommGroup M] [Module A M] (m : M) :
    iAdicModuleZeroToAssociatedGraded I M
        (Submodule.Quotient.mk (p := I • (⊤ : Submodule A M)) m) =
      DirectSum.of (Ideal.IAdicAssociatedGradedModulePiece I M) 0
        ((I.stableFiltration (⊤ : Submodule A M)).associatedGradedModuleMk 0
          ⟨m, by
            change m ∈ I ^ 0 • (⊤ : Submodule A M)
            simp⟩) := rfl

/-- The ring component of the comparison on a direct-sum representative. -/
theorem iAdicTensorRingToAssociatedGraded_of
    (I : Ideal A) (n : ℕ) (a : ↥((I ^ n : Ideal A) : Submodule A A)) :
    iAdicTensorRingToAssociatedGraded I
        (DirectSum.of (IAdicTensorRingPieceData I) n (Submodule.Quotient.mk a)) =
      DirectSum.of (Ideal.IAdicAssociatedGradedPiece I) n
        (Ideal.associatedGradedRingMk I n a) := by
  simp only [iAdicTensorRingToAssociatedGraded]
  rw [← DirectSum.lof_eq_of A ℕ (IAdicTensorRingPieceData I) n (Submodule.Quotient.mk a)]
  rw [DirectSum.toModule_lof]
  rw [LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [iAdicTensorRingPieceEquiv_mk]
  rw [DirectSum.lof_eq_of A ℕ (Ideal.IAdicAssociatedGradedPiece I) n
    (Ideal.associatedGradedRingMk I n a)]

/-- Third graph clause: Matsumura's homogeneous formula on a pure tensor. -/
theorem iAdicGradedComparisonMapData_tensor_clause
    (I : Ideal A) (M : Type v) [AddCommGroup M] [Module A M]
    (n : ℕ) (a : ↥((I ^ n : Ideal A) : Submodule A A)) (m : M) :
    (iAdicGradedComparisonMapData I M).comparison
        ((DirectSum.of (IAdicTensorRingPieceData I) n
            (Submodule.Quotient.mk
              (p := I • (⊤ : Submodule A ↥((I ^ n : Ideal A) : Submodule A A))) a)) ⊗ₜ[A ⧸ I]
          (Submodule.Quotient.mk (p := I • (⊤ : Submodule A M)) m)) =
      DirectSum.of (Ideal.IAdicAssociatedGradedModulePiece I M) n
        ((I.stableFiltration (⊤ : Submodule A M)).associatedGradedModuleMk n
          ⟨a.1 • m, by
            change a.1 • m ∈ I ^ n • (⊤ : Submodule A M)
            exact Submodule.smul_mem_smul a.2 Submodule.mem_top⟩) := by
  letI : Module (A ⧸ I) (Ideal.IAdicAssociatedGraded I) :=
    Module.compHom _ (iAdicQuotientToAssociatedGradedRing I)
  letI : Module (A ⧸ I) (Ideal.IAdicAssociatedGradedModule I M) :=
    Module.compHom _ (iAdicQuotientToAssociatedGradedRing I)
  show TensorProduct.lift (iAdicGradedComparisonBilinear I M) _ = _
  rw [TensorProduct.lift.tmul]
  show iAdicTensorRingToAssociatedGradedQuotientLinear I
        (DirectSum.of (IAdicTensorRingPieceData I) n (Submodule.Quotient.mk a)) •
      iAdicModuleZeroToAssociatedGradedQuotientLinear I M
        (Submodule.Quotient.mk (p := I • (⊤ : Submodule A M)) m) = _
  rw [show iAdicTensorRingToAssociatedGradedQuotientLinear I
        (DirectSum.of (IAdicTensorRingPieceData I) n (Submodule.Quotient.mk a)) =
      iAdicTensorRingToAssociatedGraded I
        (DirectSum.of (IAdicTensorRingPieceData I) n (Submodule.Quotient.mk a)) from rfl]
  rw [show iAdicModuleZeroToAssociatedGradedQuotientLinear I M
        (Submodule.Quotient.mk (p := I • (⊤ : Submodule A M)) m) =
      iAdicModuleZeroToAssociatedGraded I M
        (Submodule.Quotient.mk (p := I • (⊤ : Submodule A M)) m) from rfl]
  rw [iAdicTensorRingToAssociatedGraded_of, iAdicModuleZeroToAssociatedGraded_of]
  rw [DirectSum.Gmodule.of_smul_of]
  change DirectSum.of (Ideal.IAdicAssociatedGradedModulePiece I M) (n + 0)
      ((I.stableFiltration (⊤ : Submodule A M)).associatedGradedModuleSMul n 0
        (Ideal.associatedGradedRingMk I n a)
        ((I.stableFiltration (⊤ : Submodule A M)).associatedGradedModuleMk 0
          ⟨m, by
            change m ∈ I ^ 0 • (⊤ : Submodule A M)
            simp⟩)) = _
  rw [Ideal.Filtration.associatedGradedModuleSMul_mk']
  rw [DirectSum.of_eq_of_gradedMonoid_eq]
  exact Sigma.ext (Nat.add_zero n)
    (Ideal.Filtration.associatedGradedModuleMk_heq_of_eq (F := I.stableFiltration (⊤ : Submodule A M))
      (Nat.add_zero n) rfl _ _)

/-- First graph clause of `IsIAdicGradedComparisonMapData` for the canonical data: the ring
component is the identity on direct-sum representatives. -/
theorem iAdicGradedComparisonMapData_ring_clause
    (I : Ideal A) (M : Type v) [AddCommGroup M] [Module A M]
    (n : ℕ) (a : ↥((I ^ n : Ideal A) : Submodule A A)) :
    (iAdicGradedComparisonMapData I M).ringModelToGraded
        (DirectSum.of (IAdicTensorRingPieceData I) n (Submodule.Quotient.mk a)) =
      DirectSum.of (Ideal.IAdicAssociatedGradedPiece I) n
        (Ideal.associatedGradedRingMk I n a) := by
  simp only [iAdicGradedComparisonMapData, iAdicTensorRingToAssociatedGraded]
  rw [← DirectSum.lof_eq_of A ℕ (IAdicTensorRingPieceData I) n (Submodule.Quotient.mk a)]
  rw [DirectSum.toModule_lof]
  rw [LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [iAdicTensorRingPieceEquiv_mk]
  rw [DirectSum.lof_eq_of A ℕ (Ideal.IAdicAssociatedGradedPiece I) n
    (Ideal.associatedGradedRingMk I n a)]

instance (I : Ideal A) (M : Type v) [AddCommGroup M] [Module A M] :
    Nonempty (IAdicGradedComparisonMapData I M) :=
  ⟨{
    ringModelToGraded := fun _ => 0
    moduleZeroToGraded := fun _ => 0
    comparison := fun _ => 0
  }⟩

/-- Exact representative graph for the comparison construction.

The first clause identifies the tensor-friendly degree-`n` quotient model
with the routed associated-graded ring piece on representatives.  The second
does the same for `M/IM`.  The third is Matsumura's homogeneous formula:
the pure tensor of the classes of `a ∈ I^n` and `m ∈ M` maps to the class
of `a • m` in degree `n` of `gr_I(M)`.

Existence of data satisfying this graph is proved for the canonical data
(`isIAdicGradedComparisonMapData_canonical`), which also exhibits an element of the subtype
`IAdicGradedComparisonData`. What remains a result-layer obligation is representative
independence for an arbitrary presentation, and the identification of these formulas with the
usual comparison homomorphism at a general presentation without the tensor-friendly quotient
model. Callers that need the proved witness must use `iAdicGradedComparisonData`: the raw
`Nonempty` instance is the zero family written out explicitly, so it does not select the
canonical data. -/
def IsIAdicGradedComparisonMapData
    (I : Ideal A) (M : Type v) [AddCommGroup M] [Module A M]
    (D : IAdicGradedComparisonMapData I M) : Prop :=
  let F := I.stableFiltration (⊤ : Submodule A M)
  (∀ (n : ℕ) (a : ↥((I ^ n : Ideal A) : Submodule A A)),
      D.ringModelToGraded
          (DirectSum.of (IAdicTensorRingPieceData I) n
            (Submodule.Quotient.mk a)) =
        DirectSum.of (Ideal.IAdicAssociatedGradedPiece I) n
          (Ideal.associatedGradedRingMk I n a)) ∧
    (∀ m : M,
      D.moduleZeroToGraded
          (Submodule.Quotient.mk
            (p := I • (⊤ : Submodule A M)) m) =
        F.associatedGradedModuleMk 0
          ⟨m, by
            change m ∈ I ^ 0 • (⊤ : Submodule A M)
            simp⟩) ∧
    ∀ (n : ℕ) (a : ↥((I ^ n : Ideal A) : Submodule A A)) (m : M),
      D.comparison
          (DirectSum.of (IAdicTensorRingPieceData I) n
              (Submodule.Quotient.mk
                (p := I •
                  (⊤ : Submodule A
                    ↥((I ^ n : Ideal A) : Submodule A A))) a) ⊗ₜ[A ⧸ I]
            Submodule.Quotient.mk
              (p := I • (⊤ : Submodule A M)) m) =
        DirectSum.of
          (Ideal.IAdicAssociatedGradedModulePiece I M) n
          (F.associatedGradedModuleMk n
            ⟨a.1 • m, by
              change a.1 • m ∈ I ^ n • (⊤ : Submodule A M)
              exact Submodule.smul_mem_smul a.2 Submodule.mem_top⟩)

/-- The carrier of all comparison-map data satisfying Matsumura's exact
homogeneous representative graph.  No map is selected before quotient/scalar
descent and well-definedness are proved. -/
def IAdicGradedComparisonData
    (I : Ideal A) (M : Type v) [AddCommGroup M] [Module A M] :=
  {D : IAdicGradedComparisonMapData I M // IsIAdicGradedComparisonMapData I M D}

/-- Nondegenerate control: on a representative whose graded class is nonzero, the canonical ring
component is nonzero, so it is not the zero family. -/
theorem iAdicGradedComparisonMapData_ring_component_ne_zero
    (I : Ideal A) (M : Type v) [AddCommGroup M] [Module A M]
    (n : ℕ) (a : ↥((I ^ n : Ideal A) : Submodule A A))
    (ha : Ideal.associatedGradedRingMk I n a ≠ 0) :
    (iAdicGradedComparisonMapData I M).ringModelToGraded
        (DirectSum.of (IAdicTensorRingPieceData I) n (Submodule.Quotient.mk a)) ≠ 0 := by
  rw [iAdicGradedComparisonMapData_ring_clause]
  intro h
  exact ha ((DirectSum.of_injective (β := Ideal.IAdicAssociatedGradedPiece I) n)
    (by simpa only [map_zero] using h))

/-- Concrete tensor control: over `ℤ` with `I = ⊥` in degree `0`, the comparison of `[1] ⊗ [1]` is
nonzero, so the tensor graph clause is also nonvacuous. -/
theorem iAdicGradedComparisonMapData_tensor_component_ne_zero_int :
    (iAdicGradedComparisonMapData (⊥ : Ideal ℤ) ℤ).comparison
      ((DirectSum.of (IAdicTensorRingPieceData (⊥ : Ideal ℤ)) 0
          (Submodule.Quotient.mk
            (⟨(1 : ℤ), by
              change (1 : ℤ) ∈ (⊥ : Ideal ℤ) ^ 0
              simp⟩ : ↥(((⊥ : Ideal ℤ) ^ 0 : Ideal ℤ) : Submodule ℤ ℤ)))) ⊗ₜ[ℤ ⧸ (⊥ : Ideal ℤ)]
        (Submodule.Quotient.mk (p := (⊥ : Ideal ℤ) • (⊤ : Submodule ℤ ℤ)) (1 : ℤ))) ≠ 0 := by
  rw [iAdicGradedComparisonMapData_tensor_clause]
  intro h
  have hx := congrArg (fun z => z 0) h
  simp only [DirectSum.of_eq_same, DirectSum.zero_apply] at hx
  have hmem := (Submodule.Quotient.mk_eq_zero _).mp hx
  simpa using hmem

/-- The control's hypothesis is inhabited: over `ℤ` with the zero ideal in degree `0`, the class
of `1` has nonzero associated-graded representative, because the denominator is `⊥`. -/
theorem associatedGradedRingMk_one_ne_zero :
    Ideal.associatedGradedRingMk (⊥ : Ideal ℤ) 0
      (⟨(1 : ℤ), by
        change (1 : ℤ) ∈ (⊥ : Ideal ℤ) ^ 0
        simp⟩ : ↥(((⊥ : Ideal ℤ) ^ 0 : Ideal ℤ) : Submodule ℤ ℤ)) ≠ 0 := by
  intro h
  have hmem := (Submodule.Quotient.mk_eq_zero _).mp h
  simpa using hmem

/-- Concrete nonvacuous instance of the control: `A = M = ℤ`, `I = ⊥`, `n = 0`, `a = 1`. -/
theorem iAdicGradedComparisonMapData_ring_component_ne_zero_int :
    (iAdicGradedComparisonMapData (⊥ : Ideal ℤ) ℤ).ringModelToGraded
      (DirectSum.of (IAdicTensorRingPieceData (⊥ : Ideal ℤ)) 0
        (Submodule.Quotient.mk
          (⟨(1 : ℤ), by
            change (1 : ℤ) ∈ (⊥ : Ideal ℤ) ^ 0
            simp⟩ : ↥(((⊥ : Ideal ℤ) ^ 0 : Ideal ℤ) : Submodule ℤ ℤ)))) ≠ 0 :=
  iAdicGradedComparisonMapData_ring_component_ne_zero (⊥ : Ideal ℤ) ℤ 0 _ 
    associatedGradedRingMk_one_ne_zero

/-- The canonical comparison data satisfies Matsumura's exact representative graph. -/
theorem isIAdicGradedComparisonMapData_canonical
    (I : Ideal A) (M : Type v) [AddCommGroup M] [Module A M] :
    IsIAdicGradedComparisonMapData I M (iAdicGradedComparisonMapData I M) :=
  ⟨iAdicGradedComparisonMapData_ring_clause I M,
   iAdicGradedComparisonMapData_zero_clause I M,
   iAdicGradedComparisonMapData_tensor_clause I M⟩

/-- The canonical comparison data as an element of the exact graph subtype. -/
noncomputable def iAdicGradedComparisonData
    (I : Ideal A) (M : Type v) [AddCommGroup M] [Module A M] :
    IAdicGradedComparisonData I M :=
  ⟨iAdicGradedComparisonMapData I M, isIAdicGradedComparisonMapData_canonical I M⟩


end LeanCategories.Algebra
