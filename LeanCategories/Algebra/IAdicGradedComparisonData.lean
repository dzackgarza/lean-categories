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
carrier.  The comparison with the routed `I^n/I^(n+1)` piece is itself
recorded as raw data by its representative graph; no equality of denominators,
linearity, bijectivity, tensor descent, or comparison theorem is proved here.

Thus the tensor product in this file is literally over `A/I`, while every
statement identifying the carrier presentation with the routed associated
graded object remains Sweep-IV result work.
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

All three are intentionally raw functions: their additive/linear,
well-definedness, and isomorphism properties are results, not constructor
fields in Sweep III. -/
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

Existence of data satisfying this graph, independence of representatives,
linearity over `A/I`, and the fact that these formulas give the usual
comparison homomorphism are all result-layer obligations. -/
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

end LeanCategories.Algebra
