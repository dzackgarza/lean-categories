/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Algebra.AssociatedGraded
public import Mathlib.Algebra.Module.Torsion.Basic
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

/-- Matsumura's graded comparison-map data selected from its exact homogeneous
representative graph.

This declaration performs no quotient/scalar descent and proves no map law. -/
def iAdicGradedComparisonMapData
    (I : Ideal A) (M : Type v) [AddCommGroup M] [Module A M] :
    IAdicGradedComparisonMapData I M :=
  Classical.epsilon (IsIAdicGradedComparisonMapData I M)

end LeanCategories.Algebra
