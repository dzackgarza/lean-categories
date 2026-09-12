/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Homological.HochschildEnveloping

/-!
# The enveloping-algebra augmentation

Weibel, *An Introduction to Homological Algebra* (1994), Alternate Calculation 9.2.4,
pp. 306--310 (FC05-C09-U016).

This file records the construction layer: the multiplication map `Rᵉ → R`, its
kernel `I`, and the canonical `k`-linear splitting `R → Rᵉ`.  The low-degree
Hochschild calculation and the universal class in `I/I²` are theorem-layer content.
-/

@[expose] public section

namespace LeanCategories.Homological

open scoped TensorProduct

universe u v

variable (k : Type u) [CommRing k]
variable (R : Type v) [Ring R] [Algebra k R]

/-- Multiplication `Rᵉ=R⊗_kRᵐᵒᵖ → R`, `r⊗sᵐᵒᵖ ↦ rs`. -/
def envelopingMultiplication : EnvelopingAlgebra k R →ₗ[k] R :=
  TensorProduct.lift <| LinearMap.mk₂ k
    (fun r s => r * MulOpposite.unop s)
    (by intro r r' s; exact add_mul _ _ _)
    (by intro a r s; simpa using Algebra.smul_mul_assoc a r (MulOpposite.unop s))
    (by intro r s s'; exact mul_add _ _ _)
    (by
      intro a r s
      rw [MulOpposite.unop_smul]
      exact Algebra.mul_smul_comm a r (MulOpposite.unop s))

@[simp]
theorem envelopingMultiplication_tmul (r s : R) :
    envelopingMultiplication k R (r ⊗ₜ[k] (MulOpposite.op s : Rᵐᵒᵖ)) = r * s :=
  rfl

/-- The augmentation ideal `I=ker(Rᵉ→R)` used in Alternate Calculation 9.2.4. -/
def hochschildAugmentationIdeal : Submodule k (EnvelopingAlgebra k R) :=
  LinearMap.ker (envelopingMultiplication k R)

/-- The canonical `k`-linear splitting `r ↦ r⊗1`. -/
def envelopingSection : R →ₗ[k] EnvelopingAlgebra k R :=
  (Algebra.TensorProduct.includeLeft : R →ₐ[k] EnvelopingAlgebra k R).toLinearMap

@[simp]
theorem envelopingMultiplication_section :
    (envelopingMultiplication k R).comp (envelopingSection k R) = LinearMap.id := by
  ext r
  simp [envelopingSection, envelopingMultiplication]

end LeanCategories.Homological
