/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Module.Bimodule

/-!
# Enveloping algebras and bimodules

Weibel, *An Introduction to Homological Algebra* (1994), §9.1, pp. 300--305
(FC05-C09-U004).

For a `k`-algebra `R`, the enveloping algebra is `Rᵉ = R ⊗_k Rᵐᵒᵖ`.
An `R`-bimodule is canonically a left `Rᵉ`-module, with
`(r ⊗ sᵐᵒᵖ) • m = r • (sᵐᵒᵖ • m)`.
-/

@[expose] public section

namespace LeanCategories.Homological

open scoped TensorProduct

universe u v w

/-- The enveloping algebra `Rᵉ = R ⊗_k Rᵐᵒᵖ`. -/
abbrev EnvelopingAlgebra (k : Type u) [CommRing k]
    (R : Type v) [Ring R] [Algebra k R] :=
  R ⊗[k] Rᵐᵒᵖ

variable (k : Type u) [CommRing k]
variable (R : Type v) [Ring R] [Algebra k R]
variable (M : Type w) [AddCommGroup M] [Module k M]
  [Module R M] [Module Rᵐᵒᵖ M]
  [IsScalarTower k R M] [IsScalarTower k Rᵐᵒᵖ M]
  [SMulCommClass R Rᵐᵒᵖ M]

/-- The canonical left `Rᵉ`-module structure on an `R`-bimodule. -/
def envelopingModule : Module (EnvelopingAlgebra k R) M :=
  TensorProduct.Algebra.module

@[simp]
theorem enveloping_tmul_smul (r s : R) (m : M) :
    letI := envelopingModule k R M
    (r ⊗ₜ[k] (MulOpposite.op s : Rᵐᵒᵖ)) • m =
      r • ((MulOpposite.op s : Rᵐᵒᵖ) • m) := by
  letI := envelopingModule k R M
  exact TensorProduct.Algebra.moduleAux_apply r (MulOpposite.op s : Rᵐᵒᵖ) m

end LeanCategories.Homological
