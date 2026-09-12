/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Lie.TraceForm
public import Mathlib.Algebra.Lie.UniversalEnveloping
public import Mathlib.LinearAlgebra.BilinearForm.Properties

/-!
# Casimir elements from trace-form dual bases

Weibel, *An Introduction to Homological Algebra* (1994), Construction 7.8.8,
§7.8, pp. 242--247 (FC05-C07-U059).

For a finite-dimensional representation whose trace form is nondegenerate,
choose a basis `e_i` and its trace-form dual basis `e^i`.  The Casimir element
is `Σ_i e_i e^i` in the universal enveloping algebra.

Basis independence, centrality, augmentation-ideal membership, and the scalar
by which this element acts on a simple module are theorem-layer statements and
are not asserted here.
-/

@[expose] public noncomputable section

namespace LeanCategories.Homological

open scoped BigOperators

universe u v

variable (K : Type u) [Field K]
variable (L M : Type v) [LieRing L] [LieAlgebra K L]
  [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]
variable {ι : Type v} [Fintype ι] [DecidableEq ι]

/-- The Casimir element associated to a finite basis and its dual for the
representation trace form.

In Weibel Construction 7.8.8, `L` is the image of the original semisimple Lie
algebra in `gl(M)`, where this trace form is nondegenerate. -/
def casimirElement
    (h : (LieModule.traceForm K L M).Nondegenerate)
    (b : Module.Basis ι K L) : UniversalEnvelopingAlgebra K L :=
  ∑ i : ι,
    UniversalEnvelopingAlgebra.ι K (b i) *
      UniversalEnvelopingAlgebra.ι K
        ((LieModule.traceForm K L M).dualBasis h b i)

end LeanCategories.Homological
