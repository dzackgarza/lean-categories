/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Map

/-!
# Pure submodules

Matsumura, *Commutative Ring Theory*, Appendix to §7, pp. 53--54,
`FC13-C03-U025`: a submodule `N ⊆ M` is pure when tensoring its inclusion
with any module is injective.

The declaration is a definition-only port of the predicate represented in
`AntoineChambert-Loir/DividedPowers4` commit
`e10578d9399ad5324cabff2ea76090cf81a0268c`,
`DividedPowers/ForMathlib/RingTheory/Pure.lean::Submodule.IsPure`
(Apache-2.0).  The finitely-presented test criterion is a result and is not
part of this declaration.
-/

@[expose] public section

namespace Submodule

universe u v w

variable {R : Type u} {M : Type v}
variable [CommRing R] [AddCommGroup M] [Module R M]

/-- A submodule `N ⊆ M` is pure when, for every `R`-module `E`, the map
`N ⊗[R] E → M ⊗[R] E` induced by the inclusion is injective. -/
def IsPure (N : Submodule R M) : Prop :=
  ∀ (E : Type w) [AddCommGroup E] [Module R E],
    Function.Injective
      (TensorProduct.map N.subtype (LinearMap.id : E →ₗ[R] E))

end Submodule
