/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Homological.HochschildShuffleProduct
public import Mathlib.LinearAlgebra.PiTensorProduct.Basic

/-!
# Internal Hochschild shuffle product

Weibel, *An Introduction to Homological Algebra* (1994), §9.4, pp. 319--325
(FC05-C09-U055).

For a commutative `k`-algebra `R`, multiplication `R ⊗ₖ R → R` converts the
external shuffle construction into an internal one.  Here this is recorded
literally by applying multiplication in every algebra tensor factor.  The
coefficient tensor is left visible; the canonical further passage to the
appropriate balanced coefficient tensor, and the induced product on homology,
are result-level statements.
-/

@[expose] public noncomputable section

namespace LeanCategories.Homological

open CategoryTheory
open scoped TensorProduct

universe u v wM wN

variable (k : Type u) [CommRing k]
variable (R : Type v) [CommRing R] [Algebra k R]
variable (M : Type wM) [AddCommGroup M] [Module k M]
variable (N : Type wN) [AddCommGroup N] [Module k N]

/-- Multiplication `R ⊗ₖ R → R`, the algebra map used to turn the external
Hochschild product into the internal product. -/
def hochschildTensorMultiplication : (R ⊗[k] R) →ₗ[k] R :=
  TensorProduct.lift (LinearMap.mul k R)

@[simp]
lemma hochschildTensorMultiplication_tmul (r s : R) :
    hochschildTensorMultiplication k R (r ⊗ₜ[k] s) = r * s :=
  rfl

/-- Apply multiplication independently in every tensor factor. -/
def hochschildInternalTensorPowerCollapse (n : ℕ) :
    TensorPower k n (R ⊗[k] R) →ₗ[k] TensorPower k n R :=
  PiTensorProduct.map (fun _ => hochschildTensorMultiplication k R)

/-- Collapse the algebra part of an external shuffle target along
`R ⊗ₖ R → R`, leaving the coefficient tensor visible. -/
def hochschildInternalCollapse (p q : ℕ) :
    HochschildShuffleTargetDegree k R R M N p q →ₗ[k]
      ((M ⊗[k] N) ⊗[k] TensorPower k (p + q) R) :=
  TensorProduct.map LinearMap.id (hochschildInternalTensorPowerCollapse k R (p + q))

/-- The pure-tensor internal shuffle formula obtained from the external
shuffle formula by multiplying the two algebra components factorwise. -/
def hochschildInternalShufflePure {p q : ℕ}
    (m : M) (a : Fin p → R) (n : N) (b : Fin q → R) :
    (M ⊗[k] N) ⊗[k] TensorPower k (p + q) R :=
  hochschildInternalCollapse k R M N p q
    (hochschildShufflePure k R R M N m a n b)

/-- The degreewise internal Hochschild product associated to a realization of
the external shuffle product.  Differential compatibility is Proposition
9.4.2-level content and is not asserted here. -/
def HochschildShuffleExternalProductRealization.internalMap
    (E : HochschildShuffleExternalProductRealization k R R M N) (p q : ℕ) :
    ModuleCat.of k
        (HochschildChainDegree (k := k) (R := R) (M := M) p ⊗[k]
          HochschildChainDegree (k := k) (R := R) (M := N) q) ⟶
      ModuleCat.of k ((M ⊗[k] N) ⊗[k] TensorPower k (p + q) R) :=
  E.map p q ≫ ModuleCat.ofHom (hochschildInternalCollapse k R M N p q)

end LeanCategories.Homological
