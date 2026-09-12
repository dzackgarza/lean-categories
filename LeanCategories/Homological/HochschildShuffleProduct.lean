/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Homological.HochschildComplex
public import LeanCategories.Homological.HochschildShuffleElements
public import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Shuffle external product on Hochschild chains

Weibel, *An Introduction to Homological Algebra* (1994), §9.4, pp. 319--325
(FC05-C09-U052).

For Hochschild chains of a pair of `k`-algebras, the external product tensors
the coefficient terms and shuffles the two strings of algebra terms, inserting
the first algebra through `r ↦ r ⊗ 1` and the second through `s ↦ 1 ⊗ s`.
This file records the signed `(p,q)`-shuffle formula and packages a chain-level
realization of that formula.  The assertion that the resulting family is a
chain map, and hence induces the external product on Hochschild homology, is
result-level content (Proposition 9.4.1).
-/

@[expose] public noncomputable section

namespace LeanCategories.Homological

open CategoryTheory
open scoped TensorProduct BigOperators

universe u vR vS wM wN

variable (k : Type u) [CommRing k]
variable (R : Type vR) [CommRing R] [Algebra k R]
variable (S : Type vS) [CommRing S] [Algebra k S]
variable (M : Type wM) [AddCommGroup M] [Module k M]
variable (N : Type wN) [AddCommGroup N] [Module k N]

/-- The target degree of the `(p,q)` shuffle product before identifying it
with the standard Hochschild chain module for `R ⊗ₖ S` and `M ⊗ₖ N`. -/
abbrev HochschildShuffleTargetDegree (p q : ℕ) :=
  (M ⊗[k] N) ⊗[k] TensorPower k (p + q) (R ⊗[k] S)

/-- The concatenated list of algebra factors used before shuffling: the first
`p` factors are `a_i ⊗ 1`, and the final `q` factors are `1 ⊗ b_j`. -/
def hochschildExternalFactor {p q : ℕ} (a : Fin p → R) (b : Fin q → S)
    (i : Fin (p + q)) : R ⊗[k] S := by
  classical
  by_cases hi : (i : ℕ) < p
  · exact a ⟨i, hi⟩ ⊗ₜ[k] 1
  · exact 1 ⊗ₜ[k] b ⟨(i : ℕ) - p, by omega⟩

/-- The pure-tensor value of Weibel's signed `(p,q)` shuffle product.

A shuffle permutation records the output position of each input factor, hence
we evaluate the concatenated factor list at `σ⁻¹(i)` in output position `i`. -/
def hochschildShufflePure {p q : ℕ}
    (m : M) (a : Fin p → R) (n : N) (b : Fin q → S) :
    HochschildShuffleTargetDegree k R S M N p q := by
  classical
  exact ∑ σ : Equiv.Perm (Fin (p + q)),
    if IsShuffleAt p σ then
      ((Equiv.Perm.sign σ : ℤˣ) : ℤ) •
        ((m ⊗ₜ[k] n) ⊗ₜ[k]
          PiTensorProduct.tprod k
            (fun i => hochschildExternalFactor k R S a b (σ.symm i)))
    else 0

/-- A chain-level realization of the Hochschild shuffle external product.
The `map_pure` field fixes the map uniquely on the standard pure generators.
Compatibility with Hochschild differentials is deliberately theorem-layer. -/
structure HochschildShuffleExternalProductRealization where
  /-- The `(p,q)` chain-level external product. -/
  map : ∀ p q : ℕ,
    ModuleCat.of k
        (HochschildChainDegree (k := k) (R := R) (M := M) p ⊗[k]
          HochschildChainDegree (k := k) (R := S) (M := N) q) ⟶
      ModuleCat.of k (HochschildShuffleTargetDegree k R S M N p q)
  /-- On pure Hochschild chains, `map` is the signed shuffle sum. -/
  map_pure : ∀ (p q : ℕ) (m : M) (a : Fin p → R) (n : N) (b : Fin q → S),
    map p q
        (hochschildChainPure (k := k) (R := R) (M := M) m a ⊗ₜ[k]
          hochschildChainPure (k := k) (R := S) (M := N) n b) =
      hochschildShufflePure k R S M N m a n b

end LeanCategories.Homological
