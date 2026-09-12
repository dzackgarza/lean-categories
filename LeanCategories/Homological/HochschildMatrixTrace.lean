/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.LinearAlgebra.TensorPower.Basic
public import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Matrix trace on Hochschild chains

Weibel, *An Introduction to Homological Algebra*, Definition 9.5.7, p. 329
(FC05-C09-U079).

Besides the ordinary matrix trace, Weibel defines a trace map on degree-`n` Hochschild chains by
summing over cyclic strings of matrix indices.  The construction below is the corresponding
`k`-linear map.  Its compatibility with the Hochschild simplicial operators, and hence the induced
map on homology, is theorem-level material and is not included in this Definitions unit.
-/

@[expose] public section

open scoped BigOperators TensorProduct

namespace LeanCategories.Homological

universe u v w x

/-- Cyclic successor in `Fin (n+1)`, used to write the closed index string in Weibel's matrix-trace
formula. -/
noncomputable def hochschildCyclicNext (n : ℕ) (i : Fin (n + 1)) : Fin (n + 1) :=
  ⟨(i + 1) % (n + 1), Nat.mod_lt _ (Nat.succ_pos n)⟩

/-- Weibel's ordinary trace `M_m(R) → R`, exposed with the source terminology.

Source: Weibel, Definition 9.5.7, p. 329 (FC05-C09-U079). -/
abbrev matrixTrace (ι : Type x) (R : Type v) [Fintype ι] [Semiring R] :
    Matrix ι ι R →ₗ[R] R :=
  Matrix.traceLinearMap ι R R

/-- The degree-`n` matrix trace on Hochschild chains
`M_m(M) ⊗ M_m(R)^{⊗ n} → M ⊗ R^{⊗ n}`.

For each cyclic index string `(i₀,...,iₙ)`, take the `(i₀,i₁)` entry of the coefficient matrix and
then the `(i_r,i_{r+1})` entry of the `r`th algebra matrix, with `i_{n+1}=i₀`, and sum over all
index strings.  `TensorProduct.map` and `PiTensorProduct.map` provide the multilinear extension from
pure tensors automatically.

Source: Weibel, Definition 9.5.7, p. 329 (FC05-C09-U079). -/
noncomputable def matrixHochschildTrace
    (k : Type u) [CommRing k]
    (R : Type v) [Ring R] [Algebra k R]
    (M : Type w) [AddCommGroup M] [Module k M]
    (ι : Type x) [Fintype ι] (n : ℕ) :
    (Matrix ι ι M ⊗[k] TensorPower k n (Matrix ι ι R)) →ₗ[k]
      (M ⊗[k] TensorPower k n R) := by
  classical
  exact ∑ idx : Fin (n + 1) → ι,
    TensorProduct.map
      (Matrix.entryLinearMap k M (idx 0) (idx (hochschildCyclicNext n 0)))
      (PiTensorProduct.map fun r : Fin n =>
        Matrix.entryLinearMap k R
          (idx r.succ) (idx (hochschildCyclicNext n r.succ)))

/-- The defining formula for `matrixHochschildTrace` on pure tensors. -/
lemma matrixHochschildTrace_tmul_tprod
    (k : Type u) [CommRing k]
    (R : Type v) [Ring R] [Algebra k R]
    (M : Type w) [AddCommGroup M] [Module k M]
    (ι : Type x) [Fintype ι] (n : ℕ)
    (m : Matrix ι ι M) (g : Fin n → Matrix ι ι R) :
    matrixHochschildTrace k R M ι n (m ⊗ₜ[k] PiTensorProduct.tprod k g) =
      ∑ idx : Fin (n + 1) → ι,
        (m (idx 0) (idx (hochschildCyclicNext n 0))) ⊗ₜ[k]
          PiTensorProduct.tprod k (fun r : Fin n =>
            g r (idx r.succ) (idx (hochschildCyclicNext n r.succ))) := by
  classical
  simp [matrixHochschildTrace]

end LeanCategories.Homological
