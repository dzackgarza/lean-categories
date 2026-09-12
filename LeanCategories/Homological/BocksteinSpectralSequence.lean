/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Homological.ExactCouple
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.SpectralSequence.Basic
public import Mathlib.Data.Nat.Prime.Basic

/-!
# The Bockstein exact couple and spectral sequence

Weibel, *An Introduction to Homological Algebra* (1994), Construction 5.9.9,
pp. 157--158 (FC05-C05-U077).

Fix a prime `ℓ`. Given a graded abelian group `H_*` for which multiplication
by `ℓ` occurs in a long exact sequence

`⋯ ⟶ E_{n+1} ⟶ H_n ⟶[ℓ] H_n ⟶ E_n ⟶ H_{n-1} ⟶ ⋯`,

rolling the sequence into an exact couple yields the Bockstein spectral
sequence with initial page `E⁰ = E`. Weibel notes that its differential lowers
total degree by one; the auxiliary bigrading required by the spectral-sequence
formalism is artificial.

This file records that construction data. Proposition 5.9.10 and the later
convergence statements are not part of the definition layer.
-/

@[expose] public noncomputable section

namespace LeanCategories.Homological

open CategoryTheory CategoryTheory.Limits

/-- Multiplication by the fixed prime `ℓ` on an abelian group. -/
def bocksteinPrimeMap (ℓ : ℕ) (A : ModuleCat ℤ) : A ⟶ A :=
  ℓ • 𝟙 A

/-- The graded long-exact-sequence data which Weibel rolls into the Bockstein
exact couple in Construction 5.9.9. -/
structure BocksteinExactCoupleData (ℓ : ℕ) where
  /-- The chosen integer is prime. -/
  prime : Nat.Prime ℓ
  /-- The graded integral object `H_*`. -/
  H : ℤ → ModuleCat ℤ
  /-- The graded coefficient object `E_*`. -/
  E : ℤ → ModuleCat ℤ
  /-- The reduction/quotient map `H_n ⟶ E_n`. -/
  j : ∀ n : ℤ, H n ⟶ E n
  /-- The connecting map `E_n ⟶ H_{n-1}`. -/
  k : ∀ n : ℤ, E n ⟶ H (n - 1)
  /-- `E_{n+1} ⟶ H_n ⟶[ℓ] H_n` is a complex. -/
  k_i : ∀ n : ℤ,
    (k (n + 1) ≫ eqToHom (congrArg H (by omega : n + 1 - 1 = n))) ≫
      bocksteinPrimeMap ℓ (H n) = 0
  /-- Exactness at the first copy of `H_n`. -/
  exact_ki : ∀ n : ℤ,
    (ShortComplex.mk
      (k (n + 1) ≫ eqToHom (congrArg H (by omega : n + 1 - 1 = n)))
      (bocksteinPrimeMap ℓ (H n)) (k_i n)).Exact
  /-- `H_n ⟶[ℓ] H_n ⟶ E_n` is a complex. -/
  i_j : ∀ n : ℤ, bocksteinPrimeMap ℓ (H n) ≫ j n = 0
  /-- Exactness at the second copy of `H_n`. -/
  exact_ij : ∀ n : ℤ,
    (ShortComplex.mk (bocksteinPrimeMap ℓ (H n)) (j n) (i_j n)).Exact
  /-- `H_n ⟶ E_n ⟶ H_{n-1}` is a complex. -/
  j_k : ∀ n : ℤ, j n ≫ k n = 0
  /-- Exactness at `E_n`. -/
  exact_jk : ∀ n : ℤ,
    (ShortComplex.mk (j n) (k n) (j_k n)).Exact

/-- The artificial bigrading used to view `E_*` as the page-zero object of a
homological spectral sequence: bidegree `(p,q)` carries `E_{p+q}`. -/
def bocksteinPageZeroObject {ℓ : ℕ} (X : BocksteinExactCoupleData ℓ)
    (pq : ℤ × ℤ) : ModuleCat ℤ :=
  X.E (pq.1 + pq.2)

/-- A source-faithful realization of the Bockstein spectral sequence associated
to `X`. Existence of such a spectral sequence is supplied by the general exact
couple result (Weibel Proposition 5.9.2); this structure merely records the
resulting object and pins down its page-zero data and differential. -/
structure BocksteinSpectralSequenceRealization {ℓ : ℕ}
    (X : BocksteinExactCoupleData ℓ) where
  /-- The associated homological spectral sequence, starting on page zero. -/
  spectralSequence :
    SpectralSequence (ModuleCat ℤ)
      (fun r => ComplexShape.up' (⟨-r, r - 1⟩ : ℤ × ℤ)) 0
  /-- The initial page is the artificially bigraded copy of `E_*`. -/
  pageZeroIso : ∀ pq : ℤ × ℤ,
    (spectralSequence.page 0 (by omega)).X pq ≅ bocksteinPageZeroObject X pq
  /-- On page zero, the differential is `jk` (categorical order `k ≫ j`),
  hence lowers the underlying grading by one as in Weibel 5.9.9. -/
  pageZeroDifferential : ∀ p q : ℤ,
    (spectralSequence.page 0 (by omega)).d (p, q) (p, q - 1) ≫
        (pageZeroIso (p, q - 1)).hom =
      (pageZeroIso (p, q)).hom ≫ X.k (p + q) ≫ X.j (p + q - 1) ≫
        eqToHom
          (congrArg X.E
            (show p + q - 1 = p + (q - 1) by omega))

end LeanCategories.Homological
