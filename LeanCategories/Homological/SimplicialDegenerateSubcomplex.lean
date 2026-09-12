/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Homological.SimplicialChainComplexes
public import Mathlib.Algebra.Category.ModuleCat.Abelian

/-!
# The degenerate subcomplex of a simplicial module

Weibel, *An Introduction to Homological Algebra* (1994), §8.3, pp. 263--269
(FC05-C08-U033).

For a simplicial module `A`, the degenerate part in degree `n` is the sum of
the images of the degeneracies `σ_i : A_{n-1} → A_n`.  Mathlib's Dold--Kan
development explicitly leaves this subcomplex as a TODO; this file records the
source degree submodules and the definition-layer realization of them as a
subcomplex of the unnormalized alternating-face complex.  The decomposition
`C(A)=N(A)⊕D(A)` is the following theorem row and is not asserted here.
-/

@[expose] public section

noncomputable section

namespace LeanCategories.Homological

open CategoryTheory Opposite Simplicial

universe u v

variable (R : Type u) [Ring R]

/-- The degree-`n` degenerate submodule
`D_n(A)=Σ_{i=0}^{n-1} im(σ_i)`.  For `n=0` the index type is empty, hence this
is the zero submodule. -/
def simplicialDegenerateSubmodule
    (A : SimplicialObject (ModuleCat.{v} R)) (n : ℕ) :
    Submodule R (A.obj (op ⦋n⦌)) := by
  cases n with
  | zero => exact ⊥
  | succ n => exact ⨆ i : Fin (n + 1), LinearMap.range (A.σ i).hom

/-- Definition-layer realization of the degenerate degree submodules as a
chain subcomplex of Weibel's unnormalized complex `C(A)`.

The degree isomorphism and the inclusion equation say exactly that the degree
`n` object is `Σ_i im(σ_i)` with its ordinary subtype inclusion. -/
structure SimplicialDegenerateSubcomplexRealization
    (A : SimplicialObject (ModuleCat.{v} R)) where
  /-- The degenerate chain complex. -/
  complex : ChainComplex (ModuleCat.{v} R) ℕ
  /-- Its inclusion into the unnormalized alternating-face complex. -/
  inclusion : complex ⟶ simplicialUnnormalizedChainComplex A
  /-- Identification of each degree with the sum of degeneracy images. -/
  degreeIso : ∀ n : ℕ,
    complex.X n ≅ ModuleCat.of R (simplicialDegenerateSubmodule R A n)
  /-- Under the degree identification, the subcomplex inclusion is the
  ordinary subtype map of the degenerate submodule. -/
  inclusion_degree : ∀ n : ℕ,
    (degreeIso n).hom ≫
        ModuleCat.ofHom (Submodule.subtype (simplicialDegenerateSubmodule R A n)) =
      inclusion.f n

end LeanCategories.Homological
