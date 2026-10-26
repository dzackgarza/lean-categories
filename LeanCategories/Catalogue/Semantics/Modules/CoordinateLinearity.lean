/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.LinearAlgebra.Pi

@[expose] public section

/-!
# Coordinate closure of the existing linearity predicate

These proof adapters expose Mathlib's existing `LinearMap.pi`, `prod`,
`vecCons`, and `vecEmpty` through the `IsLinearMap` predicate used by the
public module-map admission. They preserve every input function. They do not
construct a different map or assume that its coordinates are linear.

In particular, the finite-vector rule is uniform in the tail length `n`.
Mathlib supplies `LinearMap.vecCons` precisely because `Fin.cases` does not
commute definitionally with function application. Pointwise extensionality
alone does not eliminate a vector constructor at an arbitrary index.

The scalar ring here may be any semiring. Each nonstructural coordinate still
requires its full addition and scalar preservation laws; arbitrary scalar
endomorphisms over a noncommutative ring are not asserted to be linear.

Reuse: Mathlib `LinearAlgebra/Pi.lean`, `LinearAlgebra/Prod.lean`, and
`Algebra/Module/LinearMap/Defs.lean` at
`db584cd6d46c92f209a44c0f1c829460d327499d`, Apache-2.0. The 2026-10-24 public
formalization-corpus search `"LinearMap.vecCons"` located this exact owner.
The only new mathematics is the predicate-to-bundled-map-to-predicate glue.
-/

namespace CasCatalogue.Modules.CoordinateLinearity

universe u v w z i

variable {R : Type u} {M : Type v} [Semiring R] [AddCommMonoid M] [Module R M]

/-- Coordinatewise linearity gives the same whole function into a dependent
product. No finiteness or enumeration of the index type is required. -/
theorem pi {ι : Type i} {N : ι → Type w}
    [∀ i, AddCommMonoid (N i)] [∀ i, Module R (N i)]
    {f : M → (i : ι) → N i} (h : ∀ i, IsLinearMap R (fun x => f x i)) :
    IsLinearMap R f :=
  (LinearMap.pi (fun i => (h i).mk' (fun x => f x i))).isLinear

/-- Pairing two linear coordinate functions retains both original functions. -/
theorem prod {N : Type w} {P : Type z}
    [AddCommMonoid N] [AddCommMonoid P] [Module R N] [Module R P]
    {f : M → N} {g : M → P} (hf : IsLinearMap R f) (hg : IsLinearMap R g) :
    IsLinearMap R (fun x => (f x, g x)) :=
  ((hf.mk' f).prod (hg.mk' g)).isLinear

/-- The empty coordinate function is the existing zero-dimensional linear map. -/
theorem vecEmpty {N : Type w} [AddCommMonoid N] [Module R N] :
    IsLinearMap R (fun _ : M => (Matrix.vecEmpty : Fin 0 → N)) :=
  (LinearMap.vecEmpty : M →ₗ[R] Fin 0 → N).isLinear

/-- Prepending one linear coordinate to a linear tail is linear, at every
dimension and with exactly the original vector-valued function. -/
theorem vecCons {N : Type w} [AddCommMonoid N] [Module R N] {n : ℕ}
    {f : M → N} {g : M → Fin n → N}
    (hf : IsLinearMap R f) (hg : IsLinearMap R g) :
    IsLinearMap R (fun x => Matrix.vecCons (f x) (g x)) :=
  ((hf.mk' f).vecCons (hg.mk' g)).isLinear

end CasCatalogue.Modules.CoordinateLinearity
