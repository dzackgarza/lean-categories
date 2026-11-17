/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# A retraction splits a module into a range and a kernel

If a linear map `i : N →ₗ M` has a left inverse `p` (`p ∘ i = id`), then the range of `i` and the
kernel of `p` are complementary submodules: `M = i N ⊕ ker p`. This is the module-theoretic form
of a *splitting* of an embedding, taken over an arbitrary commutative ring with the additive
groups as carriers; no finiteness, freeness or primitivity hypothesis is needed, and none is
available from the datum.

The point of the lemma is what it does *not* say. A splitting chooses a complement. Two different
retractions of the same `i` therefore give two different complements, so the choice of a
complement of a fixed embedding is not contractible: it is data a consumer must name. The
orthogonal complement `S^⊥` is a *different* notion (it is forced by the form, hence unique), and
over a ring it is not in general a complement at all — Nikulin 1980, §5° states only that
`M` is an *overlattice* of `S ⊕ S^⊥`.

## Provenance

Searched (`LinearMap IsCompl ker range`, `isCompl ker leftInverse`, `linear map splitting direct
sum`, `Submodule isCompl range ker`, `IsProj isCompl`) in Mathlib at the pinned revision and in
this repository. Mathlib owns `LinearMap.IsProj` and `LinearMap.IsIdempotentElem`, and proves
`LinearMap.ker_eq_bot`-style facts, but no statement pairing `range i` with `ker p` under
`p ∘ i = id`; the nearest hit is `LinearMap.IsProj` restricted to endomorphisms of one module
(`p : M →ₗ M` with `p * p = p`), which does not cover an embedding into a larger module.
-/

@[expose] public section

open Submodule

namespace LinearMap

variable {R M N : Type*} [Ring R] [AddCommGroup M] [AddCommGroup N]
  [Module R M] [Module R N]

/-- A retraction of a linear map splits its target: the range and the kernel of the retraction are
complementary. -/
theorem isCompl_range_ker_of_comp_eq_id (i : N →ₗ[R] M) (p : M →ₗ[R] N)
    (h : p.comp i = LinearMap.id) : IsCompl (range i) (ker p) := by
  refine ⟨?_, ?_⟩
  · rw [Submodule.disjoint_def]
    intro x hx hx'
    obtain ⟨y, rfl⟩ := mem_range.mp hx
    have hp : p (i y) = y := by simpa using LinearMap.congr_fun h y
    have hy : y = 0 := by
      have h0 : p (i y) = 0 := mem_ker.mp hx'
      rw [hp] at h0
      exact h0
    rw [hy, map_zero]
  · rw [codisjoint_iff, eq_top_iff]
    intro x _
    refine mem_sup.mpr ⟨i (p x), mem_range.mpr ⟨p x, rfl⟩, x - i (p x), ?_, by abel⟩
    have hp : p (i (p x)) = p x := by simpa using LinearMap.congr_fun h (p x)
    rw [mem_ker, map_sub, hp, sub_self]

end LinearMap
