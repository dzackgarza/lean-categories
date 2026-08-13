/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Lattices.Valued.Topological

/-!
# Real quotients of realized integral lattices

A real realization of a finite projective `ℤ`-lattice, as built in
`LeanCategories.Lattices.Valued.Topological`, gives an inclusion `L ⊂ L_ℝ` of a discrete full
`ℤ`-lattice in a real vector space. This file forms the quotient `L_ℝ / L` and proves that it is
a compact topological group.

## Relation to the algebraic base change

The algebraic cokernel and this topological quotient are different constructions.

For a base change along `ℤ → K` with `K` a field of characteristic zero, the map
`L → L ⊗ K` is injective and `coker(L → L ⊗ K) = L_K / L` is a *torsion* `ℤ`-module: every
element `x ⊗ 1` of `L_K` is killed by some nonzero integer modulo `L`, because `L_K` is a
`ℚ`-vector space spanned by `L`. That cokernel carries no topology, no complex structure, and is
not an abelian variety. It is the algebraic comparison object of Proposition 19.4 style
statements about `L → L^*`, and lives in the module category.

The quotient built here is the topological one: `L_ℝ` is the *real* realization with its norm
topology, `L` sits inside it as a discrete subgroup of full rank, and `L_ℝ / L` is a compact
real torus. Passing from that real torus to a complex torus, and further to an abelian variety,
requires two extra pieces of data that no purely algebraic base change supplies:

* a complex structure on `L_ℝ`, that is an `ℝ`-linear `J` with `J ∘ J = -1`, making `L_ℝ` a
  complex vector space of half the real dimension;
* a Riemann form, that is an alternating integral form `E` on `L` with `E(Jx, Jy) = E(x, y)`
  and `E(x, Jx) > 0`, which is the polarization making the complex torus algebraic.

The two constructions are related by comparison maps, never identified.

## Mathlib coverage

Mathlib supplies the compactness input through `IsZLattice.isCompact_range_of_periodic`, and the
quotient topology and topological group structure through `QuotientModule.Quotient.topologicalSpace`
and `Submodule.topologicalAddGroup_quotient`. It has no notion of a complex structure on a real
vector space, no complex torus, no abelian variety and no Riemann form, so this file stops at the
real torus.
-/

@[expose] public section

noncomputable section

namespace LeanCategories.Lattices.Valued

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

namespace FiniteProjectiveLatticeCat

/-- The real torus `L_ℝ / L` of a basis-compatible real realization, with its quotient topology. -/
abbrev realQuotient (L : FiniteProjectiveLatticeCat ℤ ℤ)
    {I : Type*} [Finite I]
    (b : Module.Basis I ℤ L.obj.obj.carrier) (c : Module.Basis I ℝ E) : Type u :=
  E ⧸ L.realLatticeImage b c

/-- The quotient map of a real realization onto its real torus. -/
def realQuotientMk (L : FiniteProjectiveLatticeCat ℤ ℤ)
    {I : Type*} [Finite I]
    (b : Module.Basis I ℤ L.obj.obj.carrier) (c : Module.Basis I ℝ E) :
    E →ₗ[ℤ] L.realQuotient b c :=
  (L.realLatticeImage b c).mkQ

/-- The real torus of a realized lattice is compact: the realized lattice is a full-rank
discrete subgroup, so the quotient map is periodic with compact range. -/
theorem realQuotient_compact (L : FiniteProjectiveLatticeCat ℤ ℤ)
    {I : Type*} [Finite I]
    (b : Module.Basis I ℤ L.obj.obj.carrier) (c : Module.Basis I ℝ E) :
    CompactSpace (L.realQuotient b c) := by
  have : FiniteDimensional ℝ E := Module.Finite.of_basis c
  refine ⟨?_⟩
  rw [← Set.range_eq_univ.mpr (L.realLatticeImage b c).mkQ_surjective]
  refine IsZLattice.isCompact_range_of_periodic (L.realLatticeImage b c) _
    (Submodule.continuous_mkQ _) ?_
  intro z w hw
  simpa [Submodule.Quotient.eq] using hw

end FiniteProjectiveLatticeCat

end LeanCategories.Lattices.Valued
