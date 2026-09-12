/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Homological.TsyganBicomplex

/-!
# The I, S, and B maps of cyclic homology

Weibel, *An Introduction to Homological Algebra* (1994), §9.6, pp. 330--337,
immediately before Proposition 9.6.11 (FC05-C09-U092).

For a cyclic object `A`, inclusion of the Hochschild column of Tsygan's
bicomplex gives `I : HH_n(A) ⟶ HC_n(A)`, translation by two columns gives
`S : HC_n(A) ⟶ HC_{n-2}(A)`, and the connecting morphism gives
`B : HC_{n-1}(A) ⟶ HH_n(A)`.

This file records exactly those three degree-indexed map families.  The
exactness of the resulting SBI sequence is Proposition 9.6.11
(FC05-C09-U093) and is deliberately not asserted here.
-/

@[expose] public noncomputable section

namespace LeanCategories.Homological

open CategoryTheory

universe v u

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- Hochschild homology of a cyclic object, computed from the alternating
face-map complex of its underlying simplicial object. -/
def cyclicHochschildHomology (A : CyclicObject (C := C)) (n : ℕ) : C :=
  (HomologicalComplex.homologyFunctor C (ComplexShape.down ℕ) n).obj
    (cyclicHochschildComplex A)

/-- Weibel's three map families preceding the SBI sequence.

The `S` and `B` fields are indexed without subtraction:

* `S n` is the source map `HC_{n+2}(A) ⟶ HC_n(A)`;
* `B n` is the source map `HC_n(A) ⟶ HH_{n+1}(A)`.

Thus the displayed source indexing is recovered verbatim while avoiding
truncated subtraction on `ℕ`.  No exactness assertion is part of this
definition. -/
structure CyclicSBIMaps
    (A : CyclicObject (C := C))
    (T : TsyganBicomplexRealization A)
    [HomologicalComplex₂.HasTotal T.bicomplex (ComplexShape.down ℕ)] where
  /-- Inclusion of the Hochschild column: `I : HH_n(A) ⟶ HC_n(A)`. -/
  I : ∀ n : ℕ, cyclicHochschildHomology A n ⟶ cyclicHomology A T n
  /-- Periodicity by two columns, reindexed as
  `S : HC_{n+2}(A) ⟶ HC_n(A)`. -/
  S : ∀ n : ℕ, cyclicHomology A T (n + 2) ⟶ cyclicHomology A T n
  /-- Connecting morphism, reindexed as
  `B : HC_n(A) ⟶ HH_{n+1}(A)`. -/
  B : ∀ n : ℕ, cyclicHomology A T n ⟶ cyclicHochschildHomology A (n + 1)

end LeanCategories.Homological
