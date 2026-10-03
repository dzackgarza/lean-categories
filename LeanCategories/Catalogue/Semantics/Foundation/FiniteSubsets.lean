/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Catalogue.Semantics.Foundation.PowerSets
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Algebra.Polynomial.Roots
public import LeanCategories.Catalogue.Semantics.Algebra.PolynomialEvidence
public meta import LeanCategories.Catalogue.Registry.Semantic
public meta import LeanCategories.Catalogue.Semantics.Foundation.Evidence
public meta import LeanCategories.Catalogue.Semantics.Algebra.PolynomialEvidence

@[expose] public section

/-!
# Finite subsets

`𝒫_fin(X)` (Mathlib `Finset X`), the finite subsets of `X`, a subobject of `𝒫(X)` (`Finset.coe`,
injective); sums and products over a subset are defined on it, where they are defined at all.
-/

open CategoryTheory

namespace CasCatalogue.Foundation.FiniteSubsets

open CasCatalogue.Foundation.PowerSets

/-- `𝒫_fin(X)`. -/
abbrev finiteSubsets (X : Type) : SetsCat.{0} := Finset X

/-- `𝒫_fin(X) ↪ 𝒫(X)`. -/
def inclusion (X : Type) : finiteSubsets X ⟶ powerSet X := TypeCat.ofHom fun A => (A : Set X)

/-- Admit the actual finite subset, keeping its extent rather than replacing it by
an independently chosen list. Mathlib's `Set.Finite.toFinset` is inverse to coercion. -/
noncomputable def admit (X : Type) (A : Set X) (h : A.Finite) :
    CasCatalogue.Foundation.Objects.fin 1 ⟶ finiteSubsets X :=
  TypeCat.ofHom fun _ => h.toFinset

/-- The admitted finite object has exactly the original comprehension as its extent. -/
theorem inclusion_admit (X : Type) (A : Set X) (h : A.Finite) :
    admit X A h ≫ inclusion X = TypeCat.ofHom (fun _ => A) := by
  ext x a
  exact h.mem_toFinset

/-- Finite subsets form a genuine subobject of the power set. -/
instance inclusion_mono (X : Type) : Mono (inclusion X) := by
  exact (CategoryTheory.mono_iff_injective _).mpr Finset.coe_injective

/-- Nonzero polynomials over a domain have a finite root comprehension. This is
Mathlib `Polynomial.finite_setOfPred_isRoot`, with its defining predicate retained. -/
theorem finite_polynomial_zeros {R : Type*} [CommRing R] [IsDomain R]
    (p : Polynomial R) (hp : p ≠ 0) : Set.Finite {a | p.eval a = 0} :=
  Polynomial.finite_setOfPred_isRoot hp

/-- Evaluation in a chosen coefficient algebra is evaluation of the polynomial
after its actual coefficient map. Finiteness requires that mapped polynomial to be
nonzero, including when a nonfaithful coefficient map kills the original polynomial. -/
theorem finite_polynomial_zeros_aeval {R A : Type*} [CommRing R] [CommRing A]
    [IsDomain A] [Algebra R A] (p : Polynomial R)
    (hp : p.map (algebraMap R A) ≠ 0) : Set.Finite {a : A | Polynomial.aeval a p = 0} := by
  simpa only [Polynomial.eval_map, Polynomial.aeval_def] using
    finite_polynomial_zeros (p.map (algebraMap R A)) hp

open Lean Elab Tactic in
/-- Establish finiteness from supplied evidence, finite literal/finset extents, or
the roots of a nonzero polynomial. The root case uses the polynomial owner's existing
nonvanishing procedure; it does not assume that every polynomial-root set is finite. -/
meta def finiteSubsetEvidence : TacticM Unit := do
  let nonzero : TacticM Unit :=
    CasCatalogue.Evidence.closeByFirst m!"the polynomial is not established to be nonzero"
      [do evalTactic (← `(tactic| assumption)),
       CasCatalogue.Algebra.Polynomials.nonzeroPolynomialEvidence]
  CasCatalogue.Evidence.establish "𝒫_fin" <|
    CasCatalogue.Evidence.closeByFirst m!"the subset is not established to be finite"
      [do evalTactic (← `(tactic| assumption)),
       do evalTactic (← `(tactic| exact Set.toFinite _)),
       do evalTactic (← `(tactic| exact Finset.finite_toSet _)),
       do evalTactic (← `(tactic| simp only [Set.finite_empty, Set.finite_singleton,
         Set.finite_insert])),
       do
         evalTactic (← `(tactic| apply finite_polynomial_zeros))
         nonzero,
       do
         evalTactic (← `(tactic| apply finite_polynomial_zeros_aeval))
         nonzero]

end CasCatalogue.Foundation.FiniteSubsets

namespace CasCatalogue

normalized_registry .object
  { id := ⟨"obj.sets.finite_subsets"⟩, category := CategoryId.sets, name := "𝒫_fin"
    declaration := `CasCatalogue.Foundation.FiniteSubsets.finiteSubsets
    inclusion := some `CasCatalogue.Foundation.FiniteSubsets.inclusion
    admission := some `CasCatalogue.Foundation.FiniteSubsets.admit
    evidence := some `CasCatalogue.Foundation.FiniteSubsets.finiteSubsetEvidence }

end CasCatalogue
