/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.CharP.Frobenius
public import Mathlib.GroupTheory.QuotientGroup.Defs
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.QuadraticForm.Basic

/-!
# The Arf class in characteristic two

Peters--Sterk, *Symmetric and Quadratic Forms* (June 2024), Chapter 8, §8.2
(`FC11-C08-U007`, source lines 4781--4787), define the Arf class of a nondegenerate
quadratic form over a field of characteristic two. They choose a symplectic basis
`(e_i, f_i)` and take the class of `∑ i, q (e_i) * q (f_i)` modulo the
Artin--Schreier subgroup `wp(k) = {x^2 + x | x in k}`.

The following construction records the source symplectic-presentation data
explicitly. The later source clauses asserting existence and basis independence
are not asserted here, and no arbitrary dummy presentation is selected before
those results.
-/

@[expose] public section

namespace LeanCategories.ForMathlib.QuadraticMap

/-- The additive Artin--Schreier map `x ↦ x² - x`. In characteristic two this is
the source's map `x ↦ x² + x`. -/
def artinSchreierHom (k : Type*) [Field k] [CharP k 2] : k →+ k :=
  (frobenius k 2).toAddMonoidHom - AddMonoidHom.id k

/-- The additive quotient `k / wp(k)` in which the characteristic-two Arf class takes values. -/
abbrev ArtinSchreierQuotient (k : Type*) [Field k] [CharP k 2] :=
  k ⧸ (artinSchreierHom k).range

/-- Candidate finite symplectic presentations of a vector space. The candidate family is
kept separate from the predicate so that this type is inhabited even before the source's
existence result is formalized. -/
abbrev SymplecticPresentation (V : Type*) :=
  Σ n : ℕ, Fin n ⊕ Fin n → V

section

variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V]

/-- A candidate presentation is a symplectic basis for the polar form of `q`, ordered as
`(e_i, f_i)`. -/
def IsSymplecticPresentation [CharP k 2]
    (q : QuadraticForm k V) (p : SymplecticPresentation V) : Prop :=
  ∃ b : Module.Basis (Fin p.1 ⊕ Fin p.1) k V,
    (fun i => b i) = p.2 ∧
      (∀ i j, q.polarBilin (p.2 (Sum.inl i)) (p.2 (Sum.inl j)) = 0) ∧
      (∀ i j, q.polarBilin (p.2 (Sum.inr i)) (p.2 (Sum.inr j)) = 0) ∧
      (∀ i j, q.polarBilin (p.2 (Sum.inl i)) (p.2 (Sum.inr j)) =
        if i = j then 1 else 0) ∧
      (∀ i j, q.polarBilin (p.2 (Sum.inr i)) (p.2 (Sum.inl j)) =
        if i = j then -1 else 0)

/-- Source-faithful symplectic-presentation data for `q`: a candidate
presentation together with the exact source predicate. -/
abbrev SymplecticPresentationData [CharP k 2]
    (q : QuadraticForm k V) :=
  {p : SymplecticPresentation V // IsSymplecticPresentation q p}

/-- The source's characteristic-two Arf class: choose a symplectic presentation, form
`∑ i, q(e_i)q(f_i)`, and pass to the Artin--Schreier quotient. -/
noncomputable def arfClass [CharP k 2] [FiniteDimensional k V]
    (q : QuadraticForm k V) (_hq : q.polarBilin.Nondegenerate)
    (P : SymplecticPresentationData q) :
    ArtinSchreierQuotient k :=
  let p := P.1
  QuotientAddGroup.mk' (artinSchreierHom k).range
    (∑ i : Fin p.1, q (p.2 (Sum.inl i)) * q (p.2 (Sum.inr i)))

end

end LeanCategories.ForMathlib.QuadraticMap
