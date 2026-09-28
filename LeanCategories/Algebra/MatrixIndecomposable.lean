/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Logic.Equiv.Sum

@[expose] public section

/-!
# Decomposable and indecomposable matrices

A square matrix is *decomposable* when a re-indexing splits its index set into two nonempty parts
with no nonzero entry between them (in either direction), i.e. it is block diagonal after a
permutation; it is *indecomposable* otherwise. Vinberg's `C⁺`-matrices are the indecomposable
nonnegative ones, and a Coxeter or Cartan matrix is indecomposable exactly when its diagram is
connected.

**Theorem** (`Matrix.isDecomposable_iff_not_preconnected`). `A` is decomposable iff its
*support graph* — `i ~ j` for `i ≠ j` with `A i j ≠ 0` or `A j i ≠ 0` — is not preconnected.

Provenance: the definitions are migrated from `dzackgarza/research`,
`computations/scripts/sterk-enriques-cusps/lean/Atoms.lean` (section `Indecomposable`, Sterk
graph node V1); the support-graph characterization is new here.

LC-09 search: Mathlib's `Matrix.IsIrreducible` (`LinearAlgebra/Matrix/Irreducible/Defs.lean`)
is the Perron–Frobenius notion for *nonnegative* matrices over an ordered ring, via strong
connectivity of the quiver of *positive* entries. It is a different notion (directed, and
requiring an order); the corpus search "indecomposable matrix block diagonal permutation"
returns nothing closer. For a symmetric nonnegative matrix the two agree through the support
graph; that comparison is not proved here.
-/

namespace Matrix

universe u v

variable {n : Type u} {α : Type v}

/-- `A` is *decomposable* when some re-indexing `n ≃ ι ⊕ κ` with `ι`, `κ` nonempty makes both
off-diagonal blocks vanish. -/
def IsDecomposable [Zero α] (A : Matrix n n α) : Prop :=
  ∃ (ι κ : Type u) (_ : Nonempty ι) (_ : Nonempty κ) (e : n ≃ ι ⊕ κ),
    ∀ i j, A (e.symm (Sum.inl i)) (e.symm (Sum.inr j)) = 0 ∧
      A (e.symm (Sum.inr j)) (e.symm (Sum.inl i)) = 0

/-- Indecomposability, the condition on a `C⁺`-matrix. -/
def IsIndecomposable [Zero α] (A : Matrix n n α) : Prop :=
  ¬ A.IsDecomposable

/-- The support graph: distinct indices are adjacent when either entry between them is
nonzero. -/
def supportGraph [Zero α] (A : Matrix n n α) : SimpleGraph n where
  Adj i j := i ≠ j ∧ (A i j ≠ 0 ∨ A j i ≠ 0)
  symm := ⟨fun _ _ h ↦ ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h ↦ h.1 rfl⟩

/-- A matrix is decomposable exactly when its support graph is not preconnected. -/
theorem isDecomposable_iff_not_preconnected [Zero α] (A : Matrix n n α) :
    A.IsDecomposable ↔ ¬ A.supportGraph.Preconnected := by
  classical
  constructor
  · rintro ⟨ι, κ, ⟨i₀⟩, ⟨k₀⟩, e, hz⟩ hconn
    -- Adjacent indices lie on the same side of the splitting.
    have side : ∀ {u w : n}, A.supportGraph.Adj u w → (e u).isLeft = (e w).isLeft := by
      intro u w h
      rcases hu : e u with i | k <;> rcases hw : e w with i' | k'
      · rfl
      · exfalso
        have hu' : u = e.symm (Sum.inl i) := by rw [← hu, Equiv.symm_apply_apply]
        have hw' : w = e.symm (Sum.inr k') := by rw [← hw, Equiv.symm_apply_apply]
        rcases h.2 with h' | h' <;> apply h' <;> rw [hu', hw']
        exacts [(hz i k').1, (hz i k').2]
      · exfalso
        have hu' : u = e.symm (Sum.inr k) := by rw [← hu, Equiv.symm_apply_apply]
        have hw' : w = e.symm (Sum.inl i') := by rw [← hw, Equiv.symm_apply_apply]
        rcases h.2 with h' | h' <;> apply h' <;> rw [hu', hw']
        exacts [(hz i' k).2, (hz i' k).1]
      · rfl
    have walk : ∀ {u w : n} (p : A.supportGraph.Walk u w), (e u).isLeft = (e w).isLeft := by
      intro u w p
      induction p with
      | nil => rfl
      | cons h _ ih => exact (side h).trans ih
    obtain ⟨p⟩ := hconn (e.symm (Sum.inl i₀)) (e.symm (Sum.inr k₀))
    simpa using walk p
  · intro h
    obtain ⟨u, v, huv⟩ : ∃ u v, ¬ A.supportGraph.Reachable u v := by
      simpa [SimpleGraph.Preconnected] using h
    let P : n → Prop := A.supportGraph.Reachable u
    refine ⟨{w // P w}, {w // ¬ P w}, ⟨⟨u, SimpleGraph.Reachable.refl u⟩⟩, ⟨⟨v, huv⟩⟩,
      (Equiv.sumCompl P).symm, fun i j ↦ ?_⟩
    simp only [Equiv.symm_symm, Equiv.sumCompl_apply_inl, Equiv.sumCompl_apply_inr]
    have hne : (i : n) ≠ j := fun hij ↦ j.2 (hij ▸ i.2)
    by_contra hnz
    exact j.2 (i.2.trans (SimpleGraph.Adj.reachable
      ⟨hne, by rcases not_and_or.mp hnz with h' | h' <;> [exact .inl h'; exact .inr h']⟩))

/-- A matrix is indecomposable exactly when its support graph is preconnected. -/
theorem isIndecomposable_iff_preconnected [Zero α] (A : Matrix n n α) :
    A.IsIndecomposable ↔ A.supportGraph.Preconnected := by
  rw [IsIndecomposable, isDecomposable_iff_not_preconnected, not_not]

end Matrix
