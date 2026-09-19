/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Topology.Constructions

@[expose] public section

/-!
# Topological wedge sums

Definition-level realization of Hatcher FC07-C00-U021.  An arbitrary family of pointed
spaces is first placed in its topological disjoint union, then all chosen points are
identified to one quotient class.  Only the quotient data is recorded here.
-/

noncomputable section

namespace LeanCategories.Topology

universe u v

/-- The disjoint union underlying an arbitrary wedge before basepoints are identified. -/
abbrev WedgePre (ι : Type u) (X : ι → Type v) := Σ i, X i

/-- Class labels for an arbitrary wedge quotient. -/
inductive WedgeClass (ι : Type u) (X : ι → Type v)
  | base
  | point (q : WedgePre ι X)

/-- Classify every chosen point into one common class and every other point separately. -/
noncomputable def wedgeClassify {ι : Type u} (X : ι → Type v) (p : ∀ i, X i)
    (q : WedgePre ι X) : WedgeClass ι X :=
  if q.2 = p q.1 then WedgeClass.base else WedgeClass.point q

/-- The equivalence relation defining the wedge of a family of pointed spaces. -/
noncomputable def wedgeSetoid {ι : Type u} (X : ι → Type v) (p : ∀ i, X i) :
    Setoid (WedgePre ι X) :=
  Setoid.ker (wedgeClassify X p)

/-- The arbitrary topological wedge `⋁ i, X i`. -/
noncomputable abbrev Wedge {ι : Type u} (X : ι → Type v) [∀ i, TopologicalSpace (X i)]
    (p : ∀ i, X i) :=
  Quotient (wedgeSetoid X p)

/-- The quotient map from one summand into the wedge. -/
noncomputable def wedgeMk {ι : Type u} (X : ι → Type v) [∀ i, TopologicalSpace (X i)]
    (p : ∀ i, X i) (i : ι) (x : X i) : Wedge X p :=
  Quotient.mk (wedgeSetoid X p) ⟨i, x⟩

end LeanCategories.Topology
