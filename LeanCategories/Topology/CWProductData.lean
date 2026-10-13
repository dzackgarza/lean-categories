/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Topology.CWComplex.Classical.Basic

/-!
# Product-cell data for CW complexes

Hatcher, *Algebraic Topology*, Chapter 0 (FC07-C00-U017).

Sweep III records only the source's cell indexing and underlying product-cell
subsets. The CW axioms for the product-cell topology and its comparison with
the ordinary product topology are result-layer statements.
-/

@[expose] public noncomputable section

open _root_.Topology

namespace LeanCategories.Topology

universe u v

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
variable {C : Set X} {D : Set Y} [CWComplex C] [CWComplex D]

/-- Degree-`n` product cells: choose `m ≤ n`, an `m`-cell of `C`, and an
`(n-m)`-cell of `D`. -/
abbrev CWProductCellIndex (C : Set X) (D : Set Y)
    [CWComplex C] [CWComplex D] (n : ℕ) : Type (max u v) :=
  Σ m : Fin (n + 1), _root_.Topology.CWComplex.cell C m.1 ×
    _root_.Topology.CWComplex.cell D (n - m.1)

/-- The open product cell attached to a product-cell index. -/
def cwProductOpenCell (n : ℕ) (e : CWProductCellIndex C D n) : Set (X × Y) :=
  {p | p.1 ∈ _root_.Topology.RelCWComplex.openCell (C := C) e.1.1 e.2.1 ∧
    p.2 ∈ _root_.Topology.RelCWComplex.openCell (C := D) (n - e.1.1) e.2.2}

end LeanCategories.Topology
