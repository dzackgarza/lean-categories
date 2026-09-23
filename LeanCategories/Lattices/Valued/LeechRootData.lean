/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Lattices.Valued.LeechLatticeData
public import Mathlib.Data.Matrix.Block

/-!
# Leech-root coordinate construction

Peters--Sterk FC11-C17-U030, Version JUNE 2024, printed p. 314
(PDF page 321), Example 17.2.10.4.

The source uses `II_{1,25} = U ⊥ Γ₂₄(-1)` and calls the vectors
`e - (1 + q(v)) f + v`, with `v ∈ Γ₂₄(-1)`, Leech roots.
Here the positive Leech half-norm is `leechQuadraticData`, so the
coefficient of `f` is `leechQuadraticData v - 1`. The negative sign
on the Leech block is part of the Gram data, not a supplied hypothesis.

This file constructs the ambient carrier, its actual form, distinguished
hyperbolic-plane vectors, the root map and its range. It does not prove
the root norm, lattice classification, chamber, reflection-generation,
symmetry-group, or nonreflectivity results in the surrounding paragraph.
-/

@[expose] public noncomputable section

namespace LeanCategories.Lattices.Valued

/-- The concrete carrier of `U ⊥ Γ₂₄(-1)`, with the two summands indexed
separately so the source basis vectors and Leech coordinates remain visible. -/
abbrev LeechLorentzianCarrierData := (Fin 2 ⊕ Fin 24) → ℤ

/-- Gram data for the hyperbolic plane orthogonally summed with the
negative Leech form. -/
def leechLorentzianGramMatrixData :
    Matrix (Fin 2 ⊕ Fin 24) (Fin 2 ⊕ Fin 24) ℤ :=
  Matrix.fromBlocks !![0, 1; 1, 0] 0 0 (-leechGramMatrixData)

/-- The specified integral form on the ambient rank-26 carrier. -/
def leechLorentzianBilinearData :
    LinearMap.BilinForm ℤ LeechLorentzianCarrierData :=
  Matrix.toBilin' leechLorentzianGramMatrixData

/-- The first standard vector `e` of the source hyperbolic plane. -/
def leechHyperbolicEData : LeechLorentzianCarrierData :=
  Sum.elim ![1, 0] 0

/-- The second standard vector `f` of the source hyperbolic plane. -/
def leechHyperbolicFData : LeechLorentzianCarrierData :=
  Sum.elim ![0, 1] 0

/-- The inclusion of the fixed Leech coordinates into the negative block. -/
def leechNegativeInclusionData (v : LeechCarrierData) :
    LeechLorentzianCarrierData :=
  Sum.elim 0 v

/-- The source vector `e - (1 + q₋(v)) f + v`, where `q₋` is the
negative Leech half-norm. No root-property proof is an input. -/
def leechRootData (v : LeechCarrierData) : LeechLorentzianCarrierData :=
  Sum.elim ![1, leechQuadraticData v - 1] v

/-- The full family of Leech roots, as the range of the displayed source
construction rather than a supplied root set. -/
def leechRootsData : Set LeechLorentzianCarrierData :=
  Set.range leechRootData

end LeanCategories.Lattices.Valued
