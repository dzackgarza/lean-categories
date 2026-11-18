/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Lattices.Valued.FoldingInvariantChamber

/-!
# Probes for `#116` stage 3, on the smallest inputs that decide them

`FoldingInvariantChamber.lean` states `IsChamberWithWalls` for the invariant lattice `M^σ`. Its
content is decided here on the smallest inputs:

* the identification of the invariant real form: the fixed part is spanned by the fixed lattice
  vectors (`realForm_mem_span_fixed`), checked on the zero vector of the worked lattice `T_dP`
  where the involution is `I = -I_En`;
* the three fields of the predicate: `isChamberWithWalls_invariant` is stated with exactly the
  arithmetic inputs of AEGS §3.7 and nothing else, so an instantiation here shows the statement is
  not a restatement of its own conclusion (each hypothesis is a statement about `ℤ`-lattices: a
  divisibility, a lattice point, an integer multiple);
* the axiom footprint of the new declarations.
-/

@[expose] public section

open QuadraticMap
open LeanCategories.Modules.Bilinear.Valued

namespace LeanCategories.Lattices.Valued

/-! ## The identification of the invariant real form -/

/-- The zero vector of the real form is fixed and lies in the span of the fixed lattice vectors. -/
example : (0 : (realForm tdpFiniteLattice).obj.carrier) ∈
    Submodule.span ℝ (Set.range fun v :
      involutionFixedSubmodule (L := tdpFiniteLattice) tdpIsometry =>
        toRealForm tdpFiniteLattice (v : tdpFiniteLattice.obj.obj.carrier)) :=
  realForm_mem_span_fixed tdpIsometry tdpIsometry_mul_self (by rw [map_zero])

/-- The pairing of two fixed lattice vectors is the same in the invariant real form as in the
ambient lattice — the bridge that makes the invariant chamber's cones comparable with the ambient
picture. -/
example [Module.Projective ℤ (involutionFixedSubmodule (L := tdpFiniteLattice) tdpIsometry)]
    (v w : involutionFixedSubmodule (L := tdpFiniteLattice) tdpIsometry) :
    (realForm (invariantFixedLattice (L := tdpFiniteLattice) tdpIsometry)).obj.pairing
        (toRealForm _ (v : (invariantFixedLattice (L := tdpFiniteLattice)
          tdpIsometry).obj.obj.carrier))
        (toRealForm _ (w : (invariantFixedLattice (L := tdpFiniteLattice)
          tdpIsometry).obj.obj.carrier))
      = ((invariantFixedLattice (L := tdpFiniteLattice) tdpIsometry).obj.obj.pairing v w : ℝ) :=
  invariant_pairing_toRealForm tdpIsometry v w

/-! ## The predicate, from the arithmetic inputs only -/

/-- **The chamber of the invariant lattice**, with the three arithmetic inputs as hypotheses. The
statement is an implication: its hypotheses are a divisibility statement about the folded roots, a
lattice interior vector, and the completeness of the wall set — not the three fields of
`IsChamberWithWalls`, which is what the theorem produces. -/
example [Module.Projective ℤ (involutionFixedSubmodule (L := tdpFiniteLattice) tdpIsometry)]
    (R : Set tdpFiniteLattice.obj.obj.carrier)
    (hroots : foldedRootSetInvariant tdpIsometry R ⊆
      negativeReflectiveRoots (invariantFixedLattice (L := tdpFiniteLattice) tdpIsometry))
    (w : involutionFixedSubmodule (L := tdpFiniteLattice) tdpIsometry)
    (hw : 0 < (invariantFixedLattice (L := tdpFiniteLattice) tdpIsometry).obj.obj.pairing w w)
    (hwv : ∀ v ∈ foldedRootSetInvariant tdpIsometry R,
      0 < (invariantFixedLattice (L := tdpFiniteLattice) tdpIsometry).obj.obj.pairing w v)
    (hcomplete : ∀ ρ ∈ negativeReflectiveRoots
        (invariantFixedLattice (L := tdpFiniteLattice) tdpIsometry),
      ∃ v ∈ foldedRootSetInvariant tdpIsometry R, ∃ k : ℤ, k ≠ 0 ∧ ρ = k • v) :
    IsChamberWithWalls (invariantFixedLattice (L := tdpFiniteLattice) tdpIsometry)
      (toRealForm _ w) (foldedRootSetInvariant tdpIsometry R) :=
  isChamberWithWalls_invariant tdpIsometry R hroots w hw hwv hcomplete

/-! ## Axiom footprint -/

#print axioms realForm_mem_span_fixed
#print axioms isChamberWithWalls_invariant
#print axioms chamberOf_invariant_folded

end LeanCategories.Lattices.Valued
