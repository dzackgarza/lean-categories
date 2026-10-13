/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Lattices.Valued.Standard
public import Mathlib.Data.PNat.Basic

@[expose] public section

/-!
# Three-arm T-shaped lattice data

Peters--Sterk, Chapter 4 (FC11-C04-U002), defines the lattice
`T̃_{p,q,r}` from a T-shaped graph with three positive arm lengths.  This
file records the finite vertex type and the corresponding negative
simply-laced Gram data.  The categorical lattice wrapper is deliberately
separate from this data layer.
-/

namespace LeanCategories.Lattices.Valued

/-- Vertices of the T-shaped diagram with arm lengths `p`, `q`, and `r`,
where the common branch vertex is counted in each source arm length. -/
inductive TTildeIndex (p q r : ℕ+)
  | branch
  | pArm (i : Fin ((p : ℕ) - 1))
  | qArm (i : Fin ((q : ℕ) - 1))
  | rArm (i : Fin ((r : ℕ) - 1))
  deriving DecidableEq, Fintype

/-- The source rank parameter `p + q + r - 2`. -/
def tTildeRank (p q r : ℕ+) : ℕ :=
  (p : ℕ) + (q : ℕ) + (r : ℕ) - 2

/-- Pairing data along one arm: square `-2`, adjacent entries `1`, and
all other entries `0`. -/
def tTildeArmPairing {n : ℕ} (i j : Fin n) : ℤ :=
  if i = j then -2
  else if i.val + 1 = j.val ∨ j.val + 1 = i.val then 1
  else 0

/-- Pairing of the branch vertex with a vertex on an arm.  The arm is
indexed from its leaf toward the branch, so only its final vertex pairs
nontrivially with the branch. -/
def tTildeBranchPairing (n : ℕ+) (i : Fin ((n : ℕ) - 1)) : ℤ :=
  if i.val + 1 = (n : ℕ) - 1 then 1 else 0

/-- The negative simply-laced T-shaped Gram matrix defining the source
data for `T̃_{p,q,r}`. -/
def tTildeGramMatrix (p q r : ℕ+) :
    Matrix (TTildeIndex p q r) (TTildeIndex p q r) ℤ
  | .branch, .branch => -2
  | .branch, .pArm i => tTildeBranchPairing p i
  | .pArm i, .branch => tTildeBranchPairing p i
  | .branch, .qArm i => tTildeBranchPairing q i
  | .qArm i, .branch => tTildeBranchPairing q i
  | .branch, .rArm i => tTildeBranchPairing r i
  | .rArm i, .branch => tTildeBranchPairing r i
  | .pArm i, .pArm j => tTildeArmPairing i j
  | .qArm i, .qArm j => tTildeArmPairing i j
  | .rArm i, .rArm j => tTildeArmPairing i j
  | .pArm _, .qArm _ => 0
  | .pArm _, .rArm _ => 0
  | .qArm _, .pArm _ => 0
  | .qArm _, .rArm _ => 0
  | .rArm _, .pArm _ => 0
  | .rArm _, .qArm _ => 0

end LeanCategories.Lattices.Valued
