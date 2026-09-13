/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Homological.Spectrification
public import LeanCategories.Topology.HomotopyGroups
public import Mathlib.Topology.CWComplex.Classical.Basic

/-!
# CW prespectra and Ω-spectra

Hatcher's terminology in Chapter 4 calls a sequence of based CW complexes with suspension
structure maps a *spectrum*.  The repository already owns the underlying sequence and structure
maps as `Prespectrum`; this file adds exactly the CW-level condition needed by Hatcher without
requiring Weibel's stronger cellular-inclusion condition on the structure maps.

The adjoint maps `Dₙ → ΩDₙ₊₁` are already constructed in `Spectrification.lean`.  Requiring these
maps to be weak homotopy equivalences is Hatcher's definition of an Ω-spectrum.
-/

@[expose] public section

noncomputable section

open CategoryTheory

namespace LeanCategories.Homological

open LeanCategories.Topology
open Set

universe u

namespace Prespectrum

/-- Chosen CW structures on every level of a prespectrum. -/
structure CWLevelStructure (D : Prespectrum.{u}) where
  cwLevel : ∀ n : ℕ, Topology.CWComplex (Set.univ : Set (D.space n).right)

/-- A prespectrum has CW levels when each of its based level spaces is a CW complex.

Unlike `Prespectrum.IsCW`, this places no cellularity or embedding condition on the structure
maps.  This is exactly the extra condition in Hatcher's definition of a spectrum.

Source: Hatcher, *Algebraic Topology*, §4.F, p. 406 (FC07-C04-U137). -/
def HasCWLevels (D : Prespectrum.{u}) : Prop :=
  Nonempty (CWLevelStructure D)

/-- Hatcher's Ω-spectrum condition on a prespectrum: every level is a CW complex and every
adjoint structure map `Dₙ → ΩDₙ₊₁` is a weak homotopy equivalence.

Source: Hatcher, *Algebraic Topology*, §4.3, p. 393 (FC07-C04-U077). -/
def IsOmegaSpectrum (D : Prespectrum.{u}) : Prop :=
  HasCWLevels D ∧
    ∀ n : ℕ, IsWeakHomotopyEquivalence (prespectrumLoopAdjoint D n).right.hom

end Prespectrum

/-- Hatcher's topological spectrum: a prespectrum whose level spaces are CW complexes.

The generalized-homology theory represented by such a spectrum is theorem-level content and is
not built into this structure.

Source: Hatcher, *Algebraic Topology*, §4.F, p. 406 (FC07-C04-U137). -/
structure CWPrespectrum extends Prespectrum.{u} where
  cwLevels : Prespectrum.CWLevelStructure toPrespectrum

end LeanCategories.Homological
