/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.AlgebraicGeometry.AffinePointSpace
public import Mathlib.RingTheory.Nullstellensatz
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.Topology.Irreducible

/-!
# Hartshorne's classical affine and quasi-affine varieties

Hartshorne, *Algebraic Geometry* (1977), Chapter I, §1, pp. 1--7
(FC06-C01-U011).

The affine point space `A^n_k = k^n` is given its Zariski topology.  An affine
variety is an irreducible closed subset, and a quasi-affine variety is an open
subset of an affine variety.
-/

@[expose] public noncomputable section

namespace LeanCategories.AlgebraicGeometry

universe u

variable (k : Type u) [Field k] [IsAlgClosed k]

/-- The Zariski topology on Hartshorne's classical affine point space, induced
from the canonical point map into `Spec k[x₁,…,xₙ]`.

This is the point-set topology whose algebraic closed sets are the polynomial
zero loci used in Chapter I. -/
def affineZariskiTopology (n : ℕ) : TopologicalSpace (AffinePointSpace k n) :=
  TopologicalSpace.induced
    (MvPolynomial.pointToPoint (k := k) : (Fin n → k) →
      PrimeSpectrum (MvPolynomial (Fin n) k))
    PrimeSpectrum.zariskiTopology

local instance affinePointSpaceTopology (n : ℕ) :
    TopologicalSpace (AffinePointSpace k n) :=
  affineZariskiTopology k n

/-- Hartshorne's affine variety: an irreducible closed subset of `A^n_k`.

Source: Hartshorne, Chapter I, §1, p. 3 (FC06-C01-U011). -/
structure AffineVariety (n : ℕ) where
  /-- The point set of the variety. -/
  carrier : Set (AffinePointSpace k n)
  /-- It is Zariski closed. -/
  isClosed : IsClosed carrier
  /-- It is irreducible. -/
  irreducible : IsIrreducible carrier

/-- The underlying topological space of an affine variety. -/
abbrev AffineVariety.Points {n : ℕ} (Y : AffineVariety k n) :=
  ↥Y.carrier

/-- Hartshorne's quasi-affine variety: an open subset of an affine variety.

Using an open of the subtype gives the relative topology literally, rather
than incorrectly requiring the subset to be open in all of affine space.

Source: Hartshorne, Chapter I, §1, p. 3 (FC06-C01-U011). -/
structure QuasiAffineVariety (n : ℕ) where
  /-- An ambient affine variety. -/
  ambient : AffineVariety k n
  /-- The chosen open subset in the relative topology of the ambient variety. -/
  openSet : TopologicalSpace.Opens ambient.Points

/-- The underlying subset of affine point space of a quasi-affine variety. -/
def QuasiAffineVariety.carrier {n : ℕ} (Y : QuasiAffineVariety k n) :
    Set (AffinePointSpace k n) :=
  Subtype.val '' (Y.openSet : Set Y.ambient.Points)

end LeanCategories.AlgebraicGeometry
