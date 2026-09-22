/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Topology.ContinuedFractionPlumbingData
public import LeanCategories.Topology.ComplexSurfaceResolutionData
public import LeanCategories.Topology.HirzebruchJungSingularityData
public import Mathlib.Combinatorics.SimpleGraph.Basic

/-!
# Hirzebruch--Jung resolution data

Definition-level realization of Peters--Sterk FC11-C04-U056.

The checked libraries do not provide a category of possibly singular complex
analytic surfaces with holomorphic quotient germs and resolutions.  This file
therefore isolates that missing analytic layer in an explicit interface and
records the source definition of a resolution without proving that a
particular resolution exists.

For the Hirzebruch--Jung quotient `A_{t,s}`, the source additionally specifies
the exceptional fibre as a string of projective lines whose dual graph is the
linear continued-fraction graph and whose self-intersections are `-m_i`.
Those are recorded as supplied construction data.  No existence theorem, no
smoothness theorem for a glued surface, and no biholomorphic-identification
proof is constructed in Sweep III.

The source also writes `A_n` for `A_{n+1,n}` and gives the familiar local
equation `uv = w^(n+1)`.  Both the notation and the raw hypersurface model are
defined below; identifying that hypersurface analytically with the quotient is
result-layer work.
-/

@[expose] public noncomputable section

namespace LeanCategories.Topology

universe u

/-- Peters--Sterk's definition of a resolution of an isolated surface
singularity, expressed against the missing analytic interface.

An instance consists of a smooth source surface and a holomorphic map to the
singular surface which is biholomorphic away from the fibre over the singular
point.  This definition has no existence content. -/
structure ComplexSurfaceSingularityResolutionData
    (I : ComplexSurfaceResolutionInterface.{u})
    (Y : TopCat.{u}) (p : Y) where
  source : TopCat.{u}
  map : source → Y
  source_isSmooth : I.IsSmoothComplexSurface source
  target_isIsolatedSingularity : I.IsIsolatedSurfaceSingularity Y p
  map_isHolomorphic : I.IsHolomorphicMap map
  map_isBiholomorphicOutsideFiber :
    I.IsBiholomorphicOutsideFiber map p

/-- The exceptional divisor of a resolution: the fibre over the singular
point. -/
def resolutionExceptionalDivisor
    {I : ComplexSurfaceResolutionInterface.{u}}
    {Y : TopCat.{u}} {p : Y}
    (R : ComplexSurfaceSingularityResolutionData I Y p) :
    Set R.source :=
  R.map ⁻¹' {p}

/-- The dual graph of a family of curves: distinct vertices are adjacent
exactly when the corresponding curves meet. -/
def curveConfigurationDualGraph
    {X : Type u} {J : Type*}
    (curve : J → Set X) : SimpleGraph J :=
  SimpleGraph.fromRel fun i j =>
    (curve i ∩ curve j).Nonempty

/-- The distinguished origin, viewed in the bundled Hirzebruch--Jung quotient
space. -/
def hirzebruchJungOriginPoint (t s : ℕ) :
    hirzebruchJungQuotientTopCat t s := by
  change HirzebruchJungQuotient t s
  exact hirzebruchJungOrigin t s

/-- A resolution datum whose target is the Hirzebruch--Jung quotient
`W_{t,s}` and whose distinguished singular point is the origin orbit. -/
abbrev HirzebruchJungResolutionData
    (I : ComplexSurfaceResolutionInterface.{0}) (t s : ℕ) :=
  ComplexSurfaceSingularityResolutionData I
    (hirzebruchJungQuotientTopCat t s)
    (hirzebruchJungOriginPoint t s)

/-- Source-supplied exceptional-chain data for a Hirzebruch--Jung resolution.

The coefficient equation is the same negative continued fraction used in the
plumbing construction.  The exact dual-graph equation records both that
consecutive curves meet and that there are no other intersections; the
separate transversality field records the source's stronger local statement.
No value of this structure is manufactured here. -/
structure HirzebruchJungExceptionalChainData
    (I : ComplexSurfaceResolutionInterface.{0})
    (t s : ℕ) (R : HirzebruchJungResolutionData I t s) where
  n : ℕ
  m : Fin (n + 1) → ℤ
  isLensCoefficientSequence :
    IsLensPlumbingCoefficientSequence (s : ℤ) (t : ℤ) m
  curve : Fin (n + 1) → Set R.source
  curve_isProjectiveLine :
    ∀ i, I.IsProjectiveLineCurve (curve i)
  exceptional_eq_union :
    resolutionExceptionalDivisor R = ⋃ i, curve i
  dualGraph_eq :
    curveConfigurationDualGraph curve =
      continuedFractionPlumbingGraph n
  selfIntersection :
    ∀ i, I.HasSelfIntersection (curve i) (-m i)
  adjacent_meetTransversely :
    ∀ {i j}, (continuedFractionPlumbingGraph n).Adj i j →
      I.MeetTransverselyInOnePoint (curve i) (curve j)

/-- A complete data-level Hirzebruch--Jung resolution specification:
a resolution together with the source exceptional chain.

Existence of such data for `A_{t,s}` is a theorem, not part of this
definition. -/
structure HirzebruchJungResolutionConstructionData
    (I : ComplexSurfaceResolutionInterface.{0}) (t s : ℕ) where
  resolution : HirzebruchJungResolutionData I t s
  exceptionalChain :
    HirzebruchJungExceptionalChainData I t s resolution

/-- The raw hypersurface carrying the source local equation
`uv = w^(n+1)`.  The ambient coordinates are `((u,v),w)`. -/
def duValAHypersurface (n : ℕ) : Set ((ℂ × ℂ) × ℂ) :=
  {z | z.1.1 * z.1.2 = z.2 ^ (n + 1)}

/-- The source notation `A_n = A_{n+1,n}` at the definition-data level. -/
abbrev DuValASingularityData (n : ℕ) :=
  HirzebruchJungSingularityData (n + 1) n

/-- The canonical pointed quotient carrying the source notation
`A_n = A_{n+1,n}`. -/
def duValASingularityData (n : ℕ) : DuValASingularityData n :=
  hirzebruchJungSingularityData (n + 1) n

end LeanCategories.Topology
