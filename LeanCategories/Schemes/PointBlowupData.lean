/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Schemes.BirationalSurfaceModels
public import Mathlib.LinearAlgebra.Projectivization.Basic
public import Mathlib.RingTheory.Ideal.Cotangent

/-!
# Blow-up data for a smooth complex surface at a point

Definition-level realization of Beauville FC12-C02-U001.

Beauville II.1 introduces the blow-up `ε : Ŝ → S` of a smooth surface at a
point `p`, characterized here by the source-level data used in that
definition:

* `ε` is an isomorphism away from `p`;
* its exceptional curve is a projective line parametrizing tangent directions
  at `p`;
* the strict transform of a curve is the closure of the inverse image away
  from `p`.

The current library does not construct the global blow-up scheme.  Sweep III
therefore stores candidate data and the exact defining graph, and selects the
blow-up datum from that graph.  Existence of a candidate satisfying the graph,
the projective-line and tangent-space identifications, and their geometric
compatibilities are result-layer statements and are not proved here.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Topology
open scoped LinearAlgebra.Projectivization

namespace LeanCategories.Schemes

/-- Cotangent space of the local ring of `S` at `p`. -/
abbrev surfacePointCotangentSpaceData
    (S : SmoothProjectiveComplexSurface) (p : S.scheme) :=
  IsLocalRing.CotangentSpace (S.scheme.presheaf.stalk p)

/-- Zariski tangent space, represented as the dual of the local cotangent
space. -/
abbrev surfacePointTangentSpaceData
    (S : SmoothProjectiveComplexSurface) (p : S.scheme) :=
  Module.Dual
    (IsLocalRing.ResidueField (S.scheme.presheaf.stalk p))
    (surfacePointCotangentSpaceData S p)

/-- Projectivized tangent directions at `p`. -/
abbrev surfacePointTangentDirectionsData
    (S : SmoothProjectiveComplexSurface) (p : S.scheme) :=
  Projectivization
    (IsLocalRing.ResidueField (S.scheme.presheaf.stalk p))
    (surfacePointTangentSpaceData S p)

/-- Raw candidate data for the blow-up of `S` at `p`.

All geometric conditions are kept in `IsPointBlowupData`; constructing a
candidate therefore requires no new proof-valued fields. -/
structure PointBlowupCandidateData
    (S : SmoothProjectiveComplexSurface) (p : S.scheme) where
  surface : SmoothProjectiveComplexSurface
  projection : surface.scheme ⟶ S.scheme
  exceptionalScheme : Scheme
  exceptionalι : exceptionalScheme ⟶ surface.scheme
  strictTransform : Set S.scheme → Set surface.scheme

/-- The candidate type is inhabited independently of the blow-up existence
theorem. -/
instance (S : SmoothProjectiveComplexSurface) (p : S.scheme) :
    Nonempty (PointBlowupCandidateData S p) :=
  ⟨{
    surface := S
    projection := 𝟙 S.scheme
    exceptionalScheme := S.scheme
    exceptionalι := 𝟙 S.scheme
    strictTransform := fun C => C
  }⟩

/-- Beauville II.1's exact definition-level graph for blowing up a smooth
complex surface at a point.

The exceptional subscheme is the set-theoretic fibre over `p`, is a
projective line, and its points parametrize the projectivized Zariski tangent
space.  The strict-transform assignment is literally topological closure of
the inverse image of the punctured curve. -/
def IsPointBlowupData
    (S : SmoothProjectiveComplexSurface) (p : S.scheme)
    (B : PointBlowupCandidateData S p) : Prop :=
  B.projection ≫ S.structureMap = B.surface.structureMap ∧
    IsClosed ({p} : Set S.scheme) ∧
    (∃ U : S.scheme.Opens,
      (U : Set S.scheme) = ({p} : Set S.scheme)ᶜ ∧
        IsIso (B.projection ∣_ U)) ∧
    IsClosedImmersion B.exceptionalι ∧
    Set.range B.exceptionalι.base =
      B.projection.base ⁻¹' ({p} : Set S.scheme) ∧
    Nonempty
      (B.exceptionalScheme ≅
        ProjectiveSpace
          (IsLocalRing.ResidueField (S.scheme.presheaf.stalk p)) 1) ∧
    Module.finrank
        (IsLocalRing.ResidueField (S.scheme.presheaf.stalk p))
        (surfacePointTangentSpaceData S p) = 2 ∧
    Nonempty
      (B.exceptionalScheme ≃ surfacePointTangentDirectionsData S p) ∧
    ∀ C : Set S.scheme,
      B.strictTransform C =
        closure (B.projection.base ⁻¹' (C \ ({p} : Set S.scheme)))

end LeanCategories.Schemes
