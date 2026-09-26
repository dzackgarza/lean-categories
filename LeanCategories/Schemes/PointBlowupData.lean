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

Mathlib exposes the Rees algebra and projective-spectrum ingredients but no
scheme-level blow-up constructor.  The source object is therefore represented
directly as bundled blow-up data: the surface, projection, exceptional
subscheme, strict transforms, and the defining compatibility proofs are fields
of `PointBlowupData`.  There is no candidate carrier or separately supplied
graph predicate.
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

/-- Beauville II.1's blow-up of a smooth complex surface at a point, bundled
with the defining geometric data and compatibilities.

The exceptional subscheme is the set-theoretic fibre over `p`, is a
projective line, and its points parametrize the projectivized Zariski tangent
space.  The strict-transform assignment is literally topological closure of
the inverse image of the punctured curve. -/
structure PointBlowupData
    (S : SmoothProjectiveComplexSurface) (p : S.scheme) where
  surface : SmoothProjectiveComplexSurface
  projection : surface.scheme ⟶ S.scheme
  exceptionalScheme : Scheme
  exceptionalι : exceptionalScheme ⟶ surface.scheme
  strictTransform : Set S.scheme → Set surface.scheme
  projection_over_base :
    projection ≫ S.structureMap = surface.structureMap
  center_closed : IsClosed ({p} : Set S.scheme)
  iso_away_from_center :
    ∃ U : S.scheme.Opens,
      (U : Set S.scheme) = ({p} : Set S.scheme)ᶜ ∧
        IsIso (projection ∣_ U)
  exceptional_closed : IsClosedImmersion exceptionalι
  exceptional_fiber :
    Set.range exceptionalι.base =
      projection.base ⁻¹' ({p} : Set S.scheme)
  exceptional_projective_line :
    Nonempty
      (exceptionalScheme ≅
        ProjectiveSpace
          (IsLocalRing.ResidueField (S.scheme.presheaf.stalk p)) 1)
  tangent_dimension :
    Module.finrank
        (IsLocalRing.ResidueField (S.scheme.presheaf.stalk p))
        (surfacePointTangentSpaceData S p) = 2
  exceptional_tangent_directions :
    Nonempty
      (exceptionalScheme ≃ surfacePointTangentDirectionsData S p)
  strictTransform_eq :
    ∀ C : Set S.scheme,
      strictTransform C =
        closure (projection.base ⁻¹' (C \ ({p} : Set S.scheme)))

/-- Beauville II.16's definition of an exceptional curve on a smooth
projective complex surface: it is the exceptional curve of a blow-up of
another smooth surface at a point.

The target surface and center are existential data, while the blow-down
morphism, exceptional subscheme and strict transforms are the fields of the
constructed `PointBlowupData`; no contraction or Castelnuovo theorem is used
here. -/
def IsExceptionalCurveData
    (S : SmoothProjectiveComplexSurface) (E : Set S.scheme) : Prop :=
  ∃ (T : SmoothProjectiveComplexSurface) (p : T.scheme)
    (B : PointBlowupData T p),
    ∃ h : B.surface = S,
      h ▸ Set.range B.exceptionalι.base = E

/-- The definition-level predicate that a surface contains no exceptional
curve.  Beauville's assertion that this is equivalent to minimality is
result-layer content. -/
def HasNoExceptionalCurveData
    (S : SmoothProjectiveComplexSurface) : Prop :=
  ∀ E : Set S.scheme, ¬ IsExceptionalCurveData S E

end LeanCategories.Schemes
