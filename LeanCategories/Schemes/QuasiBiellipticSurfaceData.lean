/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Schemes.BiellipticSurfaceData
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Topology

/-!
# Quasi-bielliptic surface data

Definition-level realization of Beauville FC12-A-U007.

In characteristics two or three Beauville defines a quasi-bielliptic surface
as a quotient `(E × C) / G`, where `E` is elliptic and `C` is a
cuspidal cubic.  The accompanying assertion on the order of the canonical
class is result content and is not built into the definition here.

The cuspidal cubic is represented scheme-theoretically, not merely as a set:
it is a reduced closed subscheme of the projective plane with underlying
closed set `V(Y²Z - X³)`.  For a reduced closed subscheme this fixes the
usual reduced scheme structure while requiring no quotient-ring grading
construction in Sweep III.

As for FC12-C06-U023, quotient existence is not constructed.  A supplied
surface satisfies the predicate when there are group-action and quotient-map
data satisfying the categorical quotient universal property.
-/

@[expose] public noncomputable section

open CategoryTheory Limits MonoidalCategory
open _root_.AlgebraicGeometry
open LeanCategories.AlgebraicGeometry

namespace LeanCategories.Schemes

universe u

/-- The structural morphism `P^n_k → Spec k`. -/
def projectiveSpaceToSpecData
    (k : Type u) [Field k] (n : ℕ) :
    ProjectiveSpace k n ⟶ Spec (.of k) :=
  ProjectiveSpace.structureMorphism k n ≫
    Spec.map
      (CommRingCat.ofHom
        (algebraMap k (projectiveSpaceGrading k n 0)))

/-- A smooth projective surface over a field.  This is the field-generic
counterpart of `SmoothProjectiveComplexSurface` used by the characteristic
zero chapters. -/
structure SmoothProjectiveSurfaceData (k : Type u) [Field k] where
  scheme : Scheme.{u}
  structureMap : scheme ⟶ Spec (.of k)
  integral : IsIntegral scheme
  smooth : SmoothOfRelativeDimension 2 structureMap
  projective : ∃ (n : ℕ) (ι : scheme ⟶ ProjectiveSpace k n),
    IsClosedImmersion ι ∧ ι ≫ projectiveSpaceToSpecData k n = structureMap

/-- A field-generic smooth projective surface as an object over its base. -/
abbrev SmoothProjectiveSurfaceData.toOver
    {k : Type u} [Field k] (S : SmoothProjectiveSurfaceData k) :
    Over (Spec (.of k)) :=
  Over.mk S.structureMap

/-- The homogeneous cubic `Y²Z-X³` cutting out the standard cuspidal cubic
in the projective plane. -/
def cuspidalCubicPolynomialData
    (k : Type u) [Field k] : MvPolynomial (Fin 3) k :=
  MvPolynomial.X 1 ^ 2 * MvPolynomial.X 2 -
    MvPolynomial.X 0 ^ 3

/-- Raw scheme and embedding data for a candidate plane cuspidal cubic. -/
structure CuspidalCubicCandidateData (k : Type u) [Field k] where
  scheme : Scheme.{u}
  structureMap : scheme ⟶ Spec (.of k)
  embedding : scheme ⟶ ProjectiveSpace k 2

/-- A cuspidal cubic candidate as an object over `Spec k`. -/
abbrev CuspidalCubicCandidateData.toOver
    {k : Type u} [Field k] (C : CuspidalCubicCandidateData k) :
    Over (Spec (.of k)) :=
  Over.mk C.structureMap

/-- Exact reduced closed-subscheme presentation of the standard cuspidal
cubic `Y²Z=X³`. -/
def IsCuspidalCubicData
    {k : Type u} [Field k] (C : CuspidalCubicCandidateData k) : Prop :=
  IsReduced C.scheme ∧
    IsClosedImmersion C.embedding ∧
    C.embedding ≫ projectiveSpaceToSpecData k 2 = C.structureMap ∧
    Set.range C.embedding.base =
      ProjectiveSpectrum.zeroLocus
        (projectiveSpaceGrading k 2)
        {cuspidalCubicPolynomialData k}

/-- Beauville Appendix A's quasi-bielliptic-surface definition.

The canonical-class order dividing `4` or `6` is not a constructor clause:
it is the numerical assertion following the quotient description and remains
Sweep-IV result content. -/
def IsQuasiBiellipticSurfaceData
    {k : Type u} [Field k] [IsAlgClosed k]
    (S : SmoothProjectiveSurfaceData k) : Prop :=
  (CharP k 2 ∨ CharP k 3) ∧
    ∃ (E : AbelianVariety k),
      IsEllipticCurveData E ∧
        ∃ (C : CuspidalCubicCandidateData k),
          IsCuspidalCubicData C ∧
            ∃ (G : Type u) (_ : Group G)
              (ρ : GroupActionHomData G (E.toOver ⊗ C.toOver))
              (q : E.toOver ⊗ C.toOver ⟶ S.toOver),
              IsGroupQuotientData G ρ q

end LeanCategories.Schemes
