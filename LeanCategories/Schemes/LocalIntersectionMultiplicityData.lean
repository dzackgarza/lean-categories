/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# Local intersection multiplicity of curve germs

Definition-level realization of Beauville FC12-C01-U002.

For a closed subscheme `C ↪ S`, Mathlib's ideal-sheaf kernel is intrinsic.
Its ideal in the stalk at `x` is the filtered union of the affine-neighbourhood
ideals mapped to `𝒪_{S,x}`. Thus two curve germs determine ideals `I_C,x` and
`I_C',x` without choosing local equations. When those ideals are principal,
say `(f)` and `(g)`, their sum is exactly `(f,g)`, so

`dim_ℂ 𝒪_{S,x}/(I_C,x + I_C',x)`

is Beauville's displayed `dim_ℂ 𝒪_{S,x}/(f,g)` independently of the chosen
generators.

The definitions make sense for arbitrary closed immersions into a scheme
whose stalk carries its complex-algebra structure. In Beauville's source
specialization the ambient scheme is a smooth complex surface and the closed
immersions are distinct irreducible curves through `x`. Principality,
finite-dimensionality, and comparison with tangent-space transversality are
geometric results and are not constructor fields here.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace LeanCategories.Schemes

universe u

/-- The intrinsic stalk ideal of an ideal sheaf at `x`, constructed from the
affine-open basis by mapping every local ideal into the stalk and taking their
supremum. -/
def idealSheafStalkIdealData {S : Scheme.{u}}
    (I : S.IdealSheafData) (x : S) : Ideal (S.presheaf.stalk x) :=
  ⨆ (U : S.affineOpens) (hx : x ∈ (U.1 : Set S)),
    Ideal.map (S.presheaf.germ U.1 x hx).hom (I.ideal U)

/-- The local ideal at `x` of a closed subscheme `C ↪ S`. -/
def closedImmersionStalkIdealData {C S : Scheme.{u}}
    (i : C ⟶ S) [IsClosedImmersion i] (x : S) :
    Ideal (S.presheaf.stalk x) :=
  idealSheafStalkIdealData i.ker x

/-- Beauville's local intersection multiplicity of two closed curve germs at
`x`, expressed intrinsically through their stalk ideals.

For the source's smooth complex surface, the curve ideals are locally
principal, so the quotient is literally `𝒪_{S,x}/(f,g)` for any local
equations `f,g`. -/
def localIntersectionMultiplicityData {C C' S : Scheme.{u}}
    (i : C ⟶ S) (j : C' ⟶ S)
    [IsClosedImmersion i] [IsClosedImmersion j]
    (x : S) [Algebra ℂ (S.presheaf.stalk x)] : ℕ :=
  Module.finrank ℂ
    ((S.presheaf.stalk x) ⧸
      (closedImmersionStalkIdealData i x ⊔ closedImmersionStalkIdealData j x))

/-- Beauville's local transversality terminology: the two curve germs meet
transversely at `x` exactly when their local intersection multiplicity is one. -/
def AreLocallyTransverseData {C C' S : Scheme.{u}}
    (i : C ⟶ S) (j : C' ⟶ S)
    [IsClosedImmersion i] [IsClosedImmersion j]
    (x : S) [Algebra ℂ (S.presheaf.stalk x)] : Prop :=
  localIntersectionMultiplicityData i j x = 1

end LeanCategories.Schemes
