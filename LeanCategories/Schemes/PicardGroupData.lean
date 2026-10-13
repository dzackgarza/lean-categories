/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.AlgebraicGeometry.AmpleSheaf
public import Mathlib.CategoryTheory.Skeletal

/-!
# Picard-group definition data

Definition-level realization of Hartshorne FC06-C02-U189.

Hartshorne defines `Pic X` as the group of isomorphism classes of invertible
`O_X`-modules, with multiplication induced by tensor product.  The repository
already has proof-free owners for the sheafified tensor product, its unit, and
the tensor-invertibility predicate in `AlgebraicGeometry/AmpleSheaf.lean`.

Packaging these iso-classes immediately as a Lean `CommGroup` would require the
closure, inverse, associativity, and symmetry results of Hartshorne Proposition
6.12 (FC06-C02-U188).  Sweep III does not prove those results.  This file
therefore records the exact data-level presentation:

* the full category of tensor-invertible sheaves;
* its skeleton, i.e. isomorphism classes of invertible sheaves;
* the tensor-product graph on those classes;
* the unit-class graph; and
* the inverse-class graph.

The theorem layer proves that these graphs are total and single-valued and
install the resulting commutative group structure.
-/

@[expose] public section

open CategoryTheory
open LeanCategories.AlgebraicGeometry

namespace LeanCategories.Schemes

universe u

variable (X : AlgebraicGeometry.Scheme.{u})

/-- The object property selecting tensor-invertible `O_X`-modules. -/
def invertibleSheafPropertyData : ObjectProperty X.Modules :=
  IsTensorInvertible

/-- The full subcategory of tensor-invertible sheaves on `X`. -/
abbrev InvertibleSheafCategoryData :=
  (invertibleSheafPropertyData X).FullSubcategory

/-- The underlying Picard carrier: isomorphism classes of invertible sheaves. -/
abbrev PicardGroupCarrierData :=
  Skeleton (InvertibleSheafCategoryData X)

/-- Source-facing alias for the Picard iso-class carrier.

The group laws are not installed in Sweep III; their defining operation graphs
are recorded below and become a `CommGroup` only after FC06-C02-U188. -/
abbrev PicardGroupData := PicardGroupCarrierData X

/-- Graph of multiplication in `Pic X`: `c` is the class of `L ⊗ M` when
`a=[L]` and `b=[M]`.

The existential `hLM` is precisely the tensor-closure result supplied by
FC06-C02-U188; it is not constructed here. -/
def IsPicardTensorProductData
    (a b c : PicardGroupData X) : Prop :=
  ∃ (L M : X.Modules)
      (hL : IsTensorInvertible L)
      (hM : IsTensorInvertible M)
      (hLM : IsTensorInvertible (schemeModuleTensor L M)),
    a = toSkeleton (C := InvertibleSheafCategoryData X) ⟨L, hL⟩ ∧
      b = toSkeleton (C := InvertibleSheafCategoryData X) ⟨M, hM⟩ ∧
        c = toSkeleton (C := InvertibleSheafCategoryData X)
          ⟨schemeModuleTensor L M, hLM⟩

/-- Graph of the neutral element in `Pic X`: the class of the structure sheaf. -/
def IsPicardUnitData (e : PicardGroupData X) : Prop :=
  ∃ hO : IsTensorInvertible (schemeModuleUnit X),
    e = toSkeleton (C := InvertibleSheafCategoryData X)
      ⟨schemeModuleUnit X, hO⟩

/-- Graph of inversion in `Pic X`: `b=[L⁻¹]` when representatives tensor to
the structure sheaf in both orders.

Invertibility of the chosen inverse representative and the two displayed
isomorphisms are retained propositionally; Sweep III selects none of them. -/
def IsPicardInverseData (a b : PicardGroupData X) : Prop :=
  ∃ (L LInv : X.Modules)
      (hL : IsTensorInvertible L)
      (hLInv : IsTensorInvertible LInv),
    a = toSkeleton (C := InvertibleSheafCategoryData X) ⟨L, hL⟩ ∧
      b = toSkeleton (C := InvertibleSheafCategoryData X) ⟨LInv, hLInv⟩ ∧
        Nonempty (schemeModuleTensor L LInv ≅ schemeModuleUnit X) ∧
          Nonempty (schemeModuleTensor LInv L ≅ schemeModuleUnit X)

end LeanCategories.Schemes
