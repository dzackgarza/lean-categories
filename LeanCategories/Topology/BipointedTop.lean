/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Topology.Category.TopCat.Basic
public import Mathlib.Topology.Category.TopCat.Limits.Basic
public import Mathlib.Topology.Separation.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

@[expose] public section

open CategoryTheory CategoryTheory.Limits Topology

namespace LeanCategories.Topology

universe u

/-- Riehl Appendix E.3 (FC03-CE-U005): a bipointed space is a topological space with
 two distinct designated closed points. -/
structure BipointedTop : Type (u + 1) where
  /-- The underlying topological space. -/
  X : TopCat.{u}
  /-- The designated left endpoint. -/
  left : X
  /-- The designated right endpoint. -/
  right : X
  /-- The endpoints are distinct. -/
  left_ne_right : left ≠ right
  /-- The left endpoint is closed. -/
  isClosed_left : IsClosed ({left} : Set X)
  /-- The right endpoint is closed. -/
  isClosed_right : IsClosed ({right} : Set X)

instance : CoeSort BipointedTop (Type u) := ⟨fun X => X.X⟩

/-- Morphisms of bipointed spaces are continuous maps preserving both endpoints. -/
@[ext]
structure BipointedTop.Hom (X Y : BipointedTop.{u}) where
  /-- The underlying continuous map. -/
  toHom : X.X ⟶ Y.X
  /-- The left endpoint is preserved. -/
  map_left : toHom X.left = Y.left
  /-- The right endpoint is preserved. -/
  map_right : toHom X.right = Y.right

instance : Category BipointedTop where
  Hom := BipointedTop.Hom
  id X := ⟨𝟙 X.X, by simp, by simp⟩
  comp f g :=
    ⟨f.toHom ≫ g.toHom, by simp [f.map_left, g.map_left], by simp [f.map_right, g.map_right]⟩

/-- The map from a one-point space selecting an endpoint of a bipointed space. -/
noncomputable def BipointedTop.endpointMap (X : BipointedTop.{u}) (x : X.X) :
    TopCat.of PUnit.{u + 1} ⟶ X.X :=
  TopCat.ofHom (ContinuousMap.const (TopCat.of PUnit) x)

/-- The underlying wedge/gluing space of two bipointed spaces: glue the right endpoint of `X`
to the left endpoint of `Y` by the corresponding pushout in `TopCat` (FC03-CE-U005). -/
noncomputable def BipointedTop.wedgeSpace (X Y : BipointedTop.{u}) : TopCat.{u} :=
  pushout (X.endpointMap X.right) (Y.endpointMap Y.left)

/-- The surviving left endpoint in `X.wedgeSpace Y`. -/
noncomputable def BipointedTop.wedgeLeft (X Y : BipointedTop.{u}) : X.wedgeSpace Y :=
  pushout.inl (X.endpointMap X.right) (Y.endpointMap Y.left) X.left

/-- The surviving right endpoint in `X.wedgeSpace Y`. -/
noncomputable def BipointedTop.wedgeRight (X Y : BipointedTop.{u}) : X.wedgeSpace Y :=
  pushout.inr (X.endpointMap X.right) (Y.endpointMap Y.left) Y.right

end LeanCategories.Topology
