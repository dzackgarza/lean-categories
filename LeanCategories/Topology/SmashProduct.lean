/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Topology.Category.TopCat.Basic
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.Topology.Constructions

@[expose] public section

open _root_.CategoryTheory
open scoped _root_.CategoryTheory

namespace LeanCategories.Topology

universe u

/-- Riehl's category `Top_*` of based topological spaces, realized canonically as the under
category of the one-point space in `TopCat`. Objects are maps `* ⟶ X`; morphisms are continuous
maps commuting with the chosen basepoints. -/
abbrev BasedTop := _root_.CategoryTheory.Under (_root_.TopCat.of PUnit.{u + 1})

namespace BasedTop

/-- The distinguished point of a based space. -/
def point (X : BasedTop.{u}) : X.right := X.hom PUnit.unit

/-- A morphism of based spaces preserves the distinguished point. -/
theorem map_point {X Y : BasedTop.{u}} (f : X ⟶ Y) : f.right X.point = Y.point := by
  exact congrArg (fun k => k PUnit.unit) (_root_.CategoryTheory.Under.w f)

end BasedTop

/-- The wedge subset of the product of two based spaces: pairs for which at least one coordinate
is the basepoint. This is exactly the subspace collapsed by the smash product. -/
def wedgeSet (X Y : BasedTop.{u}) : Set (X.right × Y.right) :=
  {p | p.1 = X.point ∨ p.2 = Y.point}

/-- Equivalence relation on `X × Y` that identifies exactly the wedge subset and leaves every
point outside the wedge in its own equivalence class. -/
def smashSetoid (X Y : BasedTop.{u}) : Setoid (X.right × Y.right) where
  r p q := p = q ∨ (p ∈ wedgeSet X Y ∧ q ∈ wedgeSet X Y)
  iseqv := by
    refine ⟨fun p => Or.inl rfl, ?_, ?_⟩
    · intro p q h
      rcases h with rfl | ⟨hp, hq⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨hq, hp⟩
    · intro p q r hpq hqr
      rcases hpq with rfl | ⟨hp, hq⟩
      · exact hqr
      rcases hqr with rfl | ⟨_, hr⟩
      · exact Or.inr ⟨hp, hq⟩
      · exact Or.inr ⟨hp, hr⟩

/-- The underlying topological smash product `(X × Y)/(X ∨ Y)`. Mathlib supplies the canonical
quotient topology on this quotient. -/
abbrev Smash (X Y : BasedTop.{u}) := Quotient (smashSetoid X Y)

/-- The distinguished point of the smash product, namely the collapsed wedge class. -/
def smashPoint (X Y : BasedTop.{u}) : Smash X Y :=
  Quotient.mk (smashSetoid X Y) (X.point, Y.point)

/-- The smash product of two based spaces as an object of `Top_*`. -/
def smashObj (X Y : BasedTop.{u}) : BasedTop.{u} :=
  _root_.CategoryTheory.Under.mk
    (_root_.TopCat.ofHom ⟨fun _ : PUnit => smashPoint X Y, continuous_const⟩)

/-- The product map induced by a pair of based maps before passing to the smash quotient. -/
def pairMap {X X' Y Y' : BasedTop.{u}} (f : X ⟶ X') (g : Y ⟶ Y') :
    X.right × Y.right → X'.right × Y'.right :=
  fun p => (f.right p.1, g.right p.2)

/-- Based maps carry the smash equivalence relation into the smash equivalence relation. -/
theorem pairMap_rel {X X' Y Y' : BasedTop.{u}} (f : X ⟶ X') (g : Y ⟶ Y')
    {p q : X.right × Y.right} :
    smashSetoid X Y p q → smashSetoid X' Y' (pairMap f g p) (pairMap f g q) := by
  intro h
  rcases h with rfl | ⟨hp, hq⟩
  · exact Or.inl rfl
  · right
    constructor
    · rcases hp with hx | hy
      · left
        change f.right p.1 = X'.point
        rw [hx]
        exact BasedTop.map_point f
      · right
        change g.right p.2 = Y'.point
        rw [hy]
        exact BasedTop.map_point g
    · rcases hq with hx | hy
      · left
        change f.right q.1 = X'.point
        rw [hx]
        exact BasedTop.map_point f
      · right
        change g.right q.2 = Y'.point
        rw [hy]
        exact BasedTop.map_point g

/-- The map on smash products induced by two based maps. -/
def smashMapFn {X X' Y Y' : BasedTop.{u}} (f : X ⟶ X') (g : Y ⟶ Y') :
    Smash X Y → Smash X' Y' :=
  Quotient.lift
    (fun p => Quotient.mk (smashSetoid X' Y') (pairMap f g p))
    (fun _ _ h => Quotient.sound (pairMap_rel f g h))

/-- The product map on representatives is continuous. -/
theorem continuous_pairMap {X X' Y Y' : BasedTop.{u}} (f : X ⟶ X') (g : Y ⟶ Y') :
    Continuous (pairMap f g) := by
  exact Continuous.prodMk
    (f.right.hom.continuous_toFun.comp continuous_fst)
    (g.right.hom.continuous_toFun.comp continuous_snd)

/-- The induced map on smash quotients is continuous. -/
theorem continuous_smashMapFn {X X' Y Y' : BasedTop.{u}} (f : X ⟶ X') (g : Y ⟶ Y') :
    Continuous (smashMapFn f g) := by
  exact (continuous_quotient_mk'.comp (continuous_pairMap f g)).quotient_lift
    (fun _ _ h => Quotient.sound (pairMap_rel f g h))

/-- The based continuous map on smash products induced by a pair of based maps. -/
def smashMap {X X' Y Y' : BasedTop.{u}} (f : X ⟶ X') (g : Y ⟶ Y') :
    smashObj X Y ⟶ smashObj X' Y' :=
  _root_.CategoryTheory.Under.homMk
    (_root_.TopCat.ofHom ⟨smashMapFn f g, continuous_smashMapFn f g⟩) (by
      apply _root_.TopCat.Hom.ext
      ext z
      rcases z with ⟨⟩
      apply Quotient.sound
      right
      constructor
      · left
        exact BasedTop.map_point f
      · left
        rfl)

/-- Riehl's smash product bifunctor
`Top_* × Top_* ⟶ Top_*` (FC03-C04-U037). -/
def smashFunctor : (BasedTop.{u} × BasedTop.{u}) ⥤ BasedTop.{u} where
  obj XY := smashObj XY.1 XY.2
  map {XY X'Y'} fg := smashMap fg.1 fg.2
  map_id XY := by
    apply _root_.CategoryTheory.Under.UnderMorphism.ext
    apply _root_.TopCat.Hom.ext
    ext q
    refine Quotient.inductionOn q ?_
    intro p
    rfl
  map_comp {A B C} f g := by
    apply _root_.CategoryTheory.Under.UnderMorphism.ext
    apply _root_.TopCat.Hom.ext
    ext q
    refine Quotient.inductionOn q ?_
    intro p
    rfl

/-- Positive acceptance example: every point of the wedge is collapsed to the smash basepoint. -/
theorem smash_mk_eq_point_of_mem (X Y : BasedTop.{u}) {p : X.right × Y.right}
    (hp : p ∈ wedgeSet X Y) :
    Quotient.mk (smashSetoid X Y) p = smashPoint X Y := by
  apply Quotient.sound
  exact Or.inr ⟨hp, Or.inl rfl⟩

/-- Separating example: a point outside the wedge is not identified with a distinct point outside
it. This rules out quotient models that collapse more than `X ∨ Y`. -/
theorem smash_mk_ne_mk_of_not_mem (X Y : BasedTop.{u}) {p q : X.right × Y.right}
    (hp : p ∉ wedgeSet X Y) (hne : p ≠ q) :
    Quotient.mk (smashSetoid X Y) p ≠ Quotient.mk (smashSetoid X Y) q := by
  intro h
  have hr : (smashSetoid X Y).r p q := Quotient.exact h
  rcases hr with hpq | hw
  · exact hne hpq
  · exact hp hw.1

end LeanCategories.Topology
