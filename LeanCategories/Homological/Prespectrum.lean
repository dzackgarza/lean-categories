/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Homological.Spectrum
public import Mathlib.Topology.CWComplex.Classical.Basic

/-!
# Prespectra

Weibel, *An Introduction to Homological Algebra*, Definition 10.9.5, p. 409
(FC05-C10-U104).

A prespectrum is a sequence of based spaces together with based structure maps
`S Dₙ ⟶ Dₙ₊₁`.  We use the reduced suspension model
`(I × X)/(∂I × X ∪ I × {x₀})`, so a map out of the suspension is exactly the uncurried form of a
based map `X ⟶ ΩY`.  Functions of prespectra are levelwise based maps strictly compatible with
the structure maps.  The definition also records Weibel's CW condition: level spaces are CW
complexes and the structure maps are cellular inclusions.
-/

@[expose] public section

noncomputable section

open CategoryTheory

namespace LeanCategories.Homological

open LeanCategories.Topology
open Set

universe u

/-- The collapsed subset in the reduced suspension model: both ends of the cylinder and the
basepoint line.

Source: Weibel, Definition 10.9.5 (FC05-C10-U104), using the standard reduced suspension model. -/
def suspensionCollapsed (X : BasedTop.{u}) : Set (unitInterval × X.right) :=
  {p | p.1 = 0 ∨ p.1 = 1 ∨ p.2 = X.point}

/-- The equivalence relation defining the reduced suspension of a based space. -/
def suspensionSetoid (X : BasedTop.{u}) : Setoid (unitInterval × X.right) where
  r p q := p = q ∨ (p ∈ suspensionCollapsed X ∧ q ∈ suspensionCollapsed X)
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

/-- The reduced suspension of a based space as a quotient topological space. -/
abbrev Suspension (X : BasedTop.{u}) := Quotient (suspensionSetoid X)

/-- The basepoint of the reduced suspension. -/
def suspensionPoint (X : BasedTop.{u}) : Suspension X :=
  Quotient.mk (suspensionSetoid X) (0, X.point)

/-- The reduced suspension as a based topological space. -/
abbrev suspensionObj (X : BasedTop.{u}) : BasedTop.{u} :=
  Under.mk (TopCat.ofHom ⟨fun _ : PUnit => suspensionPoint X, continuous_const⟩)

/-- A based map carries the collapsed subset of a suspension cylinder into the collapsed
subset. -/
theorem suspensionMap_mem_collapsed {X Y : BasedTop.{u}} (f : X ⟶ Y)
    {p : unitInterval × X.right} (hp : p ∈ suspensionCollapsed X) :
    (p.1, f.right p.2) ∈ suspensionCollapsed Y := by
  rcases hp with h0 | h1 | hx
  · exact Or.inl h0
  · exact Or.inr (Or.inl h1)
  · exact Or.inr (Or.inr (by rw [hx]; exact BasedTop.map_point f))

/-- The map of reduced suspensions induced by a based map. -/
def suspensionMapFn {X Y : BasedTop.{u}} (f : X ⟶ Y) : Suspension X → Suspension Y :=
  Quotient.lift
    (fun p => Quotient.mk (suspensionSetoid Y) (p.1, f.right p.2))
    (by
      intro p q h
      apply Quotient.sound
      rcases h with rfl | ⟨hp, hq⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨suspensionMap_mem_collapsed f hp, suspensionMap_mem_collapsed f hq⟩)

/-- The induced suspension map is continuous. -/
theorem continuous_suspensionMapFn {X Y : BasedTop.{u}} (f : X ⟶ Y) :
    Continuous (suspensionMapFn f) := by
  exact (continuous_quotient_mk'.comp
    (Continuous.prodMk continuous_fst (f.right.hom.continuous_toFun.comp continuous_snd))).quotient_lift
    (by
      intro p q h
      apply Quotient.sound
      rcases h with rfl | ⟨hp, hq⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨suspensionMap_mem_collapsed f hp, suspensionMap_mem_collapsed f hq⟩)

/-- The based map on suspensions induced by a based map. -/
def suspensionMap {X Y : BasedTop.{u}} (f : X ⟶ Y) : suspensionObj X ⟶ suspensionObj Y :=
  Under.homMk
    (TopCat.ofHom ⟨suspensionMapFn f, continuous_suspensionMapFn f⟩)
    (by
      apply TopCat.Hom.ext
      ext z
      rcases z with ⟨⟩
      apply Quotient.sound
      right
      constructor
      · exact Or.inl rfl
      · exact Or.inl rfl)

/-- Evaluation of a based loop family is constant on suspension equivalence classes. -/
theorem suspensionAdjoint_rel {X Y : BasedTop.{u}}
    (φ : X.right → Path Y.point Y.point) (hφpoint : φ X.point = Path.refl Y.point)
    {p q : unitInterval × X.right} (h : suspensionSetoid X p q) :
    φ p.2 p.1 = φ q.2 q.1 := by
  rcases h with rfl | ⟨hp, hq⟩
  · rfl
  · have collapse_value : ∀ z : unitInterval × X.right,
        z ∈ suspensionCollapsed X → φ z.2 z.1 = Y.point := by
      intro z hz
      rcases hz with h0 | h1 | hx
      · rw [h0]
        exact (φ z.2).source
      · rw [h1]
        exact (φ z.2).target
      · rw [hx, hφpoint]
        rfl
    rw [collapse_value p hp, collapse_value q hq]

/-- The underlying suspension-adjoint map obtained by evaluating a continuous based loop family. -/
def suspensionAdjointFn {X Y : BasedTop.{u}}
    (φ : X.right → Path Y.point Y.point) (hφpoint : φ X.point = Path.refl Y.point) :
    Suspension X → Y.right :=
  Quotient.lift (fun p : unitInterval × X.right => φ p.2 p.1)
    (fun _ _ h => suspensionAdjoint_rel φ hφpoint h)

/-- Continuity of the suspension-adjoint map. -/
theorem continuous_suspensionAdjointFn {X Y : BasedTop.{u}}
    (φ : X.right → Path Y.point Y.point) (hφ : Continuous φ)
    (hφpoint : φ X.point = Path.refl Y.point) : Continuous (suspensionAdjointFn φ hφpoint) := by
  exact ((Path.continuous_uncurry_iff.mpr hφ).comp
    (Continuous.prodMk continuous_snd continuous_fst)).quotient_lift
      (fun _ _ h => suspensionAdjoint_rel φ hφpoint h)

/-- A based map `X ⟶ ΩY` determines a based map `SX ⟶ Y` by evaluation.  This is the direction of
the suspension-loop adjunction used in Weibel's equivalent formulation of a prespectrum.

Source: Weibel, Definition 10.9.5 (FC05-C10-U104). -/
def suspensionAdjoint {X Y : BasedTop.{u}}
    (φ : X.right → Path Y.point Y.point) (hφ : Continuous φ)
    (hφpoint : φ X.point = Path.refl Y.point) : suspensionObj X ⟶ Y :=
  Under.homMk
    (TopCat.ofHom ⟨suspensionAdjointFn φ hφpoint,
      continuous_suspensionAdjointFn φ hφ hφpoint⟩)
    (by
      apply TopCat.Hom.ext
      ext z
      rcases z with ⟨⟩
      change φ X.point 0 = Y.point
      rw [hφpoint]
      rfl)


/-- Naturality of the suspension-loop adjunction in both variables. -/
theorem suspensionAdjoint_naturality {X X' Y Y' : BasedTop.{u}}
    (f : X ⟶ X') (g : Y ⟶ Y')
    (φ : X.right → Path Y.point Y.point) (hφ : Continuous φ)
    (hφpoint : φ X.point = Path.refl Y.point)
    (ψ : X'.right → Path Y'.point Y'.point) (hψ : Continuous ψ)
    (hψpoint : ψ X'.point = Path.refl Y'.point)
    (h : ∀ (x : X.right) (t : unitInterval), g.right (φ x t) = ψ (f.right x) t) :
    suspensionMap f ≫ suspensionAdjoint ψ hψ hψpoint =
      suspensionAdjoint φ hφ hφpoint ≫ g := by
  apply Under.UnderMorphism.ext
  apply TopCat.ext
  intro q
  change Suspension X at q
  refine Quotient.inductionOn q ?_
  intro p
  rw [Under.comp_right, Under.comp_right, ConcreteCategory.comp_apply, ConcreteCategory.comp_apply]
  simpa [suspensionMap, suspensionMapFn, suspensionAdjoint, suspensionAdjointFn] using (h p.2 p.1).symm

/-- A prespectrum is a sequence of based spaces with based suspension structure maps.

Source: Weibel, Definition 10.9.5, p. 409 (FC05-C10-U104). -/
structure Prespectrum where
  space : ℕ → BasedTop.{u}
  structureMap : ∀ n : ℕ, suspensionObj (space n) ⟶ space (n + 1)

namespace Prespectrum

/-- A function of prespectra is a levelwise based map strictly compatible with structure maps.

Source: Weibel, Definition 10.9.5, p. 409 (FC05-C10-U104). -/
@[ext]
structure Hom (D E : Prespectrum.{u}) where
  app : ∀ n : ℕ, D.space n ⟶ E.space n
  comm : ∀ n : ℕ,
    suspensionMap (app n) ≫ E.structureMap n = D.structureMap n ≫ app (n + 1) := by cat_disch

@[simp]
theorem suspensionMap_id (X : BasedTop.{u}) : suspensionMap (𝟙 X) = 𝟙 (suspensionObj X) := by
  apply Under.UnderMorphism.ext
  apply TopCat.Hom.ext
  ext q
  refine Quotient.inductionOn q ?_
  intro p
  rfl

@[simp]
theorem suspensionMap_comp {X Y Z : BasedTop.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    suspensionMap (f ≫ g) = suspensionMap f ≫ suspensionMap g := by
  apply Under.UnderMorphism.ext
  apply TopCat.Hom.ext
  ext q
  refine Quotient.inductionOn q ?_
  intro p
  rfl

instance : Category Prespectrum.{u} where
  Hom := Hom
  id D :=
    { app := fun _ => 𝟙 _
      comm := by simp }
  comp := fun {D E F} f g =>
    { app := fun n => f.app n ≫ g.app n
      comm := by
        intro n
        rw [suspensionMap_comp, Category.assoc, g.comm, ← Category.assoc, f.comm,
          Category.assoc] }
  id_comp := by
    intro D E f
    apply Hom.ext
    funext n
    simp
  comp_id := by
    intro D E f
    apply Hom.ext
    funext n
    simp
  assoc := by
    intro D E F G f g h
    apply Hom.ext
    funext n
    simp

/-- A spectrum determines a prespectrum by adjointing its structural homeomorphisms
`Eₙ ≅ ΩEₙ₊₁` to maps `S Eₙ ⟶ Eₙ₊₁`.

Source: Weibel, Definition 10.9.5, p. 409 (FC05-C10-U104). -/
noncomputable def ofSpectrumObj (E : Spectrum.{u}) : Prespectrum.{u} where
  space := E.space
  structureMap n := suspensionAdjoint
    (E.loopHomeomorph n) (E.loopHomeomorph n).continuous (E.loopHomeomorph_point n)

/-- The forgetful functor from spectra to prespectra.

Source: Weibel, Definition 10.9.5, p. 409 (FC05-C10-U104). -/
noncomputable def forgetSpectrum : Spectrum.{u} ⥤ Prespectrum.{u} where
  obj := ofSpectrumObj
  map := fun {E F} f =>
    { app := f.app
      comm := by
        intro n
        exact suspensionAdjoint_naturality (f.app n) (f.app (n + 1))
          (E.loopHomeomorph n) (E.loopHomeomorph n).continuous (E.loopHomeomorph_point n)
          (F.loopHomeomorph n) (F.loopHomeomorph n).continuous (F.loopHomeomorph_point n)
          (f.comm n) }
  map_id E := by
    apply Prespectrum.Hom.ext
    funext n
    rfl
  map_comp f g := by
    apply Prespectrum.Hom.ext
    funext n
    rfl

/-- A map between CW complexes is *cellular* when it preserves every skeleton.  A cellular
inclusion is a cellular map which is a topological embedding. -/
def IsCellularInclusion {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    [T2Space X] [T2Space Y] [Topology.CWComplex (Set.univ : Set X)] [Topology.CWComplex (Set.univ : Set Y)]
    (f : X → Y) : Prop :=
  Topology.IsEmbedding f ∧ ∀ n : ℕ∞,
    MapsTo f (Topology.CWComplex.skeleton (Set.univ : Set X) n)
      (Topology.CWComplex.skeleton (Set.univ : Set Y) n)

/-- Chosen CW structures witnessing that a prespectrum is a CW prespectrum.  The suspension
CW structures are recorded because cellularity is relative to chosen CW structures.

Source: Weibel, Definition 10.9.5, p. 409 (FC05-C10-U104). -/
structure CWStructure (D : Prespectrum.{u}) where
  t2Space : ∀ n, T2Space (D.space n).right
  cwSpace : ∀ n, Topology.CWComplex (Set.univ : Set (D.space n).right)
  t2Suspension : ∀ n, T2Space (suspensionObj (D.space n)).right
  cwSuspension : ∀ n, Topology.CWComplex (Set.univ : Set (suspensionObj (D.space n)).right)
  structureMap_cellular_inclusion : ∀ n, @IsCellularInclusion
    (suspensionObj (D.space n)).right (D.space (n + 1)).right _ _
    (t2Suspension n) (t2Space (n + 1)) (cwSuspension n) (cwSpace (n + 1))
    (D.structureMap n).right

/-- A prespectrum is a CW prespectrum when its level spaces admit CW structures for which every
structure map is a cellular inclusion.

Source: Weibel, Definition 10.9.5, p. 409 (FC05-C10-U104). -/
def IsCW (D : Prespectrum.{u}) : Prop := Nonempty (CWStructure D)

end Prespectrum

end LeanCategories.Homological
