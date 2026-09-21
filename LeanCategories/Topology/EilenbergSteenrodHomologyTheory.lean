/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import Mathlib.Algebra.DirectSum.Basic
public import Mathlib.Algebra.Exact.Basic
public import Mathlib.Topology.Basic
public import Mathlib.Topology.Homotopy.Basic

/-!
# Eilenberg–Steenrod homology-theory data

This file realizes the definition layer of Hatcher `FC07-C02-U075` via the
equivalent relative Eilenberg–Steenrod formulation used by the checked ATLAS
reference.  It deliberately packages the axioms as fields; it does not prove
that any particular homology construction satisfies them.
-/

open Set Topology

universe u

namespace LeanCategories.Topology.EilenbergSteenrod

/-- A topological pair `(X, A)`, represented by a space and a distinguished
subset. -/
structure HomologyPair where
  space : Type u
  instTop : TopologicalSpace space
  sub : Set space

attribute [instance] HomologyPair.instTop

/-- Regard a topological space as the pair `(X, ∅)`. -/
def HomologyPair.ofSpace (X : Type u) [TopologicalSpace X] : HomologyPair :=
  ⟨X, ‹_›, ∅⟩

/-- Regard the distinguished subspace of `(X, A)` as `(A, ∅)`. -/
def HomologyPair.subPair (P : HomologyPair) : HomologyPair :=
  HomologyPair.ofSpace P.sub

/-- The one-point pair used in the dimension axiom. -/
def HomologyPair.point : HomologyPair.{u} :=
  HomologyPair.ofSpace PUnit.{u + 1}

/-- The excised pair `(X ∖ U, A ∖ U)`. -/
def HomologyPair.excisePair (P : HomologyPair) (U : Set P.space) : HomologyPair where
  space := (Uᶜ : Set P.space)
  instTop := instTopologicalSpaceSubtype
  sub := Subtype.val ⁻¹' P.sub

/-- The disjoint-union pair `(∐ i, X i, ∅)`. -/
def HomologyPair.coproduct (ι : Type u) (X : ι → Type u)
    [∀ i, TopologicalSpace (X i)] : HomologyPair :=
  HomologyPair.ofSpace (Σ i, X i)

/-- A continuous map of pairs. -/
structure HomologyPairMap (P Q : HomologyPair) where
  toFun : P.space → Q.space
  continuous_toFun : Continuous toFun
  mapsTo : MapsTo toFun P.sub Q.sub

/-- Identity map of a topological pair. -/
def HomologyPairMap.id (P : HomologyPair) : HomologyPairMap P P where
  toFun := _root_.id
  continuous_toFun := continuous_id
  mapsTo := fun _ h ↦ h

/-- Composition of maps of topological pairs. -/
def HomologyPairMap.comp {P Q R : HomologyPair} (g : HomologyPairMap Q R)
    (f : HomologyPairMap P Q) : HomologyPairMap P R where
  toFun := g.toFun ∘ f.toFun
  continuous_toFun := g.continuous_toFun.comp f.continuous_toFun
  mapsTo := g.mapsTo.comp f.mapsTo

/-- Restrict a map of pairs to the distinguished subspaces. -/
def HomologyPairMap.restrictToSub {P Q : HomologyPair} (f : HomologyPairMap P Q) :
    HomologyPairMap P.subPair Q.subPair where
  toFun := fun a ↦ ⟨f.toFun a.val, f.mapsTo a.property⟩
  continuous_toFun := Continuous.subtype_mk (f.continuous_toFun.comp continuous_subtype_val) _
  mapsTo := fun _ h ↦ h.elim

/-- The inclusion `(A, ∅) ↪ (X, ∅)` associated to `(X, A)`. -/
def inclusionSubToSpace (P : HomologyPair) :
    HomologyPairMap P.subPair (HomologyPair.ofSpace P.space) where
  toFun := Subtype.val
  continuous_toFun := continuous_subtype_val
  mapsTo := fun _ h ↦ h.elim

/-- The canonical map `(X, ∅) → (X, A)`. -/
def inclusionSpaceToPair (P : HomologyPair) :
    HomologyPairMap (HomologyPair.ofSpace P.space) P where
  toFun := _root_.id
  continuous_toFun := continuous_id
  mapsTo := fun _ h ↦ h.elim

/-- The excision inclusion `(X ∖ U, A ∖ U) ↪ (X, A)`. -/
def excisionInclusion (P : HomologyPair) (U : Set P.space) :
    HomologyPairMap (P.excisePair U) P where
  toFun := Subtype.val
  continuous_toFun := continuous_subtype_val
  mapsTo := fun ⟨_, _⟩ hx ↦ hx

/-- Inclusion of one summand into a disjoint union. -/
def coproductInclusion (ι : Type u) (X : ι → Type u) [∀ j, TopologicalSpace (X j)]
    (i : ι) : HomologyPairMap (HomologyPair.ofSpace (X i)) (HomologyPair.coproduct ι X) where
  toFun := Sigma.mk i
  continuous_toFun := continuous_sigmaMk
  mapsTo := fun _ h ↦ h.elim

/-- A homotopy through maps of pairs. -/
structure HomologyPairHomotopy {P Q : HomologyPair}
    (f₀ f₁ : HomologyPairMap P Q) where
  toFun : P.space × unitInterval → Q.space
  continuous_toFun : Continuous toFun
  map_zero : ∀ x, toFun (x, ⟨0, unitInterval.zero_mem⟩) = f₀.toFun x
  map_one : ∀ x, toFun (x, ⟨1, unitInterval.one_mem⟩) = f₁.toFun x
  mapsTo : ∀ (a : P.space), a ∈ P.sub → ∀ t : unitInterval, toFun (a, t) ∈ Q.sub

/-- Two pair maps are homotopic when a homotopy through pair maps exists. -/
def HomologyPairMap.Homotopic {P Q : HomologyPair}
    (f₀ f₁ : HomologyPairMap P Q) : Prop :=
  Nonempty (HomologyPairHomotopy f₀ f₁)

/-- The usual closure/interior hypothesis for excision. -/
structure IsExcisiveTriple (P : HomologyPair) (U : Set P.space) : Prop where
  sub_mem : U ⊆ P.sub
  closure_sub_interior : closure U ⊆ interior P.sub

/-- A relative Eilenberg–Steenrod homology theory.

This is the checked ATLAS interface used as the reference port for Hatcher's
definition of a reduced homology theory (`FC07-C02-U075`).  The suspension and
wedge formulations in Hatcher are represented here by the standard equivalent
relative axioms: excision, pair exactness, dimension, and Milnor additivity. -/
structure HomologyTheory where
  H : ℤ → HomologyPair → Type u
  instAddCommGroup : ∀ (n : ℤ) (P : HomologyPair), AddCommGroup (H n P)
  map : ∀ (n : ℤ) {P Q : HomologyPair}, HomologyPairMap P Q → (H n P →+ H n Q)
  map_id : ∀ (n : ℤ) (P : HomologyPair),
    map n (HomologyPairMap.id P) = AddMonoidHom.id (H n P)
  map_comp : ∀ (n : ℤ) {P Q R : HomologyPair}
    (f : HomologyPairMap P Q) (g : HomologyPairMap Q R),
    map n (g.comp f) = (map n g).comp (map n f)
  boundary : ∀ (n : ℤ) (P : HomologyPair), H (n + 1) P →+ H n P.subPair
  boundary_natural : ∀ (n : ℤ) {P Q : HomologyPair} (f : HomologyPairMap P Q),
    (map n f.restrictToSub).comp (boundary n P) =
      (boundary n Q).comp (map (n + 1) f)
  homotopy_invariance : ∀ (n : ℤ) {P Q : HomologyPair}
    (f₀ f₁ : HomologyPairMap P Q), f₀.Homotopic f₁ → map n f₀ = map n f₁
  excision : ∀ (n : ℤ) (P : HomologyPair) (U : Set P.space),
    IsExcisiveTriple P U → Function.Bijective (map n (excisionInclusion P U))
  exact_at_sub : ∀ (n : ℤ) (P : HomologyPair),
    Function.Exact (boundary n P) (map n (inclusionSubToSpace P))
  exact_at_space : ∀ (n : ℤ) (P : HomologyPair),
    Function.Exact (map n (inclusionSubToSpace P)) (map n (inclusionSpaceToPair P))
  exact_at_pair : ∀ (n : ℤ) (P : HomologyPair),
    Function.Exact (map (n + 1) (inclusionSpaceToPair P)) (boundary n P)
  dimension : ∀ (n : ℤ), n ≠ 0 → Subsingleton (H n HomologyPair.point)
  coproduct : ∀ (n : ℤ) {ι : Type u} [DecidableEq ι] (X : ι → Type u)
    [∀ i, TopologicalSpace (X i)],
    Function.Bijective
      (DirectSum.toAddMonoid (β := fun i ↦ H n (HomologyPair.ofSpace (X i)))
        (fun i ↦ map n (coproductInclusion ι X i)))

attribute [instance] HomologyTheory.instAddCommGroup

/-- The coefficient group of a homology theory in degree `n` (`FC07-C02-U077`):
the value of the theory on a one-point space. -/
abbrev HomologyTheory.coefficients (h : HomologyTheory) (n : ℤ) : Type u :=
  h.H n HomologyPair.point

end LeanCategories.Topology.EilenbergSteenrod
