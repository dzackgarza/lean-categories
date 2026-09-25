/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Homological.SpectrumMappingCone
public import LeanCategories.Topology.CWQuotientData

/-!
# Raw Puppe-sequence data for a based pair

Definition-level realization of Hatcher FC07-C04-U080.

Hatcher first constructs the canonical mapping-cone sequence

`A → X → X ∪ CA → ΣA → ΣX → ...`.

For a CW pair he then replaces `X ∪ CA` by `X/A` using the quotient map,
which is a homotopy equivalence; the resulting connecting map
`X/A → ΣA` depends on a chosen homotopy inverse and is therefore only
defined up to homotopy.

Sweep III records the based pair, its canonical mapping cone, the exact
representative formula for the Puppe collapse, and the canonical collapse
`X ∪ CA → X/A`.  It does not prove quotient descent/continuity of the raw
collapse, the comparison is a homotopy equivalence, choose its homotopy
inverse, or prove naturality/homotopy-commutativity.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace LeanCategories.Homological

open LeanCategories.Topology

universe u

/-- The ambient space `X` with the chosen basepoint. -/
abbrev basedPairAmbientObj
    (X : Type u) [TopologicalSpace X] (x0 : X) : BasedTop.{u} :=
  Under.mk
    (TopCat.ofHom
      (⟨fun _ : PUnit => x0, continuous_const⟩ : C(PUnit, X)))

/-- The subspace `A ⊆ X` with the inherited basepoint. -/
abbrev basedPairSubspaceObj
    (X : Type u) [TopologicalSpace X] (A : Set X)
    (x0 : X) (hx0 : x0 ∈ A) : BasedTop.{u} :=
  Under.mk
    (TopCat.ofHom
      (⟨fun _ : PUnit => (⟨x0, hx0⟩ : A), continuous_const⟩ :
        C(PUnit, A)))

/-- The canonical based inclusion `A ↪ X`. -/
def basedPairInclusion
    (X : Type u) [TopologicalSpace X] (A : Set X)
    (x0 : X) (hx0 : x0 ∈ A) :
    basedPairSubspaceObj X A x0 hx0 ⟶ basedPairAmbientObj X x0 :=
  Under.homMk
    (TopCat.ofHom
      (⟨Subtype.val, continuous_subtype_val⟩ : C(A, X)))
    (by rfl)

/-- Exact representative specification for the canonical Puppe collapse
`X ∪_f CA → ΣA` of a based map `f : A → X`.

The target copy of `X` is collapsed to the suspension basepoint; a cone
representative `(t,a)` is sent to the same suspension representative. -/
def IsBasedMappingConeCollapseData
    {A X : BasedTop.{u}} (f : A ⟶ X)
    (collapse :
      (basedMappingCone f).right → Suspension A) : Prop :=
  (∀ x : X.right,
    collapse ((basedMappingConeInTarget f).right x) =
      suspensionPoint A) ∧
  ∀ p : unitInterval × A.right,
    collapse
        ((basedMappingConeInCone f).right
          (Quotient.mk (coneSetoid A) p)) =
      Quotient.mk (suspensionSetoid A) p

/-- The raw Puppe collapse selected from its source representative formula.
Descent and continuity are left to the result layer. -/
def basedMappingConeCollapseData
    {A X : BasedTop.{u}} (f : A ⟶ X) :
    (basedMappingCone f).right → Suspension A :=
  letI : Nonempty (Suspension A) := ⟨suspensionPoint A⟩
  Classical.epsilon (IsBasedMappingConeCollapseData f)

/-- Exact representative specification for the canonical comparison
`X ∪ CA → X/A` for a based pair.

The target summand maps by the quotient map and the whole cone maps to the
collapsed class. -/
def IsBasedPairConeToQuotientData
    (X : Type u) [TopologicalSpace X] (A : Set X)
    (x0 : X) (hx0 : x0 ∈ A)
    (q :
      (basedMappingCone (basedPairInclusion X A x0 hx0)).right →
        CWQuotient A) : Prop :=
  (∀ x : X,
    q ((basedMappingConeInTarget
      (basedPairInclusion X A x0 hx0)).right x) =
        cwQuotientMk A x) ∧
  ∀ p : unitInterval × A,
    q ((basedMappingConeInCone
      (basedPairInclusion X A x0 hx0)).right
        (Quotient.mk
          (coneSetoid (basedPairSubspaceObj X A x0 hx0)) p)) =
      cwQuotientMk A x0

/-- The canonical raw comparison `X ∪ CA → X/A`, selected from its
representative formula.  Its homotopy-equivalence property is not part of
Sweep III. -/
def basedPairConeToQuotientData
    (X : Type u) [TopologicalSpace X] (A : Set X)
    (x0 : X) (hx0 : x0 ∈ A) :
    (basedMappingCone (basedPairInclusion X A x0 hx0)).right →
      CWQuotient A :=
  letI : Nonempty (CWQuotient A) := ⟨cwQuotientMk A x0⟩
  Classical.epsilon
    (IsBasedPairConeToQuotientData X A x0 hx0)

/-- Proof-free data of the canonical beginning of Hatcher's Puppe sequence
for a based pair.

The quotient shorthand `X/A → ΣA` is intentionally not a field: Hatcher
defines it by choosing a homotopy inverse of `X ∪ CA → X/A`, a result-layer
choice. -/
structure BasedPairPuppeData
    (X : Type u) [TopologicalSpace X] (A : Set X)
    (x0 : X) (hx0 : x0 ∈ A) where
  subspace : BasedTop.{u}
  ambient : BasedTop.{u}
  inclusion : subspace ⟶ ambient
  cone : BasedTop.{u}
  inTarget : ambient ⟶ cone
  collapseToSuspension : cone.right → Suspension subspace
  suspendedInclusion : suspensionObj subspace ⟶ suspensionObj ambient
  coneToQuotient : cone.right → CWQuotient A

/-- The canonical raw Puppe data attached to the inclusion `A ↪ X`. -/
def basedPairPuppeData
    (X : Type u) [TopologicalSpace X] (A : Set X)
    (x0 : X) (hx0 : x0 ∈ A) :
    BasedPairPuppeData X A x0 hx0 where
  subspace := basedPairSubspaceObj X A x0 hx0
  ambient := basedPairAmbientObj X x0
  inclusion := basedPairInclusion X A x0 hx0
  cone := basedMappingCone (basedPairInclusion X A x0 hx0)
  inTarget := basedMappingConeInTarget
    (basedPairInclusion X A x0 hx0)
  collapseToSuspension := basedMappingConeCollapseData
    (basedPairInclusion X A x0 hx0)
  suspendedInclusion := suspensionMap
    (basedPairInclusion X A x0 hx0)
  coneToQuotient := basedPairConeToQuotientData X A x0 hx0

end LeanCategories.Homological
