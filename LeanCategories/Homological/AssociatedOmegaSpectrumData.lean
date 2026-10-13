/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Homological.CWPrespectrum
public import LeanCategories.Topology.MappingTelescopeData

/-!
# Hatcher's associated Ω-spectrum construction data

Definition-level realization of Hatcher FC07-C04-U140.

For a spectrum `K`, Hatcher forms at level `n` the mapping telescope

`Kₙ → ΩKₙ₊₁ → Ω²Kₙ₊₂ → ···`.

Strictly speaking the level of the associated spectrum is a CW approximation
to this telescope.  This file constructs the exact telescope from the already
owned prespectrum loop-adjoint maps, records the CW-approximation datum by its
source specification, and records the represented-cohomology carrier
`[X,K'ₙ]`.  The deletion-of-the-first-stage comparison, the natural map from
a telescope of loop spaces to the loop space of a telescope, the resulting
Ω-spectrum property, and the comparison of represented homology theories are
all result clauses and are deliberately absent from Sweep III.

For a suspension spectrum, the same stage system gives Hatcher's
`QX = ⋃ᵢ ΩⁱΣⁱX`; the literal-union comparison is likewise a later
topological statement, while the canonical direct-limit carrier is recorded
here.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace LeanCategories.Homological

open LeanCategories.Topology
open Set

universe u

/-- Stage `i` of Hatcher's level-`n` associated-spectrum sequence:
`ΩⁱKₙ₊ᵢ`. -/
abbrev associatedOmegaStage
    (K : CWPrespectrum.{u}) (n i : ℕ) : BasedTop.{u} :=
  spectrificationStage K.toPrespectrum n i

/-- The canonical transition
`ΩⁱKₙ₊ᵢ → Ωⁱ⁺¹Kₙ₊ᵢ₊₁`, obtained by iterating loops on the
adjoint of the spectrum structure map. -/
def associatedOmegaTransition
    (K : CWPrespectrum.{u}) (n i : ℕ) :
    associatedOmegaStage K n i ⟶ associatedOmegaStage K n (i + 1) :=
  spectrificationTransition K.toPrespectrum n i

/-- Hatcher's mapping telescope
`Tel(Kₙ → ΩKₙ₊₁ → Ω²Kₙ₊₂ → ···)`. -/
abbrev associatedOmegaTelescope
    (K : CWPrespectrum.{u}) (n : ℕ) : BasedTop.{u} :=
  basedMappingTelescope
    (fun i => associatedOmegaStage K n i)
    (fun i => associatedOmegaTransition K n i)

/-- The representative of `x ∈ ΩⁱKₙ₊ᵢ` in the bottom of the `i`th
cylinder of Hatcher's level-`n` telescope. -/
def associatedOmegaTelescopeStageMk
    (K : CWPrespectrum.{u}) (n i : ℕ)
    (x : (associatedOmegaStage K n i).right) :
    (associatedOmegaTelescope K n).right :=
  mappingTelescopeStageMk
    (fun j => associatedOmegaStage K n j)
    (fun j => associatedOmegaTransition K n j)
    i x

/-- Candidate data for a based CW approximation `Z → X`.

The source predicates asserting that `Z` is CW and the map is a weak
homotopy equivalence are kept separately so Sweep III does not prove the
CW-approximation theorem U024. -/
structure BasedCWApproximationCandidateData (X : BasedTop.{u}) where
  source : BasedTop.{u}
  map : source ⟶ X

instance (X : BasedTop.{u}) :
    Nonempty (BasedCWApproximationCandidateData X) :=
  ⟨⟨X, 𝟙 X⟩⟩

/-- Exact source specification for a based CW approximation. -/
def IsBasedCWApproximationData
    (X : BasedTop.{u})
    (A : BasedCWApproximationCandidateData X) : Prop :=
  Nonempty (Topology.CWComplex (Set.univ : Set A.source.right)) ∧
    IsWeakHomotopyEquivalence A.map.right.hom

/-- The CW-approximation datum used for Hatcher's `K'ₙ`, selected from the
exact U023/U024 source specification.

Existence of an approximation satisfying the specification is U024 and is not
proved in Sweep III. -/
def associatedOmegaCWApproximationData
    (K : CWPrespectrum.{u}) (n : ℕ) :
    BasedCWApproximationCandidateData (associatedOmegaTelescope K n) :=
  Classical.epsilon
    (IsBasedCWApproximationData (associatedOmegaTelescope K n))

/-- Hatcher's associated level `K'ₙ` at the construction-data layer. -/
abbrev associatedOmegaLevelData
    (K : CWPrespectrum.{u}) (n : ℕ) : BasedTop.{u} :=
  (associatedOmegaCWApproximationData K n).source

/-- The specified CW-approximation map `K'ₙ → Tel(ΩⁱKₙ₊ᵢ)`. -/
def associatedOmegaLevelToTelescopeData
    (K : CWPrespectrum.{u}) (n : ℕ) :
    associatedOmegaLevelData K n ⟶ associatedOmegaTelescope K n :=
  (associatedOmegaCWApproximationData K n).map

/-- Based homotopy of based maps, written as a raw relation so no
equivalence-relation theorem is needed in Sweep III. -/
def BasedMapHomotopicData
    {X Y : BasedTop.{u}} (f g : X ⟶ Y) : Prop :=
  ∃ H : C(unitInterval × X.right, Y.right),
    (∀ x, H (0, x) = f.right x) ∧
      (∀ x, H (1, x) = g.right x) ∧
        ∀ t, H (t, X.point) = Y.point

/-- Raw based homotopy classes `[X,Y]`.  The quotient uses the homotopy
relation directly; proving its equivalence properties is result-layer work. -/
abbrev BasedHomotopyClassData
    (X Y : BasedTop.{u}) :=
  Quot (fun f g : X ⟶ Y => BasedMapHomotopicData f g)

/-- Hatcher's represented cohomology carrier
`hⁿ(X) = [X,K'ₙ]` attached to the associated level. -/
abbrev associatedOmegaRepresentedCohomologyData
    (K : CWPrespectrum.{u}) (n : ℕ) (X : BasedTop.{u}) :=
  BasedHomotopyClassData X (associatedOmegaLevelData K n)

/-- Iterated reduced suspension `ΣⁿX`. -/
def iteratedSuspensionObjData
    (X : BasedTop.{u}) : ℕ → BasedTop.{u}
  | 0 => X
  | n + 1 => suspensionObj (iteratedSuspensionObjData X n)

/-- The suspension prespectrum of a based space. -/
def suspensionPrespectrumData
    (X : BasedTop.{u}) : Prespectrum.{u} where
  space := iteratedSuspensionObjData X
  structureMap := fun _ => 𝟙 _

/-- Stage `i` of Hatcher's stable-loop system for `QX`:
`ΩⁱΣⁱX`. -/
abbrev qStageData
    (X : BasedTop.{u}) (i : ℕ) : BasedTop.{u} :=
  spectrificationStage (suspensionPrespectrumData X) 0 i

/-- The canonical transition
`ΩⁱΣⁱX → Ωⁱ⁺¹Σⁱ⁺¹X`. -/
def qTransitionData
    (X : BasedTop.{u}) (i : ℕ) :
    qStageData X i ⟶ qStageData X (i + 1) :=
  spectrificationTransition (suspensionPrespectrumData X) 0 i

/-- The canonical sequential direct-limit carrier underlying Hatcher's
`QX = ⋃ᵢ ΩⁱΣⁱX`.

Identifying this categorical direct limit with Hatcher's literal nested union
uses the fact that the canonical transitions are inclusions and is left to the
result layer. -/
abbrev qSpaceData
    (X : BasedTop.{u}) : BasedTop.{u} :=
  spectrificationLevel (suspensionPrespectrumData X) 0

end LeanCategories.Homological
