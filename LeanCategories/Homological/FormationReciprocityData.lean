/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Homological.FormationFieldData
public import Mathlib.GroupTheory.Abelianization.Defs

/-!
# Raw finite-reciprocity carriers for class formations

Definition-level realization of the carrier/notation part of Serre,
*Local Fields*, Chapter XI, `FC10-C11-U013`.

For a Galois formation extension `F/E`, Serre writes `G(F/E)^a` for the
abelianization and identifies it, by the class-formation reciprocity theorem,
with a quotient of the fixed coefficient group by a norm subgroup.  Sweep III
records the two quotient carriers only.  The reciprocity isomorphism is result
content.
-/

@[expose] public section

noncomputable section

namespace LeanCategories.Homological

universe u v w

variable {G : Type u} [Group G] {X : Type v}

/-- Serre's `G(F/E)^a`: the abelianization of the formation Galois group. -/
abbrev formationAbelianizedGaloisGroup
    (G_E : X → Subgroup G) {E F : X}
    (h : IsFormationGaloisExtension G_E E F) :=
  Abelianization (formationGaloisGroup G_E h)

/-- Raw carrier for a norm quotient `A_E / N A_F`.

The caller supplies the base coefficient group and its norm subgroup; the
theorem identifying this quotient with `G(F/E)^a` is not constructor data. -/
abbrev formationNormQuotientData
    (A_E : Type w) [CommGroup A_E] (N : Subgroup A_E) :=
  A_E ⧸ N

/-- Characterization of Serre's finite reciprocity map as the inverse of the
class-formation map `theta`.

The two equations are result content: this predicate states them but does not
prove them for the selected map. -/
def IsFormationReciprocityInverseData
    {GAb NormQuotient : Type*}
    (theta : GAb → NormQuotient)
    (reciprocity : NormQuotient → GAb) : Prop :=
  Function.LeftInverse reciprocity theta ∧
    Function.RightInverse reciprocity theta

/-- Source-faithful finite reciprocity data: a candidate inverse function
together with Serre's exact two-sided-inverse characterization.

Existence, uniqueness, homomorphism and isomorphism packaging are supplied by
the finite reciprocity theorem, not hidden in a choice. -/
abbrev FormationReciprocityInverseData
    {GAb NormQuotient : Type*}
    (theta : GAb → NormQuotient) :=
  {reciprocity : NormQuotient → GAb //
    IsFormationReciprocityInverseData theta reciprocity}

/-- Serre's norm-residue/reciprocity symbol `{a,F/E}` relative to the supplied
finite class-formation map `theta`: apply its selected inverse to the norm
class of `a`. -/
def formationReciprocitySymbolData
    {GAb NormQuotient : Type*}
    (theta : GAb → NormQuotient)
    (D : FormationReciprocityInverseData theta)
    (a : NormQuotient) : GAb :=
  D.1 a

end LeanCategories.Homological
