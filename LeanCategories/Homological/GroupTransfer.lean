/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RepresentationTheory.FiniteIndex
public import Mathlib.RepresentationTheory.Homological.GroupHomology.Shapiro
public import Mathlib.RepresentationTheory.Homological.GroupHomology.Functoriality
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Shapiro
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality

/-!
# Transfer in group homology and cohomology

Weibel, *An Introduction to Homological Algebra* (1994), Construction 6.7.16,
§6.7, pp. 189--194 (FC05-C06-U096).

For a normal finite-index subgroup `S ≤ G`, finite index identifies induction
and coinduction.  The homological transfer is obtained from the unit
`A → Coind_S^G Res(A)`, the finite-index isomorphism `Coind ≅ Ind`, and
Shapiro's lemma.  Dually, the cohomological transfer uses inverse Shapiro
followed by the counit `Coind_S^G Res(A) → A`.

The degree-zero coset-sum/norm formula and the transfer-composite identities
are theorem-layer statements.
-/

@[expose] public noncomputable section

namespace LeanCategories.Homological

open CategoryTheory Rep

universe u

variable {k G : Type u} [CommRing k] [Group G]
variable (S : Subgroup G) [S.Normal] [S.FiniteIndex]
variable [DecidableRel (QuotientGroup.rightRel S)]

/-- The coefficient morphism used to define homological transfer:
`A → Coind_S^G Res(A) ≅ Ind_S^G Res(A)`. -/
def homologicalTransferRepresentationMap (A : Rep k G) :
    A ⟶ ind S.subtype (res S.subtype A) :=
  (resCoindAdjunction k S.subtype).unit.app A ≫
    (indCoindIso (res S.subtype A)).inv

/-- Weibel's homological transfer
`H_n(G;A) → H_n(S;Res_S^G A)` for a normal finite-index subgroup. -/
def groupHomologyTransfer [DecidableEq G] (A : Rep k G) (n : ℕ) :
    groupHomology A n ⟶ groupHomology (res S.subtype A) n :=
  groupHomology.map (MonoidHom.id G) (homologicalTransferRepresentationMap S A) n ≫
    (groupHomology.indIso S (res S.subtype A) n).hom

/-- The finite-index counit `Coind_S^G Res(A) → A` used for cohomological
transfer. -/
def cohomologicalTransferRepresentationMap (A : Rep k G) :
    coind S.subtype (res S.subtype A) ⟶ A :=
  (coindResAdjunction k S).counit.app A

/-- The same counit, with the definitionally trivial restriction along
`id_G` exposed in the form expected by cohomological functoriality. -/
def cohomologicalTransferRepresentationMapId (A : Rep k G) :
    res (MonoidHom.id G) (coind S.subtype (res S.subtype A)) ⟶ A := by
  simpa [res_id] using cohomologicalTransferRepresentationMap S A

/-- Weibel's cohomological transfer
`H^n(S;Res_S^G A) → H^n(G;A)` for a normal finite-index subgroup. -/
def groupCohomologyTransfer (A : Rep k G) (n : ℕ) :
    groupCohomology (res S.subtype A) n ⟶ groupCohomology A n :=
  (groupCohomology.coindIso (S := S) (res S.subtype A) n).inv ≫
    groupCohomology.map (MonoidHom.id G)
      (cohomologicalTransferRepresentationMapId S A) n

end LeanCategories.Homological
