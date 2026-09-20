/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.GroupTheory.Index
public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Field terminology attached to a formation indexing family

Definition-level realization of Serre FC10-C11-U003.

Once fields are indexed by a family `E ↦ G_E` of finite-index subgroups,
Serre reverses subgroup inclusion to define field extension, calls an
extension Galois when the relative subgroup is normal, identifies finite
composita with subgroup intersections, and transports fields by ambient
conjugation. The Galois group is the resulting quotient group.

The later assertion that every extension is contained in a Galois extension
is a result about finite-index subgroups and is deliberately not included.
-/

@[expose] public section

namespace LeanCategories.Homological

universe u v

variable {G : Type u} [Group G] {X : Type v}

/-- Serre's order-reversing field-extension relation: `E ⊆ F` exactly when
`G_F ≤ G_E` (FC10-C11-U003). -/
def IsFormationFieldExtension (G_E : X → Subgroup G) (E F : X) : Prop :=
  G_E F ≤ G_E E

/-- A formation extension `F/E` is Galois when `G_F` is normal in `G_E`.
The first conjunct records that `F/E` is an extension at all. -/
def IsFormationGaloisExtension (G_E : X → Subgroup G) (E F : X) : Prop :=
  IsFormationFieldExtension G_E E F ∧
    ((G_E F).subgroupOf (G_E E)).Normal

/-- Serre's Galois group `G(F/E) = G_E / G_F`, represented as a bundled
group once the defining relative-normality predicate is supplied. -/
noncomputable def formationGaloisGroup (G_E : X → Subgroup G) {E F : X}
    (h : IsFormationGaloisExtension G_E E F) : GrpCat := by
  letI : ((G_E F).subgroupOf (G_E E)).Normal := h.2
  exact GrpCat.of ((G_E E) ⧸ (G_E F).subgroupOf (G_E E))

/-- A field `F` is the compositum of a finite family `S` exactly when its
subgroup is the intersection of the corresponding subgroups. -/
def IsFormationCompositum (G_E : X → Subgroup G) (S : Set X) (F : X) : Prop :=
  S.Finite ∧ G_E F = sInf (G_E '' S)

/-- `sF` is the conjugate of the field `F` by `s` when its subgroup is the
ambient conjugate `s G_F s⁻¹`. -/
def IsFormationConjugateField (G_E : X → Subgroup G) (s : G) (F sF : X) : Prop :=
  G_E sF = (G_E F).map (MulAut.conj s).toMonoidHom

end LeanCategories.Homological
