/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Group.End
public import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
# Incidence geometry from subgroup conjugacy classes

The generic construction underlying Dummit--Foote FC01-C06-U024.  Given two
subgroups, use their conjugacy classes as points and lines, with incidence
meaning that the point subgroup normalizes the line subgroup.  The source's
order-168 theorem that the resulting geometry is the Fano plane belongs to the
theorem sweep.
-/

@[expose] public section

namespace LeanCategories.Algebra.SubgroupConjugacyIncidence

universe u

variable {G : Type u} [Group G]

/-- The conjugate of a subgroup by an element of the ambient group. -/
def conjugate (g : G) (H : Subgroup G) : Subgroup G :=
  H.map (MulAut.conj g).toMonoidHom

/-- A point in the normalizer-incidence geometry determined by `U`: a chosen
conjugate of `U`. -/
structure Point (U : Subgroup G) where
  subgroup : Subgroup G
  isConjugate : ∃ g : G, subgroup = conjugate g U

/-- A line in the normalizer-incidence geometry determined by `W`: a chosen
conjugate of `W`. -/
structure Line (W : Subgroup G) where
  subgroup : Subgroup G
  isConjugate : ∃ g : G, subgroup = conjugate g W

/-- Incidence is normalization: a point `U'` lies on a line `W'` precisely
when `U'` normalizes `W'`. -/
def Incident {U W : Subgroup G} (p : Point U) (l : Line W) : Prop :=
  p.subgroup ≤ Subgroup.normalizer l.subgroup

end LeanCategories.Algebra.SubgroupConjugacyIncidence
