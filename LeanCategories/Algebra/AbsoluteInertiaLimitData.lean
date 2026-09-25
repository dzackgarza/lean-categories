/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Group.Subgroup.Basic

/-!
# Absolute inertia as a limit of finite inertia groups

Definition-level realization of Serre FC10-C13-U034.

Serre defines the inertia group of the maximal abelian extension by passage to
the limit from the finite case.  For a supplied family of finite Galois
quotients, the corresponding subgroup of the absolute abelian Galois group is
therefore the intersection of the pullbacks of the finite inertia subgroups.

Sweep III records that inverse-limit subgroup literally.  Identifying the
supplied finite quotients and inertia subgroups with the local-field objects,
or identifying the resulting subgroup with the kernel of an absolute
residue-degree map, is comparison/result content and is not proved here.
-/

@[expose] public noncomputable section

namespace LeanCategories.Algebra

universe u v w

/-- Serre's absolute abelian inertia subgroup, defined by passage to the limit
from the supplied finite inertia groups.

`projection i` is the restriction map from the absolute abelian Galois group
to a finite quotient, and `finiteInertia i` is that quotient's inertia
subgroup. -/
def absoluteAbelianInertiaLimitData
    {Index : Type u} {G : Type v} {FiniteGalois : Index → Type w}
    [CommGroup G] [∀ i, CommGroup (FiniteGalois i)]
    (projection : ∀ i, G →* FiniteGalois i)
    (finiteInertia : ∀ i, Subgroup (FiniteGalois i)) :
    Subgroup G :=
  ⨅ i, (finiteInertia i).comap (projection i)

end LeanCategories.Algebra
