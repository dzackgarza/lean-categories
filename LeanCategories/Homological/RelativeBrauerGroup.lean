/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BrauerGroup.RelativeBrauer

/-!
# Relative Brauer groups

Weibel, *An Introduction to Homological Algebra* (1994), Definition 6.6.11,
pp. 182--188 (FC05-C06-U075).

For an extension `L/K`, the relative Brauer group is the kernel of scalar
extension `Br(K) → Br(L)`.  Equivalently, its elements are the Brauer classes
of central simple `K`-algebras split by `L`.

The finite-Galois comparison `Br(L/K) ≅ H²(Gal(L/K), Lˣ)` is theorem-layer
content.  Its checked package owner is `RelativeBrGroup.isoSnd` in
`BrauerGroup.IsoSecond`.
-/

@[expose] public section

namespace LeanCategories.Homological

universe u

variable (K L : Type u) [Field K] [Field L] [Algebra K L]

/-- A central simple `K`-algebra splits over `L` when its scalar extension is a
matrix algebra over `L`. -/
abbrev CSASplitsOver (A : CSA K) : Prop :=
  isSplit K A L

/-- The relative Brauer group `Br(L/K)`, defined as the kernel of scalar
extension `Br(K) → Br(L)`. -/
noncomputable abbrev RelativeBrauerGroup : Subgroup (BrauerGroup K) :=
  RelativeBrGroup L K

/-- A Brauer class represented by `A` belongs to `Br(L/K)` exactly when `L`
splits `A`. -/
theorem mk_mem_relativeBrauerGroup_iff (A : CSA K) :
    (Quotient.mk'' A : BrauerGroup K) ∈ RelativeBrauerGroup K L ↔
      CSASplitsOver K L A :=
  mem_relativeBrGroup L K A

/-- Compatibility view of the relative Brauer group as its underlying set of
Brauer classes.  The group owner is `RelativeBrauerGroup`. -/
noncomputable abbrev relativeBrauerClasses : Set (BrauerGroup K) :=
  (RelativeBrauerGroup K L : Set (BrauerGroup K))

end LeanCategories.Homological
