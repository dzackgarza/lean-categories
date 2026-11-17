/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Lattices.Valued.CuspPlaneIncidence
public import LeanCategories.Lattices.Valued.CuspSchreierImage

/-! ## The flag fibre at a finite-index subgroup

`sec-descent-flags` of the descent page counts the flags `V ⊂ P` over a fixed discriminant datum by
the double cosets of `Γ` and of the stabilizer of the flag. `CuspPlaneIncidence` supplies the
incidence action of the plane stabilizer on the primitive isotropic lines inside the plane and the
correspondence `planeIncidentOrbitsEquivDoubleCoset`; what that module leaves to this one is the
finite-index count. Here:

* `planeFlagStabilizer P V = Stab(P) ⊓ Stab(V)` is the right flanker of the flag fibre;
* `planeLines_stabilizer_eq` identifies it with the stabilizer of the incident line
  `q : PlaneLines L P` in the incidence action, read inside `Stab(P)`: the flag stabilizer is the
  stabilizer of the actual flag, through `CuspPlaneIncidence`'s `PlaneLines.instMulAction`;
* `flagDoubleCoset Γ P V = Γ \ O(L) / (Stab(P) ⊓ Stab(V))`, with `finite_flagDoubleCoset` and
  `natCard_flagDoubleCoset_le_index : Nat.card ≤ Γ.index` for a finite-index `Γ`. It is the
  finite-index hypothesis, not a computation at a finite quotient, that bounds the flag fibre;
* the worked instance at `T_Co` (`finite_cobleFlagDoubleCoset`,
  `natCard_cobleFlagDoubleCoset_le_index`) uses the existing `cobleKernelSubgroup` and the Coble
  plane and line.

The source's reduction of the left flanker to `Γ ⊓ ρ⁻¹(F_{J,C})` needs the discriminant datum
`F_{J,C}` and its stabilizer, which belong to the discriminant-image work, not to this count. -/

@[expose] public section

open MulAction

namespace LeanCategories.Lattices.Valued

universe u

variable {R : Type u} [CommRing R] {L : IntegralLatticeCat R}

/-- The stabilizer of the flag `V ⊂ P` inside `O(L)`: the intersection of the plane and line
stabilizers. -/
noncomputable abbrev planeFlagStabilizer (P : PrimitiveIsotropic L 2) (V : PrimitiveIsotropic L 1) :
    Subgroup (OrthogonalGroup L) :=
  MulAction.stabilizer (OrthogonalGroup L) P ⊓ MulAction.stabilizer (OrthogonalGroup L) V

/-- **The stabilizer in the incidence action is the flag stabilizer.** -/
theorem planeLines_stabilizer_eq (P : PrimitiveIsotropic L 2) (q : PlaneLines L P) :
    MulAction.stabilizer (MulAction.stabilizer (OrthogonalGroup L) P) q =
      (planeFlagStabilizer P q.1).subgroupOf (MulAction.stabilizer (OrthogonalGroup L) P) := by
  ext g
  simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf, MulAction.mem_stabilizer_iff]
  constructor
  · intro h
    exact ⟨g.2, congrArg Subtype.val h⟩
  · rintro ⟨-, hV⟩
    exact Subtype.ext hV

/-- The double-coset space of the flag fibre: `Γ \ O(L) / (Stab(P) ⊓ Stab(V))`. -/
noncomputable abbrev flagDoubleCoset [IsDomain R] (Γ : FiniteIndexSubgroup L)
    (P : PrimitiveIsotropic L 2) (V : PrimitiveIsotropic L 1) : Type u :=
  DoubleCoset.Quotient (Γ.toSubgroup : Set (OrthogonalGroup L))
    (planeFlagStabilizer P V : Set (OrthogonalGroup L))

/-- **Finiteness of the flag fibre.** For a finite-index `Γ ≤ O(L)`, the double cosets
`Γ \ O(L) / (Stab(P) ⊓ Stab(V))` are finite: the flag fibres of the descent page's
`sec-descent-flags` are finite without computing anything at a finite quotient. -/
theorem finite_flagDoubleCoset [IsDomain R] (Γ : FiniteIndexSubgroup L)
    (P : PrimitiveIsotropic L 2) (V : PrimitiveIsotropic L 1) :
    Finite (flagDoubleCoset Γ P V) := by
  have := Γ.finiteIndex
  exact DoubleCoset.finite_quotient_of_finiteIndex _ Γ.toSubgroup

/-- **The index bound for the flag fibre.** -/
theorem natCard_flagDoubleCoset_le_index [IsDomain R] (Γ : FiniteIndexSubgroup L)
    (P : PrimitiveIsotropic L 2) (V : PrimitiveIsotropic L 1) :
    Nat.card (flagDoubleCoset Γ P V) ≤ Γ.toSubgroup.index := by
  have := Γ.finiteIndex
  exact DoubleCoset.natCard_quotient_le_index _ Γ.toSubgroup

/-- **The worked flag of `T_Co` is finite-index**: the flag double cosets of the stable orthogonal
group at the Coble plane and line. -/
theorem finite_cobleFlagDoubleCoset :
    Finite (flagDoubleCoset cobleKernelSubgroup coblePlane cobleLine) :=
  finite_flagDoubleCoset cobleKernelSubgroup coblePlane cobleLine

/-- **The worked flag count is bounded by the index** of the stable orthogonal group. -/
theorem natCard_cobleFlagDoubleCoset_le_index :
    Nat.card (flagDoubleCoset cobleKernelSubgroup coblePlane cobleLine) ≤
      cobleKernelSubgroup.toSubgroup.index :=
  natCard_flagDoubleCoset_le_index cobleKernelSubgroup coblePlane cobleLine


end LeanCategories.Lattices.Valued
