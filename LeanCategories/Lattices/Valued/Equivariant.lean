/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Lattices.Valued.Involution
public import Mathlib.CategoryTheory.Action.Basic
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.RepresentationTheory.Invariants
public import Mathlib.RingTheory.SimpleModule.Isotypic

/-!
# Equivariant formed lattices

A `G`-lattice is a `G`-object in the lattice category. The carrier representation,
invariant lattice, coinvariant lattice, centralizer, and normalizer come from this one action.

The coinvariant lattice `L_G` is the orthogonal complement of the invariant lattice `L^G`
inside `L`, so it carries the restricted bilinear form. The module-theoretic quotient
`L / I_G L` of the representation is a different object: it can have torsion and the bilinear
form does not descend to it, so it is not a lattice.
-/

@[expose] public section

noncomputable section

open CategoryTheory
open LeanCategories.Modules.Bilinear.Valued

namespace LeanCategories.Lattices.Valued

universe u

variable (R G : Type u) [CommRing R] [Group G]

/-- Finite projective `G`-lattices as `G`-objects in the lattice category. -/
abbrev EquivariantLatticeCat := Action (FiniteProjectiveLatticeCat R R) G

namespace EquivariantLatticeCat

/-- The carrier representation of an equivariant lattice. -/
def carrierRepresentation (L : EquivariantLatticeCat R G) :
    Representation R G L.V.obj.obj.carrier where
  toFun g := BilinModuleCat.underlyingMap (L.ρ g).hom.hom
  map_one' := by
    ext x
    change BilinModuleCat.underlyingMap (L.ρ 1).hom.hom x = x
    rw [L.ρ.map_one]
    rfl
  map_mul' g h := by
    ext x
    change BilinModuleCat.underlyingMap (L.ρ (g * h)).hom.hom x =
      BilinModuleCat.underlyingMap (L.ρ g).hom.hom
        (BilinModuleCat.underlyingMap (L.ρ h).hom.hom x)
    rw [L.ρ.map_mul]
    rfl

/-- The invariant carrier of an equivariant lattice. -/
abbrev invariants (L : EquivariantLatticeCat R G) :=
  (carrierRepresentation R G L).invariants

/-- The coinvariant lattice `L_G`: the orthogonal complement of the invariant lattice. -/
def coinvariantLattice (L : EquivariantLatticeCat R G) :
    Submodule R L.V.obj.obj.carrier :=
  LinearMap.BilinForm.orthogonal L.V.obj.obj.asBilinForm (invariants R G L)

/-- A vector is coinvariant exactly when it pairs to zero against every invariant vector. -/
@[simp]
theorem mem_coinvariantLattice_iff (L : EquivariantLatticeCat R G)
    (x : L.V.obj.obj.carrier) :
    x ∈ coinvariantLattice R G L ↔
      ∀ y ∈ invariants R G L, L.V.obj.obj.pairing y x = 0 :=
  Iff.rfl

/-- The invariant lattice is saturated: a nonzero multiple of `x` is invariant only if `x` is. -/
theorem invariants_saturated (L : EquivariantLatticeCat R G)
    [NoZeroSMulDivisors R L.V.obj.obj.carrier] {r : R} {x : L.V.obj.obj.carrier}
    (hr : r ≠ 0) (hx : r • x ∈ invariants R G L) : x ∈ invariants R G L := by
  rw [Representation.mem_invariants] at hx ⊢
  intro g
  have h : r • carrierRepresentation R G L g x = r • x := by
    rw [← map_smul]
    exact hx g
  have hzero : r • (carrierRepresentation R G L g x - x) = 0 := by
    rw [smul_sub, h, sub_self]
  exact sub_eq_zero.mp ((eq_zero_or_eq_zero_of_smul_eq_zero hzero).resolve_left hr)

/-- The coinvariant lattice is saturated: a nonzero multiple of `x` is coinvariant only if
`x` is. -/
theorem coinvariantLattice_saturated [NoZeroDivisors R] (L : EquivariantLatticeCat R G)
    {r : R} {x : L.V.obj.obj.carrier} (hr : r ≠ 0)
    (hx : r • x ∈ coinvariantLattice R G L) : x ∈ coinvariantLattice R G L := by
  rw [mem_coinvariantLattice_iff] at hx ⊢
  intro y hy
  have h : r * L.V.obj.obj.pairing y x = 0 := by
    have := hx y hy
    rwa [BilinModuleCat.pairing_smul_right, smul_eq_mul] at this
  exact (mul_eq_zero.mp h).resolve_left hr

/-- An anisotropic invariant lattice meets the coinvariant lattice trivially. -/
theorem invariants_disjoint_coinvariantLattice (L : EquivariantLatticeCat R G)
    (haniso : ∀ x ∈ invariants R G L, L.V.obj.obj.pairing x x = 0 → x = 0) :
    Disjoint (invariants R G L) (coinvariantLattice R G L) := by
  rw [Submodule.disjoint_def]
  intro x hinv hcoin
  exact haniso x hinv ((mem_coinvariantLattice_iff R G L x).mp hcoin x hinv)

/-- The carrier of an equivariant lattice as a module over the group algebra. -/
abbrev groupAlgebraModule (L : EquivariantLatticeCat R G) : Type u :=
  (carrierRepresentation R G L).asModule

/-- The isotypic component of an equivariant lattice at a group-algebra module `S`. -/
def isotypicComponent (L : EquivariantLatticeCat R G) (S : Type u) [AddCommGroup S]
    [Module (MonoidAlgebra R G) S] :
    Submodule (MonoidAlgebra R G) (groupAlgebraModule R G L) :=
  _root_.isotypicComponent (MonoidAlgebra R G) (groupAlgebraModule R G L) S

/-- The isotypic component realized inside the lattice carrier. -/
def isotypicSubmodule (L : EquivariantLatticeCat R G) (S : Type u) [AddCommGroup S]
    [Module (MonoidAlgebra R G) S] :
    Submodule R L.V.obj.obj.carrier :=
  ((isotypicComponent R G L S).restrictScalars R).map
    (carrierRepresentation R G L).asModuleEquiv.toLinearMap

/-- The group action preserves every isotypic submodule. -/
theorem isotypicSubmodule_map_le (L : EquivariantLatticeCat R G) (S : Type u)
    [AddCommGroup S] [Module (MonoidAlgebra R G) S] (g : G) :
    (isotypicSubmodule R G L S).map (carrierRepresentation R G L g) ≤
      isotypicSubmodule R G L S := by
  rintro _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
  refine ⟨MonoidAlgebra.single g (1 : R) • y,
    (isotypicComponent R G L S).smul_mem _ hy, ?_⟩
  rw [LinearEquiv.coe_coe, Representation.asModuleEquiv_map_smul,
    Representation.asAlgebraHom_single]
  simp

/-- The formed-module isomorphism supplied by one element of the group action. -/
def formedIso (L : EquivariantLatticeCat R G) (g : G) :
    L.V.obj.obj ≅ L.V.obj.obj :=
  (ObjectProperty.ι (isLattice R R)).mapIso <|
    (ObjectProperty.ι (isFiniteProjectiveLattice R R)).mapIso (L.ρAut g)

/-- The group action as a homomorphism into the lattice orthogonal group. -/
def orthogonalRepresentation (L : EquivariantLatticeCat R G) :
    G →* OrthogonalGroup L.V.obj where
  toFun g :=
    ⟨BilinModuleCat.linearEquivOfIso (formedIso R G L g),
      BilinModuleCat.linearEquivOfIso_pairing (formedIso R G L g)⟩
  map_one' := by
    ext x
    change BilinModuleCat.underlyingMap (L.ρ 1).hom.hom x = x
    rw [L.ρ.map_one]
    rfl
  map_mul' g h := by
    ext x
    change BilinModuleCat.underlyingMap (L.ρ (g * h)).hom.hom x =
      BilinModuleCat.underlyingMap (L.ρ g).hom.hom
        (BilinModuleCat.underlyingMap (L.ρ h).hom.hom x)
    rw [L.ρ.map_mul]
    rfl

/-- The action preserves the pairing. -/
theorem pairing_carrierRepresentation (L : EquivariantLatticeCat R G) (g : G)
    (a b : L.V.obj.obj.carrier) :
    L.V.obj.obj.pairing (carrierRepresentation R G L g a)
        (carrierRepresentation R G L g b) =
      L.V.obj.obj.pairing a b :=
  (orthogonalRepresentation R G L g).property a b

/-- The order of the group carries `L` into the sum of its invariant and coinvariant
lattices.

The two sublattices are disjoint but need not span: `L` is an overlattice of
`L^G ⊕ L_G`, and this bounds the gluing by `|G|`. -/
theorem card_smul_mem_sup [Fintype G] (L : EquivariantLatticeCat R G)
    (x : L.V.obj.obj.carrier) :
    (Fintype.card G : R) • x ∈ invariants R G L ⊔ coinvariantLattice R G L := by
  classical
  set s : L.V.obj.obj.carrier := ∑ g : G, carrierRepresentation R G L g x with hs
  have hinv : s ∈ invariants R G L := by
    rw [Representation.mem_invariants]
    intro h
    rw [hs, map_sum]
    refine Fintype.sum_equiv (Equiv.mulLeft h) _ _ fun g => ?_
    simp [Equiv.coe_mulLeft, map_mul, Module.End.mul_apply]
  have hrest : (Fintype.card G : R) • x - s ∈ coinvariantLattice R G L := by
    rw [mem_coinvariantLattice_iff]
    intro y hy
    have hfix : ∀ g : G, carrierRepresentation R G L g y = y :=
      (Representation.mem_invariants _ _).mp hy
    have hstep : ∀ g : G,
        L.V.obj.obj.pairing y (carrierRepresentation R G L g x) =
          L.V.obj.obj.pairing y x := by
      intro g
      conv_lhs => rw [← hfix g]
      exact pairing_carrierRepresentation R G L g y x
    rw [← BilinModuleCat.bilinMap_apply, map_sub, map_smul, hs, map_sum]
    simp only [BilinModuleCat.bilinMap_apply, hstep]
    simp [Finset.sum_const, nsmul_eq_mul]
  have := Submodule.add_mem_sup hinv hrest
  simpa using this

/-- The subgroup of the orthogonal group generated by the given `G`-action. -/
def actionImage (L : EquivariantLatticeCat R G) :
    Subgroup (OrthogonalGroup L.V.obj) :=
  (orthogonalRepresentation R G L).range

/-- The centralizer of the `G`-action in the lattice orthogonal group. -/
def orthogonalCentralizer (L : EquivariantLatticeCat R G) :
    Subgroup (OrthogonalGroup L.V.obj) :=
  Subgroup.centralizer (actionImage R G L)

/-- The normalizer of the `G`-action in the lattice orthogonal group. -/
def orthogonalNormalizer (L : EquivariantLatticeCat R G) :
    Subgroup (OrthogonalGroup L.V.obj) :=
  Subgroup.normalizer (actionImage R G L)

/-- An element of order at most two in a group action gives the existing involution structure. -/
def involutionOfElement (L : EquivariantLatticeCat R G) (g : G)
    (hg : g * g = 1) : Involution L.V.obj where
  element := orthogonalRepresentation R G L g
  involutive := by
    rw [← (orthogonalRepresentation R G L).map_mul, hg,
      (orthogonalRepresentation R G L).map_one]

end EquivariantLatticeCat

end LeanCategories.Lattices.Valued
