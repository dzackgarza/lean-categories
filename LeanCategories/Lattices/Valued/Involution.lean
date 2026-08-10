/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Lattices.Valued.OrthogonalGroup
public import LeanCategories.Lattices.Valued.Sublattice
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

@[expose] public section

open CategoryTheory
open LeanCategories.Modules.Bilinear.Valued

namespace LeanCategories.Lattices.Valued

universe u

variable {R : Type u} [CommRing R]

/-- An element of `O(L)` with square one. -/
structure Involution (L : IntegralLatticeCat R) where
  element : OrthogonalGroup L
  involutive : element * element = 1

@[ext]
theorem Involution.ext {L : IntegralLatticeCat R} {J K : Involution L}
    (h : J.element = K.element) : J = K := by
  cases J
  cases K
  simp_all

/-- Conjugation of an involution by an orthogonal-group element. -/
def Involution.conjugate (L : IntegralLatticeCat R)
    (g : OrthogonalGroup L) (J : Involution L) : Involution L where
  element := g * J.element * g⁻¹
  involutive := by
    calc
      (g * J.element * g⁻¹) * (g * J.element * g⁻¹) =
          g * (J.element * J.element) * g⁻¹ := by group
      _ = 1 := by rw [J.involutive]; simp

@[simp]
theorem Involution.conjugate_one (L : IntegralLatticeCat R)
    (J : Involution L) : J.conjugate L 1 = J := by
  ext
  simp [Involution.conjugate]

theorem Involution.conjugate_mul (L : IntegralLatticeCat R)
    (g h : OrthogonalGroup L) (J : Involution L) :
    J.conjugate L (g * h) = (J.conjugate L h).conjugate L g := by
  ext
  simp only [Involution.conjugate]
  group

/-- The orthogonal group acts on involutions by conjugation. -/
instance involutionMulAction (L : IntegralLatticeCat R) :
    MulAction (OrthogonalGroup L) (Involution L) where
  smul g J := J.conjugate L g
  one_smul := Involution.conjugate_one L
  mul_smul := Involution.conjugate_mul L

@[simp]
theorem Involution.conjugate_apply (L : IntegralLatticeCat R)
    (g : OrthogonalGroup L) (J : Involution L) (x : L.obj.carrier) :
    (J.conjugate L g).element.1 x =
      g.1 (J.element.1 (g⁻¹.1 x)) :=
  rfl

@[simp]
theorem Involution.apply_apply (L : IntegralLatticeCat R) (J : Involution L)
    (x : L.obj.carrier) : J.element.1 (J.element.1 x) = x :=
  congrArg (fun g : OrthogonalGroup L ↦ g.1 x) J.involutive

/-- The fixed submodule of an involution. -/
def fixedSubmodule (L : IntegralLatticeCat R) (J : Involution L) :
    Submodule R L.obj.carrier :=
  LinearMap.ker (J.element.1.toLinearMap - LinearMap.id)

@[simp]
theorem mem_fixedSubmodule_iff (L : IntegralLatticeCat R)
    (J : Involution L) (x : L.obj.carrier) :
    x ∈ fixedSubmodule L J ↔ J.element.1 x = x := by
  rw [fixedSubmodule, LinearMap.mem_ker]
  exact sub_eq_zero

/-- Conjugation carries the invariant carrier to the invariant carrier. -/
theorem fixedSubmodule_smul (L : IntegralLatticeCat R)
    (g : OrthogonalGroup L) (J : Involution L) :
    fixedSubmodule L (g • J) = g • fixedSubmodule L J := by
  ext x
  constructor
  · intro hx
    rw [mem_fixedSubmodule_iff] at hx
    change (J.conjugate L g).element.1 x = x at hx
    refine ⟨g⁻¹.1 x, ?_, by simp⟩
    apply (mem_fixedSubmodule_iff L J _).mpr
    apply g.1.injective
    calc
      g.1 (J.element.1 (g⁻¹.1 x)) = x := hx
      _ = g.1 (g⁻¹.1 x) := by simp
  · rintro ⟨y, hy, rfl⟩
    have hy' := (mem_fixedSubmodule_iff L J y).mp hy
    apply (mem_fixedSubmodule_iff L (g • J) _).mpr
    change (J.conjugate L g).element.1 (g.1 y) = g.1 y
    calc
      (J.conjugate L g).element.1 (g.1 y) =
          g.1 (J.element.1 y) := by
        rw [Involution.conjugate_apply]
        congr 2
        exact inv_smul_smul g y
      _ = g.1 y := congrArg g.1 hy'

/-- The anti-fixed submodule of an involution. -/
def antiFixedSubmodule (L : IntegralLatticeCat R) (J : Involution L) :
    Submodule R L.obj.carrier :=
  LinearMap.ker (J.element.1.toLinearMap + LinearMap.id)

/-- The orthogonal complement of the invariant lattice carrier. -/
def coinvariantSubmodule (L : IntegralLatticeCat R) (J : Involution L) :
    Submodule R L.obj.carrier :=
  orthogonalSubmodule L (fixedSubmodule L J)

/-- Conjugation carries the coinvariant carrier to the coinvariant carrier. -/
theorem coinvariantSubmodule_smul (L : IntegralLatticeCat R)
    (g : OrthogonalGroup L) (J : Involution L) :
    coinvariantSubmodule L (g • J) = g • coinvariantSubmodule L J := by
  change orthogonalSubmodule L (fixedSubmodule L (g • J)) =
    g • orthogonalSubmodule L (fixedSubmodule L J)
  rw [fixedSubmodule_smul, ← smul_orthogonalSubmodule]

/-- Nondegeneracy makes each coinvariant vector anti-fixed. -/
theorem coinvariantSubmodule_le_antiFixedSubmodule
    (L : IntegralLatticeCat R) (J : Involution L)
    (hL : L.obj.IsNondegenerate) :
    coinvariantSubmodule L J ≤ antiFixedSubmodule L J := by
  intro x hx
  apply LinearMap.mem_ker.mpr
  change J.element.1 x + x = 0
  have hinj : Function.Injective L.obj.adjoint :=
    L.obj.isNondegenerate_iff_adjoint_injective.mp hL
  apply hinj
  ext z
  change L.obj.bilinMap (J.element.1 x + x) z = L.obj.bilinMap 0 z
  rw [LinearMap.BilinForm.add_left, LinearMap.BilinForm.zero_left]
  have hmove : L.obj.bilinMap (J.element.1 x) z =
      L.obj.bilinMap x (J.element.1 z) := by
    have h := J.element.property x (J.element.1 z)
    rw [J.apply_apply L z] at h
    exact h
  rw [hmove, ← LinearMap.BilinForm.add_right]
  have hfixed : J.element.1 z + z ∈ fixedSubmodule L J := by
    apply LinearMap.mem_ker.mpr
    change J.element.1 (J.element.1 z + z) - (J.element.1 z + z) = 0
    rw [map_add, J.apply_apply L]
    abel
  have horth := (mem_orthogonalSubmodule_iff L (fixedSubmodule L J) x).mp hx
    (J.element.1 z + z) hfixed
  rw [L.property.2] at horth
  exact horth

/-- Each anti-fixed vector is coinvariant away from characteristic two. -/
theorem antiFixedSubmodule_le_coinvariantSubmodule
    [IsDomain R] [NeZero (2 : R)]
    (L : IntegralLatticeCat R) (J : Involution L) :
    antiFixedSubmodule L J ≤ coinvariantSubmodule L J := by
  intro x hx
  change x ∈ orthogonalSubmodule L (fixedSubmodule L J)
  rw [mem_orthogonalSubmodule_iff]
  intro y hy
  have hx0 := LinearMap.mem_ker.mp hx
  have hy0 := LinearMap.mem_ker.mp hy
  change J.element.1 x + x = 0 at hx0
  change J.element.1 y - y = 0 at hy0
  have hx' : J.element.1 x = -x := eq_neg_of_add_eq_zero_left hx0
  have hy' : J.element.1 y = y := sub_eq_zero.mp hy0
  have hisom := J.element.property y x
  rw [hy', hx'] at hisom
  change L.obj.bilinMap y (-x) = L.obj.bilinMap y x at hisom
  rw [LinearMap.BilinForm.neg_right] at hisom
  have htwo : (2 : R) * L.obj.bilinMap y x = 0 := by
    linear_combination -hisom
  exact (mul_eq_zero.mp htwo).resolve_left (NeZero.ne 2)

/-- Away from characteristic two, nondegenerate coinvariant and anti-fixed vectors agree. -/
theorem coinvariantSubmodule_eq_antiFixedSubmodule
    [IsDomain R] [NeZero (2 : R)]
    (L : IntegralLatticeCat R) (J : Involution L)
    (hL : L.obj.IsNondegenerate) :
    coinvariantSubmodule L J = antiFixedSubmodule L J :=
  le_antisymm (coinvariantSubmodule_le_antiFixedSubmodule L J hL)
    (antiFixedSubmodule_le_coinvariantSubmodule L J)

/-- The fixed submodule is primitive. -/
theorem fixedSubmodule_isPrimitive (L : IntegralLatticeCat R)
    (J : Involution L) : IsPrimitiveSubmodule (fixedSubmodule L J) := by
  letI : Module.Projective R L.obj.carrier := L.property.1
  letI : Module.IsTorsionFree R L.obj.carrier := by infer_instance
  let f := J.element.1.toLinearMap - LinearMap.id
  let e := f.quotKerEquivRange
  exact Function.Injective.moduleIsTorsionFree e e.injective
    (fun r x ↦ e.map_smul r x)

/-- The anti-fixed submodule is primitive. -/
theorem antiFixedSubmodule_isPrimitive (L : IntegralLatticeCat R)
    (J : Involution L) : IsPrimitiveSubmodule (antiFixedSubmodule L J) := by
  letI : Module.Projective R L.obj.carrier := L.property.1
  letI : Module.IsTorsionFree R L.obj.carrier := by infer_instance
  let f := J.element.1.toLinearMap + LinearMap.id
  let e := f.quotKerEquivRange
  exact Function.Injective.moduleIsTorsionFree e e.injective
    (fun r x ↦ e.map_smul r x)

/-- A nondegenerate coinvariant submodule is primitive away from characteristic two. -/
theorem coinvariantSubmodule_isPrimitive
    [IsDomain R] [NeZero (2 : R)]
    (L : IntegralLatticeCat R) (J : Involution L)
    (hL : L.obj.IsNondegenerate) :
    IsPrimitiveSubmodule (coinvariantSubmodule L J) := by
  rw [coinvariantSubmodule_eq_antiFixedSubmodule L J hL]
  exact antiFixedSubmodule_isPrimitive L J

/-- The cyclic order-two representation determined by an involution. -/
noncomputable def Involution.cyclicActionHom (L : IntegralLatticeCat R)
    (J : Involution L) : Multiplicative (ZMod 2) →* OrthogonalGroup L := by
  let f : ℤ →+ Additive (OrthogonalGroup L) :=
    zmultiplesHom (Additive (OrthogonalGroup L)) (Additive.ofMul J.element)
  have hf : f 2 = 0 := by
    change Additive.ofMul (J.element ^ (2 : ℤ)) = 0
    rw [zpow_ofNat, pow_two, J.involutive]
    rfl
  exact AddMonoidHom.toMultiplicativeLeft (ZMod.lift 2 ⟨f, hf⟩)

@[simp]
theorem Involution.cyclicActionHom_generator (L : IntegralLatticeCat R)
    (J : Involution L) :
    J.cyclicActionHom L (Multiplicative.ofAdd (1 : ZMod 2)) = J.element := by
  change Additive.toMul ((ZMod.lift 2 _) ((1 : ℤ) : ZMod 2)) = J.element
  rw [ZMod.lift_coe]
  change J.element ^ (1 : ℤ) = J.element
  simp

/-- The cyclic order-two action on the lattice carrier. -/
@[reducible]
noncomputable def Involution.cyclicAction (L : IntegralLatticeCat R)
    (J : Involution L) : MulAction (Multiplicative (ZMod 2)) L.obj.carrier :=
  MulAction.compHom L.obj.carrier (J.cyclicActionHom L)

section PID

variable [IsDomain R] [IsPrincipalIdealRing R]

/-- The fixed submodule of a finite projective lattice is projective. -/
theorem fixedSubmodule_projective (L : IntegralLatticeCat R)
    [Module.Finite R L.obj.carrier] (J : Involution L) :
    Module.Projective R (fixedSubmodule L J) := by
  letI : Module.Projective R L.obj.carrier := L.property.1
  letI : Module.Free R L.obj.carrier := by infer_instance
  let b := Module.Free.chooseBasis R L.obj.carrier
  exact Module.Projective.of_basis ((fixedSubmodule L J).basisOfPid b).2

/-- The fixed vectors with their restricted form. -/
noncomputable def invariantLattice (L : IntegralLatticeCat R)
    [Module.Finite R L.obj.carrier] (J : Involution L) :
    IntegralLatticeCat R := by
  letI : Module.Projective R (fixedSubmodule L J) :=
    fixedSubmodule_projective L J
  exact formedSublattice L (fixedSubmodule L J)

/-- The inclusion of the invariant lattice. -/
noncomputable def invariantLatticeInclusion (L : IntegralLatticeCat R)
    [Module.Finite R L.obj.carrier] (J : Involution L) :
    invariantLattice L J ⟶ L := by
  letI : Module.Projective R (fixedSubmodule L J) :=
    fixedSubmodule_projective L J
  exact formedSublatticeInclusion L (fixedSubmodule L J)

/-- The invariant-lattice inclusion is a primitive formed embedding. -/
theorem invariantLatticeInclusion_isPrimitive
    (L : IntegralLatticeCat R) [Module.Finite R L.obj.carrier]
    (J : Involution L) :
    BilinModuleCat.IsPrimitiveEmbedding (invariantLatticeInclusion L J).hom := by
  constructor
  · exact Subtype.val_injective
  · change Module.IsTorsionFree R
      (L.obj.carrier ⧸ LinearMap.range (fixedSubmodule L J).subtype)
    rw [Submodule.range_subtype]
    exact fixedSubmodule_isPrimitive L J

/-- The coinvariant submodule of a finite projective lattice is projective. -/
theorem coinvariantSubmodule_projective (L : IntegralLatticeCat R)
    [Module.Finite R L.obj.carrier] (J : Involution L) :
    Module.Projective R (coinvariantSubmodule L J) := by
  letI : Module.Projective R L.obj.carrier := L.property.1
  letI : Module.Free R L.obj.carrier := by infer_instance
  let b := Module.Free.chooseBasis R L.obj.carrier
  exact Module.Projective.of_basis ((coinvariantSubmodule L J).basisOfPid b).2

/-- The coinvariant vectors with their restricted form. -/
noncomputable def coinvariantLattice (L : IntegralLatticeCat R)
    [Module.Finite R L.obj.carrier] (J : Involution L) :
    IntegralLatticeCat R := by
  letI : Module.Projective R (coinvariantSubmodule L J) :=
    coinvariantSubmodule_projective L J
  exact formedSublattice L (coinvariantSubmodule L J)

/-- The inclusion of the coinvariant lattice. -/
noncomputable def coinvariantLatticeInclusion (L : IntegralLatticeCat R)
    [Module.Finite R L.obj.carrier] (J : Involution L) :
    coinvariantLattice L J ⟶ L := by
  letI : Module.Projective R (coinvariantSubmodule L J) :=
    coinvariantSubmodule_projective L J
  exact formedSublatticeInclusion L (coinvariantSubmodule L J)

/-- A nondegenerate coinvariant inclusion is primitive away from characteristic two. -/
theorem coinvariantLatticeInclusion_isPrimitive [NeZero (2 : R)]
    (L : IntegralLatticeCat R) [Module.Finite R L.obj.carrier]
    (J : Involution L) (hL : L.obj.IsNondegenerate) :
    BilinModuleCat.IsPrimitiveEmbedding (coinvariantLatticeInclusion L J).hom := by
  constructor
  · exact Subtype.val_injective
  · change Module.IsTorsionFree R
      (L.obj.carrier ⧸ LinearMap.range (coinvariantSubmodule L J).subtype)
    rw [Submodule.range_subtype]
    exact coinvariantSubmodule_isPrimitive L J hL

end PID

end LeanCategories.Lattices.Valued
