/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Lattices.Valued.Spinor
public import Mathlib.LinearAlgebra.CliffordAlgebra.SpinGroup

@[expose] public section

open CliffordAlgebra
open LeanCategories.Modules.Bilinear.Valued

namespace LeanCategories.Lattices.Valued

universe u

variable {K : Type u} [Field K]

/-- The quadratic form `x ↦ b(x,x)` of a finite symmetric form. -/
noncomputable def finiteFormQuadratic (L : FiniteFormCat K K) :
    QuadraticForm K L.obj.carrier :=
  LinearMap.BilinMap.toQuadraticMap L.obj.bilinMap

@[simp]
theorem finiteFormQuadratic_apply (L : FiniteFormCat K K) (x : L.obj.carrier) :
    finiteFormQuadratic L x = L.obj.pairing x x :=
  rfl

/-- The polar form of `finiteFormQuadratic` is twice the pairing. -/
theorem polar_finiteFormQuadratic (L : FiniteFormCat K K) (x y : L.obj.carrier) :
    QuadraticMap.polar (finiteFormQuadratic L) x y = 2 * L.obj.pairing x y := by
  rw [finiteFormQuadratic, LinearMap.BilinMap.polar_toQuadraticMap,
    BilinModuleCat.bilinMap_apply, BilinModuleCat.bilinMap_apply, L.property.2 y x]
  ring

/-- The Clifford algebra of a finite symmetric form. -/
abbrev FiniteFormClifford (L : FiniteFormCat K K) :=
  CliffordAlgebra (finiteFormQuadratic L)

/-- A vector of nonzero square, as a unit of the Clifford algebra.

Its inverse is `v / b(v,v)`, the standard formula for the inverse of a vector
[@Cas08a, Chapter 10, §3]. -/
noncomputable def cliffordVectorUnit (L : FiniteFormCat K K)
    (v : L.obj.carrier) (hv : L.obj.pairing v v ≠ 0) : (FiniteFormClifford L)ˣ where
  val := ι (finiteFormQuadratic L) v
  inv := ι (finiteFormQuadratic L) ((L.obj.pairing v v)⁻¹ • v)
  val_inv := by
    rw [map_smul, mul_smul_comm, ι_sq_scalar, finiteFormQuadratic_apply,
      Algebra.smul_def, ← map_mul, inv_mul_cancel₀ hv, map_one]
  inv_val := by
    rw [map_smul, smul_mul_assoc, ι_sq_scalar, finiteFormQuadratic_apply,
      Algebra.smul_def, ← map_mul, inv_mul_cancel₀ hv, map_one]

@[simp]
theorem cliffordVectorUnit_val (L : FiniteFormCat K K)
    (v : L.obj.carrier) (hv : L.obj.pairing v v ≠ 0) :
    (cliffordVectorUnit L v hv : FiniteFormClifford L) = ι (finiteFormQuadratic L) v :=
  rfl

@[simp]
theorem cliffordVectorUnit_inv_val (L : FiniteFormCat K K)
    (v : L.obj.carrier) (hv : L.obj.pairing v v ≠ 0) :
    (((cliffordVectorUnit L v hv)⁻¹ : (FiniteFormClifford L)ˣ) : FiniteFormClifford L) =
      ι (finiteFormQuadratic L) ((L.obj.pairing v v)⁻¹ • v) :=
  rfl

/-- Vectors of nonzero square lie in the Lipschitz group. -/
theorem cliffordVectorUnit_mem_lipschitzGroup (L : FiniteFormCat K K)
    (v : L.obj.carrier) (hv : L.obj.pairing v v ≠ 0) :
    cliffordVectorUnit L v hv ∈ lipschitzGroup (finiteFormQuadratic L) :=
  Subgroup.subset_closure ⟨v, rfl⟩

/-- The Clifford norm `g ↦ g * reverse g`.

On the Lipschitz group this is the classical spinor-norm numerator: it takes a vector `v`
to the scalar `b(v,v)` [@Cas08a, Chapter 10, §3]. -/
noncomputable def cliffordNorm (L : FiniteFormCat K K) (g : FiniteFormClifford L) :
    FiniteFormClifford L :=
  g * reverse g

@[simp]
theorem cliffordNorm_one (L : FiniteFormCat K K) : cliffordNorm L 1 = 1 := by
  simp [cliffordNorm]

/-- The Clifford norm of a vector is its square, the scalar `b(v,v)`. -/
theorem cliffordNorm_ι (L : FiniteFormCat K K) (v : L.obj.carrier) :
    cliffordNorm L (ι (finiteFormQuadratic L) v) =
      algebraMap K (FiniteFormClifford L) (L.obj.pairing v v) := by
  rw [cliffordNorm, reverse_ι, ι_sq_scalar, finiteFormQuadratic_apply]

/-- The Clifford norm is twisted-multiplicative in general. -/
theorem cliffordNorm_mul (L : FiniteFormCat K K) (g h : FiniteFormClifford L) :
    cliffordNorm L (g * h) = g * cliffordNorm L h * reverse g := by
  simp only [cliffordNorm, CliffordAlgebra.reverse.map_mul, mul_assoc]

/-- When the second norm is a scalar, the twisted product becomes an honest product.

This is the multiplicativity step of the spinor-norm construction; making it unconditional
needs the theorem that the norm of a Lipschitz element is a scalar. -/
theorem cliffordNorm_mul_of_scalar (L : FiniteFormCat K K) (g h : FiniteFormClifford L)
    (r : K) (hr : cliffordNorm L h = algebraMap K (FiniteFormClifford L) r) :
    cliffordNorm L (g * h) = algebraMap K (FiniteFormClifford L) r * cliffordNorm L g := by
  rw [cliffordNorm_mul, hr, cliffordNorm, ← mul_assoc, Algebra.commutes, mul_assoc]

/-- Twisted conjugation by a vector is the reflection in that vector.

The twist by `involute` cancels the sign in `x ↦ -r_v(x)` produced by plain conjugation. -/
theorem cliffordVectorUnit_involute_conj (L : FiniteFormCat K K)
    (v : L.obj.carrier) (hv : L.obj.pairing v v ≠ 0) (x : L.obj.carrier) :
    involute (Q := finiteFormQuadratic L) (cliffordVectorUnit L v hv)
        * ι (finiteFormQuadratic L) x
        * (((cliffordVectorUnit L v hv)⁻¹ : (FiniteFormClifford L)ˣ) : FiniteFormClifford L) =
      ι (finiteFormQuadratic L) (finiteFormReflection L v hv x) := by
  rw [cliffordVectorUnit_val, cliffordVectorUnit_inv_val, involute_ι, map_smul,
    mul_smul_comm, neg_mul, neg_mul, smul_neg, ι_mul_ι_mul_ι, ← map_smul, ← map_neg]
  congr 1
  rw [finiteFormReflection_apply, polar_finiteFormQuadratic, finiteFormQuadratic_apply,
    reflectionFunctional]
  simp only [LinearMap.smul_apply, BilinModuleCat.bilinMap_apply, smul_eq_mul, smul_sub,
    smul_smul, neg_sub, inv_mul_cancel₀ hv, one_smul]
  congr 2
  ring

/-- The reverse of a unit, as a unit. `reverse` is an anti-automorphism. -/
noncomputable def cliffordReverseUnit (L : FiniteFormCat K K)
    (g : (FiniteFormClifford L)ˣ) : (FiniteFormClifford L)ˣ where
  val := reverse (g : FiniteFormClifford L)
  inv := reverse ((g⁻¹ : (FiniteFormClifford L)ˣ) : FiniteFormClifford L)
  val_inv := by
    rw [← CliffordAlgebra.reverse.map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      CliffordAlgebra.reverse.map_one]
  inv_val := by
    rw [← CliffordAlgebra.reverse.map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      CliffordAlgebra.reverse.map_one]

/-- Reversal commutes with inversion of units. -/
theorem cliffordReverseUnit_inv (L : FiniteFormCat K K) (g : (FiniteFormClifford L)ˣ) :
    cliffordReverseUnit L g⁻¹ = (cliffordReverseUnit L g)⁻¹ :=
  rfl

/-- The Clifford norm of a unit, as a unit. -/
noncomputable def cliffordNormUnit (L : FiniteFormCat K K)
    (g : (FiniteFormClifford L)ˣ) : (FiniteFormClifford L)ˣ :=
  g * cliffordReverseUnit L g

@[simp]
theorem cliffordNormUnit_val (L : FiniteFormCat K K) (g : (FiniteFormClifford L)ˣ) :
    (cliffordNormUnit L g : FiniteFormClifford L) = cliffordNorm L g :=
  rfl

/-- The scalars, as units of the Clifford algebra. -/
noncomputable def algebraMapUnits (L : FiniteFormCat K K) : Kˣ →* (FiniteFormClifford L)ˣ :=
  Units.map (algebraMap K (FiniteFormClifford L)).toMonoidHom

@[simp]
theorem algebraMapUnits_val (L : FiniteFormCat K K) (r : Kˣ) :
    (algebraMapUnits L r : FiniteFormClifford L) = algebraMap K (FiniteFormClifford L) r :=
  rfl

/-- The unit group of the scalars inside the Clifford algebra. -/
noncomputable def scalarUnits (L : FiniteFormCat K K) : Subgroup (FiniteFormClifford L)ˣ :=
  (algebraMapUnits L).range

/-- Scalar units are central. -/
theorem scalarUnits_comm (L : FiniteFormCat K K) {s : (FiniteFormClifford L)ˣ}
    (hs : s ∈ scalarUnits L) (g : (FiniteFormClifford L)ˣ) : s * g = g * s := by
  obtain ⟨r, rfl⟩ := hs
  exact Units.ext (Algebra.commutes (r : K) (g : FiniteFormClifford L))

theorem cliffordReverseUnit_mul (L : FiniteFormCat K K) (g h : (FiniteFormClifford L)ˣ) :
    cliffordReverseUnit L (g * h) = cliffordReverseUnit L h * cliffordReverseUnit L g :=
  Units.ext (CliffordAlgebra.reverse.map_mul _ _)

@[simp]
theorem cliffordNormUnit_one (L : FiniteFormCat K K) : cliffordNormUnit L 1 = 1 :=
  Units.ext (by simp [cliffordNormUnit, cliffordReverseUnit])

/-- The Clifford norm is multiplicative whenever the second norm is a scalar. -/
theorem cliffordNormUnit_mul_of_mem (L : FiniteFormCat K K) (g h : (FiniteFormClifford L)ˣ)
    (hh : cliffordNormUnit L h ∈ scalarUnits L) :
    cliffordNormUnit L (g * h) = cliffordNormUnit L h * cliffordNormUnit L g := by
  have key : cliffordNormUnit L (g * h) =
      g * cliffordNormUnit L h * cliffordReverseUnit L g := by
    rw [cliffordNormUnit, cliffordNormUnit, cliffordReverseUnit_mul]
    group
  rw [key, ← scalarUnits_comm L hh g, cliffordNormUnit, mul_assoc]
  rfl

/-- The Clifford norm of an inverse is the inverse norm, once the norm is a scalar. -/
theorem cliffordNormUnit_inv_of_mem (L : FiniteFormCat K K) (g : (FiniteFormClifford L)ˣ)
    (hg : cliffordNormUnit L g ∈ scalarUnits L) :
    cliffordNormUnit L g⁻¹ = (cliffordNormUnit L g)⁻¹ := by
  have hR : cliffordReverseUnit L g * g = cliffordNormUnit L g := by
    have : cliffordReverseUnit L g = g⁻¹ * cliffordNormUnit L g := by
      rw [cliffordNormUnit, inv_mul_cancel_left]
    rw [this, mul_assoc, scalarUnits_comm L hg g, inv_mul_cancel_left]
  rw [cliffordNormUnit, cliffordReverseUnit_inv, ← mul_inv_rev, hR]

variable [Invertible (2 : K)]

/-- The units whose Clifford norm is a scalar. -/
noncomputable def normScalarSubgroup (L : FiniteFormCat K K) :
    Subgroup (FiniteFormClifford L)ˣ where
  carrier := {g | cliffordNormUnit L g ∈ scalarUnits L}
  one_mem' := by simp
  mul_mem' hg hh := by
    rw [Set.mem_setOf_eq, cliffordNormUnit_mul_of_mem L _ _ hh]
    exact mul_mem hh hg
  inv_mem' hg := by
    rw [Set.mem_setOf_eq, cliffordNormUnit_inv_of_mem L _ hg]
    exact inv_mem hg

/-- A unit which is a vector has scalar Clifford norm, namely `b(v,v)`. -/
theorem cliffordNormUnit_mem_scalarUnits_of_ι (L : FiniteFormCat K K)
    (x : (FiniteFormClifford L)ˣ) (v : L.obj.carrier)
    (hx : ι (finiteFormQuadratic L) v = (x : FiniteFormClifford L)) :
    cliffordNormUnit L x ∈ scalarUnits L := by
  have hQ : L.obj.pairing v v ≠ 0 := by
    have hu : IsUnit (finiteFormQuadratic L v) :=
      isUnit_of_isUnit_ι (finiteFormQuadratic L) (hx ▸ x.isUnit)
    exact (finiteFormQuadratic_apply L v) ▸ hu.ne_zero
  refine ⟨Units.mk0 _ hQ, Units.ext ?_⟩
  rw [cliffordNormUnit_val, ← hx, cliffordNorm_ι]
  rfl

/-- Every Lipschitz-group element has scalar Clifford norm. -/
theorem cliffordNormUnit_mem_scalarUnits (L : FiniteFormCat K K)
    {g : (FiniteFormClifford L)ˣ} (hg : g ∈ lipschitzGroup (finiteFormQuadratic L)) :
    cliffordNormUnit L g ∈ scalarUnits L := by
  refine (Subgroup.closure_le (normScalarSubgroup L)).mpr ?_ hg
  rintro x ⟨v, hv⟩
  exact cliffordNormUnit_mem_scalarUnits_of_ι L x v hv

theorem algebraMapUnits_injective (L : FiniteFormCat K K) :
    Function.Injective (algebraMapUnits L) := fun _ _ hab =>
  Units.ext <| (algebraMap K (FiniteFormClifford L)).injective (congrArg Units.val hab)

/-- The scalar units are a copy of `Kˣ`. -/
noncomputable def scalarUnitsEquiv (L : FiniteFormCat K K) : Kˣ ≃* scalarUnits L :=
  MonoidHom.ofInjective (algebraMapUnits_injective L)

/-- The Clifford norm as a group map from the Lipschitz group to `Kˣ`.

This is the numerator of the spinor norm: it is well defined because the norm of a Lipschitz
element is a scalar, and multiplicative because scalars are central. -/
noncomputable def lipschitzNorm (L : FiniteFormCat K K) :
    lipschitzGroup (finiteFormQuadratic L) →* Kˣ where
  toFun g := (scalarUnitsEquiv L).symm ⟨cliffordNormUnit L g,
    cliffordNormUnit_mem_scalarUnits L g.2⟩
  map_one' := by
    rw [← map_one (scalarUnitsEquiv L).symm]
    exact congrArg _ (Subtype.ext (by simp))
  map_mul' g h := by
    have hmem := cliffordNormUnit_mem_scalarUnits L h.2
    have key : cliffordNormUnit L ((g * h : lipschitzGroup (finiteFormQuadratic L)) :
          (FiniteFormClifford L)ˣ) =
        cliffordNormUnit L (g : (FiniteFormClifford L)ˣ) *
          cliffordNormUnit L (h : (FiniteFormClifford L)ˣ) := by
      rw [Subgroup.coe_mul, cliffordNormUnit_mul_of_mem L _ _ hmem]
      exact scalarUnits_comm L hmem _
    rw [← map_mul (scalarUnitsEquiv L).symm]
    exact congrArg _ (Subtype.ext key)

/-- The Lipschitz norm of a vector is its square `b(v,v)`. -/
@[simp]
theorem lipschitzNorm_cliffordVectorUnit (L : FiniteFormCat K K)
    (v : L.obj.carrier) (hv : L.obj.pairing v v ≠ 0) :
    lipschitzNorm L ⟨cliffordVectorUnit L v hv,
        cliffordVectorUnit_mem_lipschitzGroup L v hv⟩ = Units.mk0 (L.obj.pairing v v) hv := by
  have key : cliffordNormUnit L (cliffordVectorUnit L v hv) =
      algebraMapUnits L (Units.mk0 (L.obj.pairing v v) hv) := by
    apply Units.ext
    rw [cliffordNormUnit_val, cliffordVectorUnit_val, cliffordNorm_ι, algebraMapUnits_val]
    rfl
  rw [lipschitzNorm, MonoidHom.coe_mk, OneHom.coe_mk, MulEquiv.symm_apply_eq]
  exact Subtype.ext key

/-- The spinor norm on the Lipschitz group: the Clifford norm modulo squares.

Composing with a surjection from the Lipschitz group onto `O(L)` whose kernel is the scalars
would produce a term of `SpinorNorm L`; neither the surjection nor the kernel computation is
available in Mathlib. -/
noncomputable def lipschitzSpinorNorm (L : FiniteFormCat K K) :
    lipschitzGroup (finiteFormQuadratic L) →* FieldSquareClass K :=
  (QuotientGroup.mk' (Subgroup.square Kˣ)).comp (lipschitzNorm L)

/-- The spinor norm of a vector is the square class of `b(v,v)`, the value required of a
`SpinorNorm` on the reflection in `v`. -/
theorem lipschitzSpinorNorm_cliffordVectorUnit (L : FiniteFormCat K K)
    (v : L.obj.carrier) (hv : L.obj.pairing v v ≠ 0) :
    lipschitzSpinorNorm L ⟨cliffordVectorUnit L v hv,
        cliffordVectorUnit_mem_lipschitzGroup L v hv⟩ =
      fieldSquareClass (Units.mk0 (L.obj.pairing v v) hv) := by
  rw [lipschitzSpinorNorm, MonoidHom.comp_apply, lipschitzNorm_cliffordVectorUnit]
  rfl

end LeanCategories.Lattices.Valued
