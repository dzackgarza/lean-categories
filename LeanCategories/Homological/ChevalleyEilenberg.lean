/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.Algebra.Lie.UniversalEnveloping
public import Mathlib.LinearAlgebra.Alternating.DomCoprod
public import Mathlib.LinearAlgebra.Alternating.Uncurry.Fin
public import Mathlib.LinearAlgebra.ExteriorAlgebra.Grading
public import Mathlib.LinearAlgebra.ExteriorPower.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Tower

/-!
# The Chevalley--Eilenberg complex

Weibel, *An Introduction to Homological Algebra* (1994), §7.7, pp. 238--241
(FC05-C07-U047, FC05-C07-U048).

For a Lie algebra `L` over a commutative ring `k`, put
`U = U(L)` and `V_p(L) = U ⊗_k Λ^p L`.  Mathlib already owns these degree
objects and the enveloping-algebra augmentation.  This file records a
source-faithful realization interface for the Chevalley--Eilenberg differential
on pure wedges.

The fact that the resulting augmented complex is a projective resolution under
Weibel's freeness hypotheses is Theorem 7.7.2 and is intentionally not asserted
here.
-/

@[expose] public section

namespace LeanCategories.Homological

open CategoryTheory
open scoped BigOperators TensorProduct

attribute [local instance 100] LieRing.ofAssociativeRing

universe u

variable (k L : Type u) [CommRing k] [LieRing L] [LieAlgebra k L]

/-- The Lie bracket as the canonical alternating bilinear map. -/
noncomputable def chevalleyEilenbergLieBracket : L [⋀^Fin 2]→ₗ[k] L where
  toMultilinearMap :=
    LinearMap.uncurryLeft <|
      (MultilinearMap.ofSubsingletonₗ k k L L (0 : Fin 1)).toLinearMap.comp
        (LieAlgebra.ad k L).toLinearMap
  map_eq_zero_of_eq' := by
    intro x i j hij hne
    fin_cases i <;> fin_cases j <;> simp_all [Fin.tail, lie_self]

/-- The pure wedge `x₀ ∧ ⋯ ∧ x_{p-1}` as an element of `Λ^p L`. -/
def chevalleyEilenbergWedge {p : ℕ} (x : Fin p → L) :
    ⋀[k]^p L :=
  ⟨ExteriorAlgebra.ιMulti k p x,
    ExteriorAlgebra.ιMulti_range k p ⟨x, rfl⟩⟩

@[simp]
theorem chevalleyEilenbergWedge_eq_ιMulti {p : ℕ} (x : Fin p → L) :
    chevalleyEilenbergWedge k L x = exteriorPower.ιMulti k p x := by
  apply Subtype.ext
  rfl

/-- A pure tensor `u ⊗ (x₀ ∧ ⋯ ∧ x_{p-1})` in `V_p(L)`. -/
def chevalleyEilenbergPure {p : ℕ}
    (u : UniversalEnvelopingAlgebra k L) (x : Fin p → L) :
    UniversalEnvelopingAlgebra k L ⊗[k] (⋀[k]^p L) :=
  u ⊗ₜ[k] chevalleyEilenbergWedge k L x

/-- The action summand before alternation: `x` acts by the image of `x` in
`U(L)` on the left tensor factor, while the remaining `p` inputs form their
pure wedge. -/
noncomputable def chevalleyEilenbergActionSeed (p : ℕ) :
    L →ₗ[k] L [⋀^Fin p]→ₗ[k]
      (UniversalEnvelopingAlgebra k L ⊗[k] (⋀[k]^p L)) where
  toFun x :=
    (TensorProduct.mk k _ _ (UniversalEnvelopingAlgebra.ι k x)).compAlternatingMap
      (exteriorPower.ιMulti k p)
  map_add' x y := by
    ext v
    simp
  map_smul' r x := by
    ext v
    simp [TensorProduct.smul_tmul']

/-- The alternating action part of the Chevalley--Eilenberg differential in
degree `p + 1`. Mathlib's alternating uncurrying supplies exactly the source
sum `∑ i, (-1)^i ι(x_i) ⊗ x_0∧⋯∧x̂_i∧⋯`. -/
noncomputable def chevalleyEilenbergActionAlternating (p : ℕ) :
    L [⋀^Fin (p + 1)]→ₗ[k]
      (UniversalEnvelopingAlgebra k L ⊗[k] (⋀[k]^p L)) :=
  AlternatingMap.alternatizeUncurryFin (chevalleyEilenbergActionSeed k L p)

@[simp]
theorem chevalleyEilenbergActionAlternating_apply (p : ℕ) (x : Fin (p + 1) → L) :
    chevalleyEilenbergActionAlternating k L p x =
      ∑ i : Fin (p + 1), ((-1 : ℤ) ^ i.val) •
        chevalleyEilenbergPure k L
          (UniversalEnvelopingAlgebra.ι k (x i)) (i.removeNth x) := by
  simp [chevalleyEilenbergActionAlternating, chevalleyEilenbergActionSeed,
    AlternatingMap.alternatizeUncurryFin_apply, chevalleyEilenbergPure,
    chevalleyEilenbergWedge_eq_ιMulti]

/-- Left exterior multiplication, restricted to homogeneous exterior powers.
This is the linear map `x ⊗ w ↦ x ∧ w`. -/
noncomputable def chevalleyEilenbergWedgeLeft (p : ℕ) :
    L ⊗[k] (⋀[k]^p L) →ₗ[k] (⋀[k]^(p + 1) L) :=
  TensorProduct.lift <| LinearMap.mk₂ k
    (fun x w =>
      ⟨ExteriorAlgebra.ι k x * (w : ExteriorAlgebra k L), by
        have hx : ExteriorAlgebra.ι k x ∈ (⋀[k]^1 L) := by
          simpa only [pow_one] using
            (LinearMap.mem_range_self (ExteriorAlgebra.ι k) x)
        simpa [Nat.one_add] using SetLike.mul_mem_graded hx w.2⟩)
    (by
      intro x y w
      apply Subtype.ext
      change ExteriorAlgebra.ι k (x + y) * (w : ExteriorAlgebra k L) =
        ExteriorAlgebra.ι k x * (w : ExteriorAlgebra k L) +
          ExteriorAlgebra.ι k y * (w : ExteriorAlgebra k L)
      rw [map_add, add_mul])
    (by
      intro r x w
      apply Subtype.ext
      change ExteriorAlgebra.ι k (r • x) * (w : ExteriorAlgebra k L) =
        r • (ExteriorAlgebra.ι k x * (w : ExteriorAlgebra k L))
      rw [map_smul, Algebra.smul_def, Algebra.smul_def, mul_assoc])
    (by
      intro x y z
      apply Subtype.ext
      simp [mul_add])
    (by
      intro r x w
      apply Subtype.ext
      change ExteriorAlgebra.ι k x * (r • (w : ExteriorAlgebra k L)) =
        r • (ExteriorAlgebra.ι k x * (w : ExteriorAlgebra k L))
      rw [Algebra.smul_def, Algebra.smul_def, ← mul_assoc,
        ← Algebra.commutes r (ExteriorAlgebra.ι k x), mul_assoc])

@[simp]
theorem chevalleyEilenbergWedgeLeft_tmul (p : ℕ) (x : L) (w : ⋀[k]^p L) :
    chevalleyEilenbergWedgeLeft k L p (x ⊗ₜ[k] w) =
      ⟨ExteriorAlgebra.ι k x * (w : ExteriorAlgebra k L), by
        have hx : ExteriorAlgebra.ι k x ∈ (⋀[k]^1 L) := by
          simpa only [pow_one] using
            (LinearMap.mem_range_self (ExteriorAlgebra.ι k) x)
        simpa [Nat.one_add] using SetLike.mul_mem_graded hx w.2⟩ := by
  rfl

/-- The bracket part of the Chevalley--Eilenberg boundary as an alternating
map on `p+1` inputs.  In positive target degree this is the exterior product
of the Lie bracket with the universal `(p-1)`-fold wedge, followed by exterior
multiplication.  The leading minus sign is the zero-based form of Weibel's
`(-1)^{i+j}` convention. -/
noncomputable def chevalleyEilenbergBracketAlternating :
    (p : ℕ) → L [⋀^Fin (p + 1)]→ₗ[k] (⋀[k]^p L)
  | 0 => 0
  | n + 1 =>
      -((chevalleyEilenbergWedgeLeft k L n).compAlternatingMap <|
        AlternatingMap.domDomCongr
          ((finSumFinEquiv : Fin 2 ⊕ Fin n ≃ Fin (2 + n)).trans
            (finCongr (by omega))) <|
          (chevalleyEilenbergLieBracket k L).domCoprod
            (exteriorPower.ιMulti k n))

@[simp]
theorem chevalleyEilenbergBracketAlternating_zero :
    chevalleyEilenbergBracketAlternating k L 0 = 0 := rfl

/-- The exterior-valued bracket term embedded in `U(L) ⊗ Λ^p L` by `w ↦ 1 ⊗ w`. -/
noncomputable def chevalleyEilenbergBracketTensorAlternating (p : ℕ) :
    L [⋀^Fin (p + 1)]→ₗ[k]
      (UniversalEnvelopingAlgebra k L ⊗[k] (⋀[k]^p L)) :=
  (TensorProduct.mk k (UniversalEnvelopingAlgebra k L) (⋀[k]^p L) 1).compAlternatingMap
    (chevalleyEilenbergBracketAlternating k L p)

/-- The full source differential on the exterior generators, before extending
`U(L)`-linearly. -/
noncomputable def chevalleyEilenbergAlternating (p : ℕ) :
    L [⋀^Fin (p + 1)]→ₗ[k]
      (UniversalEnvelopingAlgebra k L ⊗[k] (⋀[k]^p L)) :=
  chevalleyEilenbergActionAlternating k L p +
    chevalleyEilenbergBracketTensorAlternating k L p

/-- The descended `k`-linear Chevalley--Eilenberg differential on the exterior
power factor. -/
noncomputable def chevalleyEilenbergExteriorDifferential (p : ℕ) :
    (⋀[k]^(p + 1) L) →ₗ[k]
      (UniversalEnvelopingAlgebra k L ⊗[k] (⋀[k]^p L)) :=
  exteriorPower.alternatingMapLinearEquiv (chevalleyEilenbergAlternating k L p)

@[simp]
theorem chevalleyEilenbergExteriorDifferential_ιMulti (p : ℕ)
    (x : Fin (p + 1) → L) :
    chevalleyEilenbergExteriorDifferential k L p (exteriorPower.ιMulti k _ x) =
      chevalleyEilenbergAlternating k L p x := by
  exact exteriorPower.alternatingMapLinearEquiv_apply_ιMulti _ _

/-- Currying the differential with respect to the left `U(L)`-action. -/
noncomputable def chevalleyEilenbergDifferentialCurry (p : ℕ) :
    UniversalEnvelopingAlgebra k L →ₗ[UniversalEnvelopingAlgebra k L]
      ((⋀[k]^(p + 1) L) →ₗ[k]
        (UniversalEnvelopingAlgebra k L ⊗[k] (⋀[k]^p L))) where
  toFun u := u • chevalleyEilenbergExteriorDifferential k L p
  map_add' u v := by
    rw [add_smul]
  map_smul' u v := by
    simp only [smul_eq_mul, RingHom.id_apply, mul_smul]

/-- The actual `U(L)`-linear Chevalley--Eilenberg differential
`U(L) ⊗ Λ^{p+1}L → U(L) ⊗ Λ^pL`. -/
noncomputable def chevalleyEilenbergDifferential (p : ℕ) :
    (UniversalEnvelopingAlgebra k L ⊗[k] (⋀[k]^(p + 1) L))
      →ₗ[UniversalEnvelopingAlgebra k L]
    (UniversalEnvelopingAlgebra k L ⊗[k] (⋀[k]^p L)) :=
  TensorProduct.AlgebraTensorModule.lift
    (chevalleyEilenbergDifferentialCurry k L p)

@[simp]
theorem chevalleyEilenbergDifferential_tmul (p : ℕ)
    (u : UniversalEnvelopingAlgebra k L) (w : ⋀[k]^(p + 1) L) :
    chevalleyEilenbergDifferential k L p (u ⊗ₜ[k] w) =
      u • chevalleyEilenbergExteriorDifferential k L p w := by
  rfl

@[simp]
theorem chevalleyEilenbergDifferential_pure (p : ℕ)
    (u : UniversalEnvelopingAlgebra k L) (x : Fin (p + 1) → L) :
    chevalleyEilenbergDifferential k L p
        (u ⊗ₜ[k] exteriorPower.ιMulti k _ x) =
      u • chevalleyEilenbergAlternating k L p x := by
  rw [chevalleyEilenbergDifferential_tmul,
    chevalleyEilenbergExteriorDifferential_ιMulti]

/-- Delete the `i`th factor from a wedge tuple. -/
def chevalleyEilenbergOmit {p : ℕ} (x : Fin (p + 1) → L)
    (i : Fin (p + 1)) : Fin p → L :=
  i.removeNth x

/-- Replace the `i`th surviving factor by `[x_i,x_j]` after deleting the
`j`th factor, for `i < j`.

Putting the bracket in the original `i`th position changes the standard
front-loaded bracket sign `(-1)^(i+j)` into `(-1)^j` in zero-based indexing. -/
def chevalleyEilenbergBracketTuple {p : ℕ} (x : Fin (p + 1) → L)
    (i j : Fin (p + 1)) (hij : i < j) : Fin p → L :=
  let i' : Fin p :=
    ⟨i.val, lt_of_lt_of_le hij (Nat.le_of_lt_succ j.isLt)⟩
  Function.update (j.removeNth x) i' ⁅x i, x j⁆

/-- The action part of the Chevalley--Eilenberg boundary on a pure wedge. -/
noncomputable def chevalleyEilenbergActionBoundary {p : ℕ}
    (u : UniversalEnvelopingAlgebra k L) (x : Fin (p + 1) → L) :
    UniversalEnvelopingAlgebra k L ⊗[k] (⋀[k]^p L) :=
  ∑ i : Fin (p + 1),
    ((-1 : ℤ) ^ i.val) •
      chevalleyEilenbergPure k L
        (u * UniversalEnvelopingAlgebra.ι k (x i))
        (chevalleyEilenbergOmit L x i)

/-- The bracket part of the Chevalley--Eilenberg boundary on a pure wedge.
The bracket is kept in the original `i`th position, hence the equivalent
zero-based sign `(-1)^j`. -/
noncomputable def chevalleyEilenbergBracketBoundary {p : ℕ}
    (u : UniversalEnvelopingAlgebra k L) (x : Fin (p + 1) → L) :
    UniversalEnvelopingAlgebra k L ⊗[k] (⋀[k]^p L) :=
  ∑ i : Fin (p + 1), ∑ j : Fin (p + 1),
    if hij : i < j then
      ((-1 : ℤ) ^ j.val) •
        chevalleyEilenbergPure k L u
          (chevalleyEilenbergBracketTuple L x i j hij)
    else 0

/-- Weibel's full Chevalley--Eilenberg boundary formula on a pure wedge. -/
noncomputable def chevalleyEilenbergBoundary {p : ℕ}
    (u : UniversalEnvelopingAlgebra k L) (x : Fin (p + 1) → L) :
    UniversalEnvelopingAlgebra k L ⊗[k] (⋀[k]^p L) :=
  chevalleyEilenbergActionBoundary k L u x +
    chevalleyEilenbergBracketBoundary k L u x

/-- A source-faithful realization of the Chevalley--Eilenberg standard complex.
The chain-complex laws, including `d²=0`, are part of `complex`; this structure
only fixes the degree objects and Weibel's differential formula on the spanning
pure wedges. -/
structure ChevalleyEilenbergRealization where
  /-- The realized standard complex. -/
  complex : ChainComplex (ModuleCat (UniversalEnvelopingAlgebra k L)) ℕ
  /-- Degree `p` is `U(L) ⊗_k Λ^p L`. -/
  degreeIso : ∀ p : ℕ,
    complex.X p ≅ ModuleCat.of (UniversalEnvelopingAlgebra k L)
      (UniversalEnvelopingAlgebra k L ⊗[k] (⋀[k]^p L))
  /-- The differential is the alternating action-and-bracket formula on pure wedges. -/
  differential_pure : ∀ (p : ℕ) (u : UniversalEnvelopingAlgebra k L)
      (x : Fin (p + 1) → L),
    (degreeIso p).hom
        (complex.d (p + 1) p
          ((degreeIso (p + 1)).inv (chevalleyEilenbergPure k L u x))) =
      chevalleyEilenbergBoundary k L u x

end LeanCategories.Homological
