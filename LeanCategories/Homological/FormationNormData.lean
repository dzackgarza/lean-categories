/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.GroupTheory.Index
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.GroupWithZero.Action
public import LeanCategories.Homological.FormationData

/-!
# Raw relative-norm data for class formations

Definition-level realization of the transfer formula underlying Serre,
*Local Fields*, Chapter XI, `FC10-C11-U021`.

For a finite-index subgroup `S ≤ H ≤ G` and a multiplicative `G`-module `A`,
the relative norm is represented by the product of the translates of a
coefficient over a chosen set of coset representatives.  Sweep III records
that displayed product only.

Independence of the chosen representatives, the assertion that an
`S`-fixed coefficient is sent to an `H`-fixed coefficient, multiplicativity,
tower laws, and agreement with the ordinary field norm are result content.
-/

@[expose] public noncomputable section

open scoped BigOperators

namespace LeanCategories.Homological

universe u v

variable {G : Type u} [Group G]
variable {A : Type v} [CommGroup A] [MulDistribMulAction G A]

/-- Raw transfer/norm product for a finite-index subgroup `S ≤ H ≤ G`.

The quotient representative selected by `Quotient.out` is deliberately part
of the raw data.  Its irrelevance for `S`-fixed inputs is a theorem. -/
def formationRelativeNormRaw
    (H : Subgroup G) (S : Subgroup H) [S.FiniteIndex] (a : A) : A := by
  letI := S.fintypeQuotientOfFiniteIndex
  exact ∏ q : H ⧸ S, (((Quotient.out q : H) : G) • a)

def formationLeftMulCosetEquiv
    (H : Subgroup G) (S : Subgroup H) (g : H) : (H ⧸ S) ≃ (H ⧸ S) where
  toFun q := g • q
  invFun q := g⁻¹ • q
  left_inv q := by simp
  right_inv q := by simp

@[simp] lemma formationLeftMulCosetEquiv_mk
    (H : Subgroup G) (S : Subgroup H) (g x : H) :
    formationLeftMulCosetEquiv H S g (QuotientGroup.mk x) =
      QuotientGroup.mk (g * x) :=
  rfl

def formationRelativeCosetAction
    (H L : Subgroup G) (hLH : L ≤ H)
    (a : formationFixedSubgroup L A)
    (q : H ⧸ L.subgroupOf H) : A :=
  Quotient.liftOn' q
    (fun h : H => (h : G) • a.1)
    (by
      intro x y hxy
      have hmem : x⁻¹ * y ∈ L.subgroupOf H :=
        QuotientGroup.leftRel_apply.mp hxy
      let l : L := ⟨(x⁻¹ * y : H).1, hmem⟩
      have hy : y = x * ⟨l.1, hLH l.2⟩ := by
        apply Subtype.ext
        simp [l]
      rw [hy]
      change (x : G) • a.1 = ((x : G) * l.1) • a.1
      rw [mul_smul, a.2 l])

@[simp]
lemma formationRelativeCosetAction_mk
    (H L : Subgroup G) (hLH : L ≤ H)
    (a : formationFixedSubgroup L A) (h : H) :
    formationRelativeCosetAction (A := A) H L hLH a (QuotientGroup.mk h) =
      (h : G) • a.1 :=
  rfl

def formationRelativeNormValue
    (H L : Subgroup G) (hLH : L ≤ H) [L.FiniteIndex]
    (a : formationFixedSubgroup L A) : A := by
  letI := (L.subgroupOf H).fintypeQuotientOfFiniteIndex
  exact ∏ q : H ⧸ L.subgroupOf H,
    formationRelativeCosetAction (A := A) H L hLH a q

lemma formationRelativeNormValue_fixed
    (H L : Subgroup G) (hLH : L ≤ H) [L.FiniteIndex]
    (a : formationFixedSubgroup L A) (h : H) :
    (h : G) • formationRelativeNormValue (A := A) H L hLH a =
      formationRelativeNormValue (A := A) H L hLH a := by
  letI := (L.subgroupOf H).fintypeQuotientOfFiniteIndex
  have hterm : ∀ q : H ⧸ L.subgroupOf H,
      (h : G) • formationRelativeCosetAction (A := A) H L hLH a q =
        formationRelativeCosetAction (A := A) H L hLH a
          (formationLeftMulCosetEquiv H (L.subgroupOf H) h q) := by
    intro q
    refine Quotient.inductionOn' q ?_
    intro x
    simp only [formationLeftMulCosetEquiv_mk, formationRelativeCosetAction_mk]
    change (h : G) • ((x : G) • a.1) = ((h : G) * (x : G)) • a.1
    rw [mul_smul]
  rw [formationRelativeNormValue]
  rw [Finset.smul_prod']
  simp_rw [hterm]
  exact (formationLeftMulCosetEquiv H (L.subgroupOf H) h).prod_comp
    (formationRelativeCosetAction (A := A) H L hLH a)

def formationRelativeFixedNormHom
    (H L : Subgroup G) (hLH : L ≤ H) [L.FiniteIndex] :
    formationFixedSubgroup L A →* formationFixedSubgroup H A where
  toFun a := ⟨formationRelativeNormValue (A := A) H L hLH a,
    formationRelativeNormValue_fixed (A := A) H L hLH a⟩
  map_one' := by
    apply Subtype.ext
    letI := (L.subgroupOf H).fintypeQuotientOfFiniteIndex
    change (∏ q : H ⧸ L.subgroupOf H,
      formationRelativeCosetAction (A := A) H L hLH (1 : formationFixedSubgroup L A) q) = 1
    apply Finset.prod_eq_one
    intro q _
    refine Quotient.inductionOn' q ?_
    intro x
    simp only [formationRelativeCosetAction_mk]
    change (x : G) • (1 : A) = 1
    exact smul_one (x : G)
  map_mul' a b := by
    apply Subtype.ext
    letI := (L.subgroupOf H).fintypeQuotientOfFiniteIndex
    change (∏ q : H ⧸ L.subgroupOf H,
      formationRelativeCosetAction (A := A) H L hLH (a * b) q) =
      (∏ q : H ⧸ L.subgroupOf H, formationRelativeCosetAction (A := A) H L hLH a q) *
      (∏ q : H ⧸ L.subgroupOf H, formationRelativeCosetAction (A := A) H L hLH b q)
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro q _
    refine Quotient.inductionOn' q ?_
    intro x
    simp only [formationRelativeCosetAction_mk, Subgroup.coe_mul]
    exact smul_mul' (x : G) a.1 b.1

/-- The relative norm as an actual multiplicative homomorphism.  This is the
same finite-coset product as `formationRelativeNormRaw`; multiplicativity is
part of constructing the map rather than deferred to a later graph. -/
def formationRelativeNormHom
    (H : Subgroup G) (S : Subgroup H) [S.FiniteIndex] : A →* A where
  toFun := formationRelativeNormRaw (A := A) H S
  map_one' := by
    classical
    simp [formationRelativeNormRaw]
  map_mul' a b := by
    classical
    simp [formationRelativeNormRaw, Finset.prod_mul_distrib]

/-- Serre's norm group: the subgroup which is the image of the relative norm
homomorphism. -/
def formationNormGroupData
    (H : Subgroup G) (S : Subgroup H) [S.FiniteIndex] : Subgroup A :=
  (formationRelativeNormHom (A := A) H S).range

def formationFixedNormGroupData
    (H L : Subgroup G) (hLH : L ≤ H) [L.FiniteIndex] :
    Subgroup (formationFixedSubgroup H A) :=
  (formationRelativeFixedNormHom (A := A) H L hLH).range

/-- The underlying set of the norm group. -/
def formationNormImageData
    (H : Subgroup G) (S : Subgroup H) [S.FiniteIndex] : Set A :=
  formationNormGroupData (A := A) H S

/-- Compatibility predicate for legacy set-level consumers. -/
def IsFormationNormGroupData
    (H : Subgroup G) (S : Subgroup H) [S.FiniteIndex] (I : Set A) : Prop :=
  I = formationNormImageData (A := A) H S

end LeanCategories.Homological
