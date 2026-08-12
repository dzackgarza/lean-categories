/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.GroupTheory.Complement
public import Mathlib.GroupTheory.Index
public import Mathlib.MeasureTheory.Measure.Haar.Basic
public import Mathlib.Topology.Algebra.OpenSubgroup
public import Mathlib.Topology.Algebra.RestrictedProduct.TopologicalSpace

/-!
# Haar measure on a restricted product of groups

Let `G i` be a family of topological groups and `U i` a family of open subgroups. The restricted
product `Πʳ i, [G i, U i]` is a topological group, and the set of elements whose component lies
in `U i` at every index is a subgroup of it. If every `U i` is compact, that subgroup is compact
and open, so it normalizes a Haar measure.

More generally a family `K i` of open subgroups with `K i ≤ U i`, and with `K i = U i` outside a
finite set of indices, cuts out a compact open subgroup `piSubgroup U K`. This file computes its
measure. The computation is in two steps.

* `relIndex_piSubgroup`: the index of `piSubgroup U K` in `piSubgroup U U` is the product of the
  local indices of `K i` in `U i`. This is pure group theory. The proof changes the family at one
  index at a time: evaluation at that index is a surjection onto `U i` which pulls the local
  subgroup back to the smaller cut-out subgroup, so `Subgroup.index_comap_of_surjective` gives
  the local index, and relative indices multiply in towers.
* `relIndex_mul_measure`: in any group with a left-invariant measure, a subgroup of finite
  relative index in a measurable subgroup has proportional measure.

Combining them gives `measure_restrictedProduct_pi`: the measure of `piSubgroup U K` is the
product of the local ratios `μloc i (K i) / μloc i (U i)` times the measure of `piSubgroup U U`.
That product is finite because almost all factors are one. The statement holds for an arbitrary
left-invariant measure on the restricted product and arbitrary Haar measures on the factors,
because only ratios of local measures occur.

`restrictedProductHaarMeasure` is the Haar measure normalized so that `piSubgroup U U` has
measure one; for it the product of local ratios is the measure itself.
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal Pointwise RestrictedProduct

namespace LeanCategories.ForMathlib

/-! ## Relative index and left-invariant measures -/

section RelIndexMeasure

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G]

/-- A subgroup of finite relative index in a larger subgroup has proportional measure. This is
the relative form of `Subgroup.index_mul_measure`. -/
theorem relIndex_mul_measure {A B : Subgroup G} (hAB : A ≤ B)
    [(A.subgroupOf B).FiniteIndex] (hA : MeasurableSet (A : Set G))
    (μ : Measure G) [μ.IsMulLeftInvariant] :
    A.relIndex B * μ A = μ B := by
  obtain ⟨s, hs, -⟩ := (A.subgroupOf B).exists_isComplement_left 1
  haveI hfin : Finite s := hs.finite_left_iff.mpr inferInstance
  have hcover : (B : Set G) = ⋃ a : s, (a.1.1 : G) • (A : Set G) := by
    refine Set.Subset.antisymm (fun x hx => ?_) (Set.iUnion_subset fun a => ?_)
    · obtain ⟨⟨a, h⟩, hah⟩ := hs.2 (⟨x, hx⟩ : B)
      exact Set.mem_iUnion.mpr ⟨a, ⟨(h : G), h.2, congrArg Subtype.val hah⟩⟩
    · rintro _ ⟨y, hy, rfl⟩
      exact mul_mem a.1.2 (hAB hy)
  have hdisj : Pairwise (Function.onFun Disjoint fun a : s => (a.1.1 : G) • (A : Set G)) := by
    intro a b hab
    refine Set.disjoint_left.mpr fun x hxa hxb => hab ?_
    obtain ⟨u, hu, rfl⟩ := hxa
    obtain ⟨w, hw, hwu⟩ := hxb
    have huB : (a.1.1 : G) * u ∈ B := mul_mem a.1.2 (hAB hu)
    have hmem : (⟨u, by simpa using mul_mem (inv_mem a.1.2) huB⟩ : B) ∈ A.subgroupOf B := hu
    have hmemw : (⟨w, hAB hw⟩ : B) ∈ A.subgroupOf B := hw
    have hkey : ((a, ⟨_, hmem⟩) : s × (A.subgroupOf B : Set B)) = (b, ⟨_, hmemw⟩) :=
      hs.1 (Subtype.ext hwu.symm)
    exact congrArg Prod.fst hkey
  have hmeas : ∀ a : s, MeasurableSet ((a.1.1 : G) • (A : Set G)) :=
    fun a => hA.const_smul _
  calc (A.relIndex B : ℝ≥0∞) * μ A = ∑' a : s, μ ((a.1.1 : G) • (A : Set G)) := by
        simp [measure_smul, Subgroup.relIndex, hs.encard_left]
    _ = μ B := by rw [← measure_iUnion hdisj hmeas, ← hcover]

end RelIndexMeasure

/-! ## Compact open subgroups have finite relative index -/

section FiniteIndex

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- An open subgroup has finite relative index in a compact subgroup. -/
theorem finiteIndex_subgroupOf_of_isOpen {A B : Subgroup G} (hA : IsOpen (A : Set G))
    (hB : IsCompact (B : Set G)) : (A.subgroupOf B).FiniteIndex := by
  haveI : CompactSpace B := isCompact_iff_compactSpace.mp hB
  haveI : Finite (B ⧸ A.subgroupOf B) :=
    Subgroup.quotient_finite_of_isOpen _ (Subgroup.subgroupOf_isOpen B A hA)
  exact Subgroup.finiteIndex_of_finite_quotient

end FiniteIndex

/-! ## Subgroups of a restricted product cut out by a family of subgroups -/

section PiSubgroup

variable {ι : Type*} {G : ι → Type*} [Π i, Group (G i)]
variable (U : Π i, Subgroup (G i))

/-- The subgroup of a restricted product whose component at every index lies in `K i`. -/
def piSubgroup (K : Π i, Subgroup (G i)) : Subgroup (Πʳ i, [G i, U i]) :=
  (Subgroup.pi Set.univ K).comap RestrictedProduct.coeMonoidHom

variable {U}

@[simp]
theorem mem_piSubgroup {K : Π i, Subgroup (G i)} {x : Πʳ i, [G i, U i]} :
    x ∈ piSubgroup U K ↔ ∀ i, x i ∈ K i :=
  ⟨fun h i => h i (Set.mem_univ i), fun h i _ => h i⟩

/-- A pointwise inclusion of families gives an inclusion of the cut-out subgroups. -/
theorem piSubgroup_mono {A B : Π i, Subgroup (G i)} (h : ∀ i, A i ≤ B i) :
    piSubgroup U A ≤ piSubgroup U B :=
  fun _ hx => mem_piSubgroup.mpr fun i => h i (mem_piSubgroup.mp hx i)

/-- Evaluation at one index, as a homomorphism onto a subgroup containing every component. -/
def piSubgroupEval (B : Π i, Subgroup (G i)) (j : ι) : piSubgroup U B →* B j where
  toFun x := ⟨(x : Πʳ i, [G i, U i]) j, mem_piSubgroup.mp x.2 j⟩
  map_one' := rfl
  map_mul' _ _ := rfl

/-- Evaluation at one index is onto the subgroup at that index. -/
theorem piSubgroupEval_surjective (B : Π i, Subgroup (G i)) (j : ι) :
    Function.Surjective (piSubgroupEval (U := U) B j) := by
  classical
  intro b
  have hcof : ∀ᶠ i in cofinite, Pi.mulSingle j (b : G j) i ∈ (U i : Set (G i)) := by
    refine Filter.eventually_cofinite.mpr ((Set.finite_singleton j).subset fun i hi => ?_)
    by_contra hij
    exact hi (by rw [Pi.mulSingle_eq_of_ne hij]; exact one_mem _)
  refine ⟨⟨RestrictedProduct.mk _ hcof, mem_piSubgroup.mpr fun i => ?_⟩, ?_⟩
  · by_cases hij : i = j
    · subst hij
      simp
    · simp [Pi.mulSingle_eq_of_ne hij]
  · exact Subtype.ext (by simp [piSubgroupEval])

/-- Changing a family at one index only, the smaller cut-out subgroup is the pullback of the
smaller subgroup at that index. -/
theorem comap_piSubgroupEval {A B : Π i, Subgroup (G i)} (j : ι)
    (heq : ∀ i, i ≠ j → A i = B i) :
    ((A j).subgroupOf (B j)).comap (piSubgroupEval (U := U) B j) =
      (piSubgroup U A).subgroupOf (piSubgroup U B) := by
  ext x
  simp only [Subgroup.mem_comap, Subgroup.mem_subgroupOf, mem_piSubgroup]
  refine ⟨fun h i => ?_, fun h => h j⟩
  by_cases hij : i = j
  · subst hij
    exact h
  · exact (heq i hij).ge (mem_piSubgroup.mp x.2 i)

/-- Changing a family at one index changes the cut-out subgroup by the local index. -/
theorem relIndex_piSubgroup_single {A B : Π i, Subgroup (G i)} (j : ι)
    (heq : ∀ i, i ≠ j → A i = B i) :
    (piSubgroup U A).relIndex (piSubgroup U B) = (A j).relIndex (B j) := by
  have h := Subgroup.index_comap_of_surjective (H := (A j).subgroupOf (B j))
    (piSubgroupEval_surjective (U := U) B j)
  rw [comap_piSubgroupEval j heq] at h
  exact h

/-- The index of one cut-out subgroup in another is the product of the local indices. -/
theorem relIndex_piSubgroup (S : Finset ι) :
    ∀ A B : Π i, Subgroup (G i), (∀ i, A i ≤ B i) → (∀ i, i ∉ S → A i = B i) →
      (piSubgroup U A).relIndex (piSubgroup U B) = ∏ i ∈ S, (A i).relIndex (B i) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    intro A B _ hout
    have hAB : A = B := funext fun i => hout i (Finset.notMem_empty i)
    subst hAB
    simp [Subgroup.relIndex_self]
  | @insert j S hj ih =>
    intro A B hAB hout
    set A' : Π i, Subgroup (G i) := Function.update A j (B j) with hA'def
    have hA'j : A' j = B j := by simp [hA'def]
    have hA'ne : ∀ i, i ≠ j → A' i = A i := fun i hij => by simp [hA'def, hij]
    have hAA' : ∀ i, A i ≤ A' i := fun i => by
      by_cases hij : i = j
      · subst hij; rw [hA'j]; exact hAB i
      · rw [hA'ne i hij]
    have hA'B : ∀ i, A' i ≤ B i := fun i => by
      by_cases hij : i = j
      · subst hij; rw [hA'j]
      · rw [hA'ne i hij]; exact hAB i
    have h1 : (piSubgroup U A).relIndex (piSubgroup U A') = (A j).relIndex (B j) := by
      rw [relIndex_piSubgroup_single j fun i hij => (hA'ne i hij).symm, hA'j]
    have h2 : (piSubgroup U A').relIndex (piSubgroup U B) = ∏ i ∈ S, (A i).relIndex (B i) := by
      rw [ih A' B hA'B fun i hi => ?_]
      · exact Finset.prod_congr rfl fun i hi =>
          congrArg (fun H : Subgroup (G i) => H.relIndex (B i))
            (hA'ne i fun h => hj (h ▸ hi))
      · by_cases hij : i = j
        · subst hij; exact hA'j
        · rw [hA'ne i hij]
          exact hout i fun h => (Finset.mem_insert.mp h).elim hij fun h' => hi h'
    rw [Finset.prod_insert hj, ← h1, ← h2,
      Subgroup.relIndex_mul_relIndex _ _ _ (piSubgroup_mono hAA') (piSubgroup_mono hA'B)]

/-- The index of a cut-out subgroup in the distinguished one, as a finite product of local
indices over the indices where the two families differ. -/
theorem relIndex_piSubgroup_toFinset {K : Π i, Subgroup (G i)} (hKU : ∀ i, K i ≤ U i)
    (hS : {i | K i ≠ U i}.Finite) :
    (piSubgroup U K).relIndex (piSubgroup U U) =
      ∏ i ∈ hS.toFinset, (K i).relIndex (U i) := by
  classical
  refine relIndex_piSubgroup hS.toFinset K U hKU fun i hi => ?_
  by_contra h
  exact hi (hS.mem_toFinset.mpr h)

end PiSubgroup

/-! ## Compactness and openness of the cut-out subgroups -/

section Topology

variable {ι : Type*} {G : ι → Type*} [Π i, Group (G i)] [Π i, TopologicalSpace (G i)]
variable [∀ i, IsTopologicalGroup (G i)] {U : Π i, Subgroup (G i)}
variable [hUopen : Fact (∀ i, IsOpen (U i : Set (G i)))]

omit [∀ i, IsTopologicalGroup (G i)] in
/-- A family of open subgroups which is the distinguished family outside a finite set of indices
cuts out an open subgroup. -/
theorem isOpen_piSubgroup {K : Π i, Subgroup (G i)} (hKU : ∀ i, K i ≤ U i)
    (hKopen : ∀ i, IsOpen (K i : Set (G i))) (hS : {i | K i ≠ U i}.Finite) :
    IsOpen (piSubgroup U K : Set (Πʳ i, [G i, U i])) := by
  have hset : (piSubgroup U K : Set (Πʳ i, [G i, U i])) =
      {x : Πʳ i, [G i, U i] | ∀ i, x.1 i ∈ (U i : Set (G i))} ∩
        ⋂ i ∈ {i | K i ≠ U i}, (fun x : Πʳ i, [G i, U i] => x i) ⁻¹' (K i : Set (G i)) := by
    ext x
    simp only [SetLike.mem_coe, mem_piSubgroup, Set.mem_inter_iff, Set.mem_setOf_eq,
      Set.mem_iInter, Set.mem_preimage]
    refine ⟨fun h => ⟨fun i => hKU i (h i), fun i _ => h i⟩, fun ⟨h1, h2⟩ i => ?_⟩
    by_cases hi : K i = U i
    · exact hi.ge (h1 i)
    · exact h2 i hi
  rw [hset]
  exact (RestrictedProduct.isOpen_forall_mem fun i => hUopen.out i).inter
    (hS.isOpen_biInter fun i _ => (hKopen i).preimage (RestrictedProduct.continuous_eval i))

omit [∀ i, IsTopologicalGroup (G i)] hUopen in
/-- The distinguished family cuts out a compact subgroup when every member is compact. -/
theorem isCompact_piSubgroup_self (hUcompact : ∀ i, IsCompact (U i : Set (G i))) :
    IsCompact (piSubgroup U U : Set (Πʳ i, [G i, U i])) := by
  haveI : ∀ i, CompactSpace (U i : Set (G i)) :=
    fun i => isCompact_iff_compactSpace.mp (hUcompact i)
  have hrange : (piSubgroup U U : Set (Πʳ i, [G i, U i])) =
      Set.range (RestrictedProduct.structureMap G (fun i => (U i : Set (G i))) cofinite) := by
    rw [RestrictedProduct.range_structureMap]
    ext x
    simp only [SetLike.mem_coe, mem_piSubgroup, Set.mem_setOf_eq]
    rfl
  rw [hrange]
  exact isCompact_range RestrictedProduct.isEmbedding_structureMap.continuous

/-- A family of open subgroups inside the distinguished family, equal to it outside a finite set
of indices, cuts out a compact subgroup. -/
theorem isCompact_piSubgroup {K : Π i, Subgroup (G i)} (hKU : ∀ i, K i ≤ U i)
    (hKopen : ∀ i, IsOpen (K i : Set (G i))) (hS : {i | K i ≠ U i}.Finite)
    (hUcompact : ∀ i, IsCompact (U i : Set (G i))) :
    IsCompact (piSubgroup U K : Set (Πʳ i, [G i, U i])) :=
  (isCompact_piSubgroup_self hUcompact).of_isClosed_subset
    (Subgroup.isClosed_of_isOpen _ (isOpen_piSubgroup hKU hKopen hS)) (piSubgroup_mono hKU)

/-- The distinguished compact open subgroup, as a positive compact set. -/
def structurePositiveCompacts (hUcompact : ∀ i, IsCompact (U i : Set (G i))) :
    TopologicalSpace.PositiveCompacts (Πʳ i, [G i, U i]) where
  carrier := piSubgroup U U
  isCompact' := isCompact_piSubgroup_self hUcompact
  interior_nonempty' := by
    rw [(isOpen_piSubgroup (fun _ => le_rfl) (fun i => hUopen.out i) (by simp)).interior_eq]
    exact ⟨1, (piSubgroup U U).one_mem⟩

end Topology

/-! ## The local factors -/

section LocalFactors

variable {ι : Type*} {G : ι → Type*} [Π i, Group (G i)] [Π i, TopologicalSpace (G i)]
variable [∀ i, IsTopologicalGroup (G i)] [∀ i, MeasurableSpace (G i)] [∀ i, BorelSpace (G i)]
variable {U K : Π i, Subgroup (G i)}

/-- The local index times the local volume of the smaller subgroup is the local volume of the
larger one. -/
theorem relIndex_mul_measure_local (μloc : Π i, Measure (G i))
    [∀ i, (μloc i).IsMulLeftInvariant] (hKU : ∀ i, K i ≤ U i)
    (hKopen : ∀ i, IsOpen (K i : Set (G i))) (hUcompact : ∀ i, IsCompact (U i : Set (G i)))
    (i : ι) : ((K i).relIndex (U i) : ℝ≥0∞) * μloc i (K i) = μloc i (U i) := by
  haveI := finiteIndex_subgroupOf_of_isOpen (hKopen i) (hUcompact i)
  exact relIndex_mul_measure (hKU i) (hKopen i).measurableSet (μloc i)

omit [Π i, MeasurableSpace (G i)] [∀ i, BorelSpace (G i)] in
/-- The local index of an open subgroup in a compact subgroup is nonzero. -/
theorem relIndex_ne_zero (hKopen : ∀ i, IsOpen (K i : Set (G i)))
    (hUcompact : ∀ i, IsCompact (U i : Set (G i))) (i : ι) : (K i).relIndex (U i) ≠ 0 :=
  (finiteIndex_subgroupOf_of_isOpen (hKopen i) (hUcompact i)).index_ne_zero

/-- The local volume ratio is the inverse of the local index. -/
theorem measure_div_measure_eq_inv (μloc : Π i, Measure (G i))
    [∀ i, (μloc i).IsHaarMeasure] (hKU : ∀ i, K i ≤ U i)
    (hKopen : ∀ i, IsOpen (K i : Set (G i))) (hUcompact : ∀ i, IsCompact (U i : Set (G i)))
    (i : ι) : μloc i (K i) / μloc i (U i) = ((K i).relIndex (U i) : ℝ≥0∞)⁻¹ := by
  have hne : μloc i (K i) ≠ 0 := ((hKopen i).measure_pos (μloc i) ⟨1, (K i).one_mem⟩).ne'
  have htop : μloc i (K i) ≠ ⊤ :=
    (((hUcompact i).of_isClosed_subset (Subgroup.isClosed_of_isOpen _ (hKopen i))
      (hKU i)).measure_lt_top).ne
  have hn0 : ((K i).relIndex (U i) : ℝ≥0∞) ≠ 0 :=
    Nat.cast_ne_zero.mpr (relIndex_ne_zero hKopen hUcompact i)
  rw [← relIndex_mul_measure_local μloc hKU hKopen hUcompact i, ENNReal.div_eq_inv_mul,
    ENNReal.mul_inv (Or.inl hn0) (Or.inl (ENNReal.natCast_ne_top _)), mul_assoc,
    ENNReal.inv_mul_cancel hne htop, mul_one]

end LocalFactors

/-! ## The product formula for the measure -/

section MeasureFormula

variable {ι : Type*} {G : ι → Type*} [Π i, Group (G i)] [Π i, TopologicalSpace (G i)]
variable [∀ i, IsTopologicalGroup (G i)] {U K : Π i, Subgroup (G i)}
variable [hUopen : Fact (∀ i, IsOpen (U i : Set (G i)))]
variable [MeasurableSpace (Πʳ i, [G i, U i])] [BorelSpace (Πʳ i, [G i, U i])]

/-- The index of the cut-out subgroup in the distinguished one is the ratio of their measures,
for any left-invariant measure on the restricted product. -/
theorem relIndex_mul_measure_piSubgroup (μ : Measure (Πʳ i, [G i, U i]))
    [μ.IsMulLeftInvariant] (hKU : ∀ i, K i ≤ U i)
    (hKopen : ∀ i, IsOpen (K i : Set (G i))) (hS : {i | K i ≠ U i}.Finite)
    (hUcompact : ∀ i, IsCompact (U i : Set (G i))) :
    ((piSubgroup U K).relIndex (piSubgroup U U) : ℝ≥0∞) * μ (piSubgroup U K) =
      μ (piSubgroup U U) := by
  haveI := finiteIndex_subgroupOf_of_isOpen (isOpen_piSubgroup hKU hKopen hS)
    (isCompact_piSubgroup_self hUcompact)
  exact relIndex_mul_measure (piSubgroup_mono hKU)
    (isOpen_piSubgroup hKU hKopen hS).measurableSet μ

variable [∀ i, MeasurableSpace (G i)] [∀ i, BorelSpace (G i)]

/-- **Product formula for the measure of a product of compact open subgroups.** The measure of
the subgroup cut out by a family `K` of open subgroups, with `K i ≤ U i` at every index and
`K i = U i` outside a finite set, is the product of the local volume ratios times the measure of
the distinguished subgroup. The product is finite because almost all factors are one, and it does
not depend on the normalization of any of the measures. -/
theorem measure_restrictedProduct_pi (μ : Measure (Πʳ i, [G i, U i])) [μ.IsMulLeftInvariant]
    (μloc : Π i, Measure (G i)) [∀ i, (μloc i).IsHaarMeasure]
    (hKU : ∀ i, K i ≤ U i) (hKopen : ∀ i, IsOpen (K i : Set (G i)))
    (hS : {i | K i ≠ U i}.Finite) (hUcompact : ∀ i, IsCompact (U i : Set (G i))) :
    μ (piSubgroup U K) = (∏ᶠ i, μloc i (K i) / μloc i (U i)) * μ (piSubgroup U U) := by
  classical
  have hratio : ∀ i, μloc i (K i) / μloc i (U i) = ((K i).relIndex (U i) : ℝ≥0∞)⁻¹ :=
    measure_div_measure_eq_inv μloc hKU hKopen hUcompact
  have hsupp : Function.mulSupport (fun i => μloc i (K i) / μloc i (U i)) ⊆ hS.toFinset := by
    intro i hi
    refine hS.mem_toFinset.mpr fun hKi => hi ?_
    change μloc i (K i) / μloc i (U i) = 1
    rw [hratio i, hKi, Subgroup.relIndex_self, Nat.cast_one, inv_one]
  rw [finprod_eq_prod_of_mulSupport_subset _ hsupp]
  have hprod : (∏ i ∈ hS.toFinset, μloc i (K i) / μloc i (U i)) *
      ((piSubgroup U K).relIndex (piSubgroup U U) : ℝ≥0∞) = 1 := by
    rw [relIndex_piSubgroup_toFinset hKU hS, Nat.cast_prod, ← Finset.prod_mul_distrib]
    refine Finset.prod_eq_one fun i _ => ?_
    rw [hratio i]
    exact ENNReal.inv_mul_cancel (Nat.cast_ne_zero.mpr (relIndex_ne_zero hKopen hUcompact i))
      (ENNReal.natCast_ne_top _)
  calc μ (piSubgroup U K) = 1 * μ (piSubgroup U K) := (one_mul _).symm
    _ = (∏ i ∈ hS.toFinset, μloc i (K i) / μloc i (U i)) *
          (((piSubgroup U K).relIndex (piSubgroup U U) : ℝ≥0∞) * μ (piSubgroup U K)) := by
        rw [← hprod, mul_assoc]
    _ = (∏ i ∈ hS.toFinset, μloc i (K i) / μloc i (U i)) * μ (piSubgroup U U) := by
        rw [relIndex_mul_measure_piSubgroup μ hKU hKopen hS hUcompact]

end MeasureFormula

/-! ## The normalized Haar measure -/

section HaarMeasure

variable {ι : Type*} {G : ι → Type*} [Π i, Group (G i)] [Π i, TopologicalSpace (G i)]
variable [∀ i, IsTopologicalGroup (G i)] {U K : Π i, Subgroup (G i)}
variable [hUopen : Fact (∀ i, IsOpen (U i : Set (G i)))]
variable [MeasurableSpace (Πʳ i, [G i, U i])] [BorelSpace (Πʳ i, [G i, U i])]

/-- The Haar measure on a restricted product of topological groups with respect to compact open
subgroups, normalized so that the distinguished compact open subgroup has measure one. -/
def restrictedProductHaarMeasure (hUcompact : ∀ i, IsCompact (U i : Set (G i))) :
    Measure (Πʳ i, [G i, U i]) :=
  Measure.haarMeasure (structurePositiveCompacts hUcompact)

instance isHaarMeasure_restrictedProductHaarMeasure
    (hUcompact : ∀ i, IsCompact (U i : Set (G i))) :
    (restrictedProductHaarMeasure hUcompact).IsHaarMeasure :=
  Measure.isHaarMeasure_haarMeasure _

/-- The distinguished compact open subgroup has measure one. -/
@[simp]
theorem restrictedProductHaarMeasure_self (hUcompact : ∀ i, IsCompact (U i : Set (G i))) :
    restrictedProductHaarMeasure hUcompact (piSubgroup U U) = 1 :=
  Measure.haarMeasure_self

variable [∀ i, MeasurableSpace (G i)] [∀ i, BorelSpace (G i)]

/-- With the normalization that the distinguished compact open subgroup has measure one, the
measure of a product of compact open subgroups is exactly the product of the local ratios. -/
theorem restrictedProductHaarMeasure_piSubgroup
    (hUcompact : ∀ i, IsCompact (U i : Set (G i))) (μloc : Π i, Measure (G i))
    [∀ i, (μloc i).IsHaarMeasure] (hKU : ∀ i, K i ≤ U i)
    (hKopen : ∀ i, IsOpen (K i : Set (G i))) (hS : {i | K i ≠ U i}.Finite) :
    restrictedProductHaarMeasure hUcompact (piSubgroup U K) =
      ∏ᶠ i, μloc i (K i) / μloc i (U i) := by
  rw [measure_restrictedProduct_pi _ μloc hKU hKopen hS hUcompact,
    restrictedProductHaarMeasure_self, mul_one]

end HaarMeasure

end LeanCategories.ForMathlib
