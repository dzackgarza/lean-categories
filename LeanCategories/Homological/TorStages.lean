/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 License as described in the file LICENSE.
-/
module

public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.RingTheory.TensorProduct.DirectLimitFG
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
public import Mathlib.RingTheory.PrincipalIdealDomain
public import Mathlib.Algebra.EuclideanDomain.Int
public import Mathlib.LinearAlgebra.Dimension.Localization
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.CategoryTheory.Abelian.Projective.Resolution
public import Mathlib.Algebra.Homology.ShortComplex.Homology
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.RingTheory.Flat.Equalizer
public import Mathlib.CategoryTheory.Abelian.LeftDerived
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

@[expose] public section

/-!
# TorStages: genuine subgroup stages of a presented group

Card `E-HAT-3.A-6 / E-HAT-3.A-2` of the qualifying-exam corpus.  Source: Hatcher, *Algebraic
Topology*, Section 3.A, exercises 2 and 6 (printed p. 267).  Certificate:
new-qual-site `proofs/cards/TorStages.lean` at commit `16c09abaa4`.

LC-09 search record (queries run against the formalization corpus and local
Mathlib): the statements below are the certificate's own; Mathlib's
CategoryTheory.Tor supplies the derived-functor definition and no comparison
API, so the certificate is ported whole.

Provenance: ported from new-qual-site at commit `16c09abaa4`,
`proofs/cards/TorStages.lean`.
-/


open scoped BigOperators

/-!
# `E-HAT-3.A-6` / `E-HAT-3.A-2`: genuine subgroup stages of a presented group

For a presentation `f : K →ₗ[ℤ] F` of `A = F / range f` and a submodule `F' ≤ F`, the stage is
`A' = F' / (F' ⊓ range f)`, presented by `K' = comap f F' → F'`: its relations are exactly
`F' ⊓ range f`, since `map f (comap f F') = F' ⊓ range f`.

`stageMap` is the map `A' → A` induced by `F' ↪ F`, and `stageMap_injective` shows it is
injective — the point a bare sub-presentation does not give, since the cokernel of a
sub-presentation need not embed in `A`. Built with Mathlib's `Submodule.mapQ` and
`Submodule.ker_mapQ` and `Submodule.mkQ_map_self`: the kernel of `stageMap` is `p.map p.mkQ`
for `p` the stage's relations, which is `⊥`.

`stageRelMap`, `range_stageRelMap` and `stageIncl` present the stage and give the transition
maps, `stageMap_comp_stageIncl` the compatibility of the triangles into `A`.

For the filtered-colimit step of Exercise 4 of §3.A a stage must be a *direct summand* of `F`,
not merely a submodule: `rTensor_subtype_injective_of_retraction` is the criterion,
`rTensor_subtype_not_injective` certifies that an arbitrary submodule fails, and for the
cards' free `F` the summands are built from finite sets of basis vectors, which completes the
descent in `exists_stage_of_free`.
-/

namespace LeanCategories.Homological.TorStages

variable {K F : Type*} [AddCommGroup K] [AddCommGroup F]

/-- The stage's relations: those elements of `F'` that already lie in the range of the
presentation. -/
abbrev stageRel (f : K →ₗ[ℤ] F) (F' : Submodule ℤ F) : Submodule ℤ F' :=
  Submodule.comap F'.subtype (LinearMap.range f)

/-- The stage's relations are the relations of the sub-presentation `K' = comap f F' → F'`. -/
theorem map_stageRel (f : K →ₗ[ℤ] F) (F' : Submodule ℤ F) :
    Submodule.map F'.subtype (stageRel f F') = F' ⊓ LinearMap.range f := by
  rw [stageRel, Submodule.map_comap_eq, Submodule.range_subtype]

/-- The map from the stage `A' = F'/(F' ⊓ range f)` into `A = F/range f`. -/
noncomputable def stageMap (f : K →ₗ[ℤ] F) (F' : Submodule ℤ F) :
    F' ⧸ Submodule.comap F'.subtype (LinearMap.range f) →ₗ[ℤ] F ⧸ LinearMap.range f :=
  Submodule.mapQ _ (LinearMap.range f) F'.subtype le_rfl

/-- The stage embeds in `A`. By `Submodule.ker_mapQ` the kernel of `stageMap` is
`p.map p.mkQ` for `p` the stage's relations, and `Submodule.mkQ_map_self` is `map p.mkQ p = ⊥`. -/
theorem stageMap_injective (f : K →ₗ[ℤ] F) (F' : Submodule ℤ F) :
    Function.Injective (stageMap f F') := by
  rw [← LinearMap.ker_eq_bot, stageMap, Submodule.ker_mapQ]
  exact Submodule.mkQ_map_self _

/-! ## The stage's own presentation, and the transition maps

`stageRelMap f F' : comap f F' → F'` is the presentation of the stage: its range is
exactly `stageRel f F'`, so its cokernel is `A'`. For `F' ≤ F''` the inclusion of stages
`stageIncl` is induced by `F' ↪ F''`, and `stageMap_comp_stageIncl` says the triangles
`A' → A'' → A` and `A' → A` agree — the compatibility a directed system of stages needs.
-/

/-- The stage's presentation `K' = comap f F' → F'`. Its cokernel is the stage `A'`. -/
def stageRelMap (f : K →ₗ[ℤ] F) (F' : Submodule ℤ F) :
    Submodule.comap f F' →ₗ[ℤ] F' where
  toFun k := ⟨f k, k.2⟩
  map_add' x y := by ext; simp
  map_smul' c x := by ext; simp

/-- The stage's presentation has exactly the stage's relations as its range, so `A'` is its
cokernel. -/
theorem range_stageRelMap (f : K →ₗ[ℤ] F) (F' : Submodule ℤ F) :
    LinearMap.range (stageRelMap f F') = stageRel f F' := by
  ext x
  simp only [LinearMap.mem_range]
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨k, congrArg Subtype.val hk⟩
  · rintro ⟨k, hk⟩
    exact ⟨⟨k, Submodule.mem_comap.mpr (by rw [hk]; exact x.2)⟩, Subtype.ext hk⟩

/-- The stage's presentation composes to the ambient presentation: `F' ↪ F` after
`K' → F'` is `K' ↪ K` after `f`. -/
theorem subtype_comp_stageRelMap (f : K →ₗ[ℤ] F) (F' : Submodule ℤ F) :
    F'.subtype.comp (stageRelMap f F') = f.comp (Submodule.comap f F').subtype := by
  ext k
  rfl

/-- For `F' ≤ F''`, the inclusion of stages `A' → A''`, induced by `F' ↪ F''`. -/
noncomputable def stageIncl {f : K →ₗ[ℤ] F} {F' F'' : Submodule ℤ F} (h : F' ≤ F'') :
    F' ⧸ stageRel f F' →ₗ[ℤ] F'' ⧸ stageRel f F'' :=
  Submodule.mapQ (stageRel f F') (stageRel f F'') (Submodule.inclusion h) fun _ hx => hx

/-- The transition maps are compatible with the maps into `A`: the triangle
`A' → A'' → A` is `A' → A`. -/
theorem stageMap_comp_stageIncl {f : K →ₗ[ℤ] F} {F' F'' : Submodule ℤ F} (h : F' ≤ F'') :
    (stageMap f F'').comp (stageIncl h) = stageMap f F' := by
  apply LinearMap.ext
  intro x
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective (p := stageRel f F') x
  rfl

/-- The transition map of the identity inclusion is the identity: the stages carry a functor on
the poset of submodules of `F`, not just a family of maps. -/
theorem stageIncl_refl (f : K →ₗ[ℤ] F) (F' : Submodule ℤ F) :
    stageIncl (f := f) (le_refl F') = LinearMap.id := by
  apply LinearMap.ext
  intro x
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective (p := stageRel f F') x
  rw [LinearMap.id_apply]
  exact congrArg Submodule.Quotient.mk (Subtype.ext rfl)

/-- Transition maps compose: `A' → A'' → A'''` is the transition map of `F' ≤ F'''`. -/
theorem stageIncl_comp {f : K →ₗ[ℤ] F} {F' F'' F''' : Submodule ℤ F} (h : F' ≤ F'')
    (h' : F'' ≤ F''') :
    (stageIncl (f := f) h').comp (stageIncl (f := f) h) =
      stageIncl (f := f) (le_trans h h') := by
  apply LinearMap.ext
  intro x
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective (p := stageRel f F') x
  rw [LinearMap.comp_apply]
  exact congrArg Submodule.Quotient.mk (Subtype.ext rfl)

/-- A transition map is injective, since the composite into `A` is. -/
theorem stageIncl_injective {f : K →ₗ[ℤ] F} {F' F'' : Submodule ℤ F} (h : F' ≤ F'') :
    Function.Injective (stageIncl (f := f) h) := by
  intro x y hxy
  apply stageMap_injective f F'
  have hx := (DFunLike.congr_fun (stageMap_comp_stageIncl (f := f) h) x).symm
  have hy := (DFunLike.congr_fun (stageMap_comp_stageIncl (f := f) h) y).symm
  simp only [LinearMap.comp_apply, hx, hy, hxy]

/-! ## Exercise 4 of §3.A at the presentation level: what a stage has to be

The cards use "`Tor(A,B) ≅ colim_α Tor(A_α,B)`" over the finitely generated subgroups. In the
presentation-level model the content is: an element of `torKernel f` already vanishes at a
stage whose middle term is finitely generated. The reduction to finite support is
`TensorProduct.exists_of_fg`. The delicate point is that vanishing upstairs descends to the
stage only when `F'` is a *direct summand* of `F`: flatness of `F'` is the wrong hypothesis
and is not enough, and `rTensor_subtype_not_injective` certifies the failure. So the
obligation is to choose the stages among the direct summands of `F` — for the cards' free
middle term, the spans of finite subsets of a basis.
-/

/-- **The direct-summand hypothesis, isolated.** If `ρ` retracts `F' ↪ F`, then
`F' ⊗ B → F ⊗ B` is injective, so an element of `F' ⊗ B` that dies in `F ⊗ B` is already zero.

This is the hypothesis the stage construction needs, and it is *not* automatic for a
submodule: `rTensor_subtype_not_injective` below certifies that for `F = ℤ`, `F' = 2ℤ` and
`B = ℤ/2` the map `F' ⊗ B → F ⊗ B` is not injective, although `F` is free. The quotient
`F/F'` has torsion there. So the stages have to be direct summands of `F`, which for the
cards' free middle term means spans of finite subsets of a basis; an arbitrary finitely
generated `F'` will not do. -/
theorem rTensor_subtype_injective_of_retraction {B : Type*} [AddCommGroup B]
    (F' : Submodule ℤ F) (ρ : F →ₗ[ℤ] F') (hρ : ρ.comp F'.subtype = LinearMap.id) :
    Function.Injective (LinearMap.rTensor B F'.subtype) := by
  have hleft : ∀ w : TensorProduct ℤ F' B,
      (LinearMap.rTensor B ρ) (LinearMap.rTensor B F'.subtype w) = w := by
    intro w
    rw [← LinearMap.comp_apply, ← LinearMap.rTensor_comp, hρ]
    simp
  intro y z hyz
  calc y = (LinearMap.rTensor B ρ) (LinearMap.rTensor B F'.subtype y) := (hleft y).symm
    _ = (LinearMap.rTensor B ρ) (LinearMap.rTensor B F'.subtype z) := by rw [hyz]
    _ = z := hleft z

/-! ### The direct-summand hypothesis is sharp

A submodule that is not a direct summand really does break the stage step, even over a free
`F`. The certified counterexample below is `F = ℤ`, `F' = 2ℤ`, `B = ℤ/2`: the stage's
relations are `0`, so the stage would be `2ℤ` itself, but `2ℤ ⊗ ℤ/2 → ℤ ⊗ ℤ/2` kills the
generator `2 ⊗ 1` (which is `2 • (1 ⊗ 1)`, and `2 • 1 = 0` in `ℤ/2`) while `2ℤ ≅ ℤ` makes it a
nonzero element of `2ℤ ⊗ ℤ/2`. So `stageMap_injective` alone does not make an arbitrary
finitely generated `F'` a usable stage.
-/

/-- Multiplication by `2` on `ℤ`. -/
def mulByTwo : ℤ →ₗ[ℤ] ℤ where
  toFun r := 2 * r
  map_add' r s := by ring
  map_smul' c r := by
    show 2 * (c * r) = c * (2 * r)
    ring

theorem mulByTwo_injective : Function.Injective mulByTwo := by
  intro a b h
  simp only [mulByTwo, LinearMap.coe_mk, AddHom.coe_mk] at h
  omega

/-- `2ℤ`, as the range of multiplication by `2`. -/
abbrev TwoZ : Submodule ℤ ℤ := LinearMap.range mulByTwo

/-- `2ℤ` is isomorphic to `ℤ`. -/
noncomputable def twoZEquiv : ℤ ≃ₗ[ℤ] TwoZ :=
  LinearEquiv.ofInjective mulByTwo mulByTwo_injective

theorem twoZEquiv_one_val : (twoZEquiv 1 : ℤ) = 2 := rfl

/-- The generator `2 ⊗ 1` of `2ℤ ⊗ ℤ/2` is nonzero, since `2ℤ ≅ ℤ` and `ℤ ⊗ ℤ/2 ≅ ℤ/2`. -/
theorem twoZEquiv_one_tmul_ne_zero : (twoZEquiv 1 ⊗ₜ[ℤ] (1 : ZMod 2)) ≠ 0 := by
  intro h
  have hmap := congrArg
    (fun z => (TensorProduct.lid ℤ (ZMod 2))
      (TensorProduct.congr twoZEquiv.symm (LinearEquiv.refl ℤ (ZMod 2)) z)) h
  simp only [map_zero, TensorProduct.congr_tmul, LinearEquiv.symm_apply_apply,
    LinearEquiv.refl_apply, TensorProduct.lid_tmul, one_smul] at hmap
  exact absurd hmap (by decide : (1 : ZMod 2) ≠ 0)

/-- Its image `2 ⊗ 1` in `ℤ ⊗ ℤ/2` is zero: `2 ⊗ 1 = 2 • (1 ⊗ 1)`. -/
theorem twoZ_tmul_one_eq_zero : ((2 : ℤ) ⊗ₜ[ℤ] (1 : ZMod 2)) = 0 := by
  refine (TensorProduct.lid ℤ (ZMod 2)).injective ?_
  have h2 : ((2 : ℤ) • (1 : ZMod 2)) = 0 := by
    show ((2 : ℤ) : ZMod 2) = 0
    decide
  rw [show ((2 : ℤ) ⊗ₜ[ℤ] (1 : ZMod 2))
      = (2 : ℤ) • ((1 : ℤ) ⊗ₜ[ℤ] (1 : ZMod 2)) from by
    rw [TensorProduct.smul_tmul']
    norm_num]
  rw [map_smul, TensorProduct.lid_tmul, smul_smul, mul_one, h2, map_zero]

/-- **The counterexample.** `F' = 2ℤ` is not a direct summand of `F = ℤ`, and the stage step
fails: `F' ⊗ B → F ⊗ B` is not injective for `B = ℤ/2`. -/
theorem rTensor_subtype_not_injective :
    ¬ Function.Injective (LinearMap.rTensor (ZMod 2) (Submodule.subtype TwoZ)) := by
  intro hinj
  have h0 : LinearMap.rTensor (ZMod 2) (Submodule.subtype TwoZ)
      (twoZEquiv 1 ⊗ₜ[ℤ] (1 : ZMod 2)) = 0 := by
    rw [LinearMap.rTensor_tmul, Submodule.coe_subtype, twoZEquiv_one_val,
      twoZ_tmul_one_eq_zero]
  refine twoZEquiv_one_tmul_ne_zero (hinj ?_)
  rw [h0, map_zero]

/-- **Exercise 4 of §3.A at the presentation level, modulo the choice of a stage.** Let
`F' ≤ F` be a stage that is a direct summand of `F` (witnessed by the retraction `ρ`), let
`P ≤ comap f F'` be finitely generated, and let `u ∈ P ⊗ B` vanish under the presentation.
Then `u`'s class already vanishes in the *stage's* Tor, i.e. after both the inclusion
`P → comap f F'` and the stage presentation `stageRelMap f F'`.

Together with `TensorProduct.exists_of_fg` — which produces `P` and `u` for any class in
`torKernel f` — this is the whole content of the card's "the component of the class already
lies in some stage", once a finitely generated direct summand `F'` containing `f(P)` is
chosen. Producing that `F'` is the one remaining obligation; see `proofs/README.md`. -/
theorem exists_stage_witness_of_retraction {B : Type*} [AddCommGroup B]
    (f : K →ₗ[ℤ] F) (F' : Submodule ℤ F) (ρ : F →ₗ[ℤ] F')
    (hρ : ρ.comp F'.subtype = LinearMap.id) (P : Submodule ℤ K) (hle : P ≤ Submodule.comap f F')
    (u : TensorProduct ℤ P B) (hu : LinearMap.rTensor B (f.comp P.subtype) u = 0) :
    LinearMap.rTensor B (stageRelMap f F')
      (LinearMap.rTensor B (Submodule.inclusion hle) u) = 0 := by
  have hcomp : (F'.subtype.comp (stageRelMap f F')).comp (Submodule.inclusion hle)
      = f.comp P.subtype := by
    ext k
    rfl
  have h0 : LinearMap.rTensor B F'.subtype (LinearMap.rTensor B (stageRelMap f F')
      (LinearMap.rTensor B (Submodule.inclusion hle) u)) = 0 := by
    rw [← LinearMap.comp_apply, ← LinearMap.rTensor_comp, ← LinearMap.comp_apply,
      ← LinearMap.rTensor_comp, hcomp, hu]
  exact (rTensor_subtype_injective_of_retraction F' ρ hρ) (by rw [h0, map_zero])


/-! ### Choosing the stages: finitely generated direct summands of a free `F`

For the cards `F` is free, and there the missing choice of `F'` is available: the span of
*any finite set of basis vectors* is a direct summand of `F`, because discarding the
coordinates outside that finite set (`coordProj`) retracts the inclusion. So every finitely
generated `P ≤ K` sits inside a finitely generated direct summand of `F`
(`exists_fg_summand`), and with `exists_stage_witness_of_retraction` the descent of a Tor
class to its stage is complete (`exists_stage_of_free`).
-/

section FreeMiddleTerm

variable {ι : Type*}

/-- Discarding the coordinates of `b` outside the finite set `t`. -/
noncomputable def coordProj (b : Module.Basis ι ℤ F) (t : Finset ι) : F →ₗ[ℤ] F :=
  ∑ i ∈ t, ((Finsupp.lapply i).comp b.repr.toLinearMap).smulRight (b i)

theorem coordProj_apply (b : Module.Basis ι ℤ F) (t : Finset ι) (x : F) :
    coordProj b t x = ∑ i ∈ t, (b.repr x) i • b i := by
  simp [coordProj]

/-- The span of the basis vectors indexed by the finite set `t`. -/
noncomputable abbrev coordSpan (b : Module.Basis ι ℤ F) (t : Finset ι) : Submodule ℤ F :=
  Submodule.span ℤ (b '' (t : Set ι))

/-- A combination of the basis vectors in `t` uses only coordinates in `t`. -/
theorem support_subset_coordSpan (b : Module.Basis ι ℤ F) (t : Finset ι) {y : F}
    (hy : y ∈ coordSpan b t) : (b.repr y).support ⊆ t := by
  have hle : coordSpan b t ≤
      Submodule.comap b.repr.toLinearMap (Finsupp.supported ℤ ℤ (t : Set ι)) := by
    rw [coordSpan, Submodule.span_le]
    rintro _ ⟨i, hi, rfl⟩
    refine Submodule.mem_comap.mpr ?_
    rw [show b.repr.toLinearMap (b i) = b.repr (b i) from rfl, Module.Basis.repr_self,
      Finsupp.mem_supported]
    exact Finset.Subset.trans Finsupp.support_single_subset (by simpa using hi)
  exact hle hy

/-- Discarding the other coordinates fixes the span of `t` pointwise. -/
theorem coordProj_eq_self (b : Module.Basis ι ℤ F) (t : Finset ι) {y : F}
    (hy : y ∈ coordSpan b t) : coordProj b t y = y := by
  rw [coordProj_apply]
  conv_rhs => rw [← b.linearCombination_repr y, Finsupp.linearCombination_apply, Finsupp.sum]
  exact (Finset.sum_subset (support_subset_coordSpan b t hy) fun i _ hi => by
    rw [Finsupp.notMem_support_iff.mp hi, zero_smul]).symm

/-- The retraction of `F` onto the span of the basis vectors in `t`. -/
noncomputable def coordRetract (b : Module.Basis ι ℤ F) (t : Finset ι) :
    F →ₗ[ℤ] coordSpan b t :=
  (coordProj b t).codRestrict _ fun x => by
    rw [coordProj_apply]
    exact Submodule.sum_mem _ fun i hi =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, hi, rfl⟩)

/-- The span of finitely many basis vectors is a direct summand of `F`. -/
theorem coordRetract_comp_subtype (b : Module.Basis ι ℤ F) (t : Finset ι) :
    (coordRetract b t).comp (coordSpan b t).subtype = LinearMap.id := by
  ext y
  exact coordProj_eq_self b t y.2

theorem coordSpan_fg (b : Module.Basis ι ℤ F) (t : Finset ι) : (coordSpan b t).FG := by
  classical
  have h : ((t.image b : Finset F) : Set F) = b '' (t : Set ι) := by
    simp only [Finset.coe_image]
  rw [coordSpan, ← h]
  exact Submodule.fg_span (t.image b).finite_toSet

/-- **Every finitely generated `P ≤ K` lies in a finitely generated direct summand of the
free module `F`.** Take the union of the supports of the images of a finite generating set of
`P`, and the span of the corresponding basis vectors. -/
theorem exists_fg_summand (b : Module.Basis ι ℤ F) (f : K →ₗ[ℤ] F) (P : Submodule ℤ K)
    (hP : P.FG) :
    ∃ (F' : Submodule ℤ F) (_ : F'.FG) (ρ : F →ₗ[ℤ] F')
      (_ : ρ.comp F'.subtype = LinearMap.id), Submodule.map f P ≤ F' := by
  classical
  obtain ⟨s, hsf, hs⟩ := Submodule.fg_def.mp hP
  have hs' : Submodule.span ℤ (((hsf.toFinset : Finset K) : Set K)) = P := by
    rw [hsf.coe_toFinset]
    exact hs
  refine ⟨coordSpan b (hsf.toFinset.biUnion fun k => (b.repr (f k)).support),
    coordSpan_fg b _, coordRetract b _, coordRetract_comp_subtype b _, ?_⟩
  rw [← hs', Submodule.map_span, Submodule.span_le]
  rintro _ ⟨k, hk, rfl⟩
  rw [← b.linearCombination_repr (f k), Finsupp.linearCombination_apply, Finsupp.sum]
  exact Submodule.sum_mem _ fun i hi =>
    Submodule.smul_mem _ _ (Submodule.subset_span
      ⟨i, Finset.subset_biUnion_of_mem _ hk hi, rfl⟩)

/-- **The stage is a finitely generated subgroup of `A`.** `stageMap` is injective, and its
range is the image of `F'` under the quotient map, so the stage is a quotient of the finitely
generated `F'`. This is the finite-generation claim the cards make about `A_α`. -/
theorem stage_range_fg (f : K →ₗ[ℤ] F) {F' : Submodule ℤ F} (hF' : F'.FG) :
    (LinearMap.range (stageMap f F')).FG := by
  rw [stageMap, Submodule.range_mapQ, Submodule.range_subtype]
  exact hF'.map (LinearMap.range f).mkQ

/-- The stage's group is a finitely generated `ℤ`-module, which is the hypothesis the structure
theorem consumes. -/
theorem stage_finite (b : Module.Basis ι ℤ F) (f : K →ₗ[ℤ] F) (t : Finset ι) :
    Module.Finite ℤ (coordSpan b t ⧸ stageRel f (coordSpan b t)) := by
  haveI : Module.Finite ℤ (coordSpan b t) :=
    Module.Finite.of_fg (coordSpan_fg b t)
  infer_instance

/-- **The stages cover `A`.** Every element of `A = F ⧸ range f` lies in the image of the stage
belonging to some finitely generated `F'` — namely `span {x}` for any lift `x`. With `stageIncl`
this is the identification `A = ⋃_α A_α` that the cards' direct-limit step starts from.

The covering stage need not be a direct summand; that extra condition is what the *Tor* descent
of `exists_stage_witness_of_retraction` requires, and `exists_fg_summand` supplies it
separately. -/
theorem exists_stage_containing (f : K →ₗ[ℤ] F) (a : F ⧸ LinearMap.range f) :
    ∃ (F' : Submodule ℤ F), F'.FG ∧ a ∈ LinearMap.range (stageMap f F') := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective (p := LinearMap.range f) a
  refine ⟨Submodule.span ℤ {x}, Submodule.fg_span_singleton x, ?_⟩
  simp only [LinearMap.mem_range]
  exact ⟨Submodule.Quotient.mk (Subtype.mk x (Submodule.mem_span_singleton_self x)), by
    simp [stageMap, Submodule.mapQ_apply]⟩

/-- **Exercise 4 of §3.A, completed for a free middle term.** With `F` free, every element of
the presentation-level `torKernel f` is carried by the `Tor` of a stage `K' = comap f F' → F'`
whose middle term is a finitely generated direct summand of `F`, and it already vanishes at
that stage. Casting out through `stageMap_injective`, the stage's `A'` is a finitely generated
subgroup of `A`, so this is the card's "the component of the class already lies in some
stage". -/
theorem exists_stage_of_free {B : Type*} [AddCommGroup B] (b : Module.Basis ι ℤ F)
    (f : K →ₗ[ℤ] F) {x : TensorProduct ℤ K B} (hx : LinearMap.rTensor B f x = 0) :
    ∃ (F' : Submodule ℤ F) (_ : F'.FG) (ρ : F →ₗ[ℤ] F')
      (_ : ρ.comp F'.subtype = LinearMap.id)
      (t : TensorProduct ℤ (Submodule.comap f F') B),
      LinearMap.rTensor B (Submodule.comap f F').subtype t = x ∧
        LinearMap.rTensor B (stageRelMap f F') t = 0 := by
  classical
  obtain ⟨P, hP, u, hu⟩ := TensorProduct.exists_of_fg x
  have hu0 : LinearMap.rTensor B (f.comp P.subtype) u = 0 := by
    rw [LinearMap.rTensor_comp, LinearMap.comp_apply, hu, hx]
  obtain ⟨F', hF', ρ, hρ, hle'⟩ := exists_fg_summand (K := K) b f P hP
  have hle : P ≤ Submodule.comap f F' := Submodule.map_le_iff_le_comap.mp hle'
  exact ⟨F', hF', ρ, hρ, LinearMap.rTensor B (Submodule.inclusion hle) u,
    by
      rw [← LinearMap.comp_apply, ← LinearMap.rTensor_comp,
        Submodule.subtype_comp_inclusion P _ hle]
      exact hu,
    exists_stage_witness_of_retraction f F' ρ hρ P hle u hu0⟩

/-- **The projectivity obligation, discharged for the finitely generated case.** A submodule of a
torsion-free `ℤ`-module is torsion-free, and a finitely generated torsion-free module over `ℤ` is
free (`Module.free_of_finite_type_torsion_free'`, `LinearAlgebra/FreeModule/PID.lean`), hence
projective (`Module.Projective.of_free`). So for the stages the cards use — `F` free, `K' = comap f
F'` finitely generated — the middle term of the two-term resolution is projective with no extra
hypothesis.

Scope, stated honestly: this discharges the projectivity obligation for the finitely generated
stages the cards use, and **not** for an arbitrary-rank kernel. The pinned tree's two relevant
results both carry that limitation: `Module.free_of_finite_type_torsion_free'`
(`LinearAlgebra/FreeModule/PID.lean`, l.387) requires `Module.Finite`, and `Submodule.basisOfPid`
requires a finite-indexed ambient basis. Nothing in the pinned tree makes an arbitrary submodule of
a free `ℤ`-module free, so the general two-term bridge stays conditional on projectivity of the
relation module — or on using the maintained full projective resolution — rather than silently
treating every kernel of an injective map into a free module as free. -/
theorem projective_comap_of_fg {F : Type*} [AddCommGroup F] [Module.IsTorsionFree ℤ F]
    (K' : Submodule ℤ F) [Module.Finite ℤ K'] : Module.Projective ℤ K' := by
  have : Module.IsTorsionFree ℤ K' :=
    Function.Injective.moduleIsTorsionFree (Submodule.subtype K')
      (fun _ _ h => Subtype.ext h) fun _ _ => rfl
  exact Module.Projective.of_free

end FreeMiddleTerm

end LeanCategories.Homological.TorStages

