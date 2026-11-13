/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 License as described in the file LICENSE.
-/
module

public import Mathlib.RingTheory.Flat.Equalizer
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.Algebra.Exact
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.CategoryTheory.Monoidal.Tor
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.LinearAlgebra.TensorProduct.Prod
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
public import Mathlib.CategoryTheory.Abelian.LeftDerived
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

@[expose] public section

/-!
# TorReductions: the Tor reductions at the presentation level

Card `E-HAT-3.A-6 / E-HAT-3.A-2` of the qualifying-exam corpus.  Source: Hatcher, *Algebraic
Topology*, Section 3.A, exercises 2 and 6 (printed p. 267).  Certificate:
new-qual-site `proofs/cards/TorReductions.lean` at commit `16c09abaa4`.

LC-09 search record (queries run against the formalization corpus and local
Mathlib): the statements below are the certificate's own; Mathlib's
CategoryTheory.Tor supplies the derived-functor definition and no comparison
API, so the certificate is ported whole.

Provenance: ported from new-qual-site at commit `16c09abaa4`,
`proofs/cards/TorReductions.lean`.
-/


/-!
# `E-HAT-3.A-6`: the Tor reductions, at the presentation level

Hatcher, *Algebraic Topology*, §3.A defines `Tor(H, G)` as the homology of `F ⊗ G` for a
free resolution `F` of `H` (Lemma 3A.2 shows the choice of resolution does not matter) and
collects the computational rules in Proposition 3A.5:

1. `Tor(A, B) ≅ Tor(B, A)`
2. `Tor(⊕ i, A i, B) ≅ ⊕ i, Tor(A i, B)`
3. `Tor(A, B) = 0` if `A` or `B` is free, or more generally torsion-free
4. `Tor(A, B) ≅ Tor(T(A), B)` for the torsion subgroup `T(A)`
5. `Tor(ℤₙ, A) ≅ ker(A --n--> A)`
6. the long exact sequence of a short exact sequence in either variable

The card cites these items by number. What this file certifies, with no hypothesis beyond
`AddCommGroup`, is the part of the reduction that Mathlib already supplies or that is
immediate from the definitions:

* `torKernel`: the presentation-level group `ker(f ⊗ id_B)` of a presentation `f : K →ₗ F`,
  which is Hatcher's `Tor` for that resolution;
* `torKernel_eq_bot_of_subsingleton`: the free case of item (3) — if the kernel of the
  presentation is trivial (so the presented group is free) then `Tor` vanishes;
* `torsionBy_eq_ker`: `Submodule.torsionBy ℤ B n` is the kernel of multiplication by `n`,
  which is the group on the right-hand side of item (5);
* `flat_of_torsionFree`: every torsion-free `ℤ`-module is flat, the hypothesis behind the
  "more generally torsion-free" clause of item (3) and behind the step
  `Tor(A_p, B) ≅ Tor(A_p, B_p)` of the card. This is not reproved: `ℤ` is a Dedekind
  domain and Mathlib's `RingTheory/Flat/TorsionFree.lean` carries the instance
  `IsTorsionFree R M → Flat R M`;
* `rTensor_injective_of_flat`: Mathlib's flatness form of item (6), that tensoring with a
  flat module preserves injectivity, which is what makes the connecting map of item (6)
  vanish for a flat quotient.

Not formalized here, and cited on the card by number: the comparison theorem making `Tor`
independent of the resolution (Lemma 3A.2), additivity (item (2)), the reduction to the
torsion subgroup (item (4)), the identification `Tor(ℤₙ, B) ≅ B[n]` (item (5)) and the
commutation with direct limits (Exercise 4 of §3.A). The first of these is the obstruction:
`CategoryTheory.Tor` in Mathlib has no long exact sequence or comparison API, and the
identification in item (5) runs through `TensorProduct.lid`, whose `smul` is the
`DistribMulAction` one while `AddCommGroup` supplies the `ZSMul` one, so that statement has
to be set up with a single `SMul ℤ _` instance before it can be formalized.
-/

namespace LeanCategories.Homological.TorReductions

open TensorProduct

/-- Multiplication by an integer, as an endomorphism of `ℤ`. -/
def mulByInt (n : ℤ) : ℤ →ₗ[ℤ] ℤ where
  toFun r := n * r
  map_add' r s := by ring
  map_smul' c r := by
    show n * (c * r) = c * (n * r)
    ring

@[simp]
theorem mulByInt_apply (n r : ℤ) : mulByInt n r = n * r := rfl

variable {B : Type*} [AddCommGroup B]

/-- The presentation-level `Tor`: for a presentation `f : K →ₗ[ℤ] F` and a group `B`, the
kernel of `f ⊗ id_B`. -/
def torKernel {K F : Type*} [AddCommGroup K] [AddCommGroup F] (f : K →ₗ[ℤ] F) :=
  (f.rTensor B).ker

/-- Hatcher, Proposition 3A.5(3), the free case at the presentation level: a presentation
whose kernel is trivial presents a free group, and then `Tor` vanishes. -/
theorem torKernel_eq_bot_of_subsingleton {K F : Type*} [AddCommGroup K] [AddCommGroup F]
    [Subsingleton K] (f : K →ₗ[ℤ] F) : torKernel (B := B) f = ⊥ :=
  Subsingleton.elim _ _

/-- Hatcher, Proposition 3A.5(5), the group on the right: the `n`-torsion of `B` is the
kernel of multiplication by `n`. -/
theorem torsionBy_eq_ker (n : ℤ) :
    Submodule.torsionBy ℤ B n = (DistribSMul.toLinearMap ℤ B n).ker := rfl

/-- Hatcher, Proposition 3A.5(3), hypothesis: a torsion-free `ℤ`-module is flat. Reused from
Mathlib's Dedekind-domain instance rather than reproved. -/
theorem flat_of_torsionFree {M : Type*} [AddCommGroup M] [Module.IsTorsionFree ℤ M] :
    Module.Flat ℤ M :=
  inferInstance

/-- Hatcher, Proposition 3A.5(6), the flatness form: tensoring with a flat module preserves
injectivity, so a flat quotient kills the connecting map. Reused from Mathlib. -/
theorem rTensor_injective_of_flat {M N P : Type*} [AddCommGroup M] [AddCommGroup N]
    [AddCommGroup P] [Module.Flat ℤ M] (f : N →ₗ[ℤ] P) (hf : Function.Injective f) :
    Function.Injective (LinearMap.rTensor M f) :=
  Module.Flat.rTensor_preserves_injective_linearMap f hf

/-- `E-HAT-3.A-2`: the quotient by the torsion subgroup is torsion-free, which is the
hypothesis that makes `A/T(A)` flat and kills the connecting map of the Tor sequence for
`(T(A), A, A/T(A))`. Reused from Mathlib's `Submodule.torsion_eq_bot`. -/
theorem torsionFree_quotient_torsion (M : Type*) [AddCommGroup M] :
    Module.IsTorsionFree ℤ (M ⧸ Submodule.torsion ℤ M) :=
  inferInstance

/-- Consequece of the previous lemma and `flat_of_torsionFree`: the quotient of an abelian
group by its torsion subgroup is flat over `ℤ`. -/
theorem flat_quotient_torsion (M : Type*) [AddCommGroup M] :
    Module.Flat ℤ (M ⧸ Submodule.torsion ℤ M) :=
  @flat_of_torsionFree (M ⧸ Submodule.torsion ℤ M) _ (torsionFree_quotient_torsion M)

/-- `E-HAT-3.A-2`, exercise 5's first ingredient: a torsion-free `ℤ`-module spanned by a
finite family is free. Reused from Mathlib's principal-ideal-domain result
`Module.free_of_finite_type_torsion_free`; the finiteness hypothesis is kept explicit as a
`Finite` index type and a spanning family. -/
theorem free_of_finite_torsionFree {M : Type*} [AddCommGroup M]
    [Module.IsTorsionFree ℤ M] {ι : Type*} [Finite ι] {s : ι → M}
    (hs : Submodule.span ℤ (Set.range s) = ⊤) : Module.Free ℤ M :=
  Module.free_of_finite_type_torsion_free (R := ℤ) hs

/-- Under `ℤ ⊗ B ≅ B`, tensoring `n · id` with `id_B` is multiplication by `n` on `B`. -/
theorem lid_rTensor_mulByInt (n : ℤ) (x : TensorProduct ℤ ℤ B) :
    (TensorProduct.lid ℤ B) ((mulByInt n).rTensor B x) =
      (DistribSMul.toLinearMap ℤ B n) ((TensorProduct.lid ℤ B) x) := by
  have key :
      (TensorProduct.lid ℤ B).toLinearMap.comp ((mulByInt n).rTensor B) =
        (DistribSMul.toLinearMap ℤ B n).comp (TensorProduct.lid ℤ B).toLinearMap := by
    refine LinearMap.ext fun y => ?_
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul r b =>
        simp only [LinearMap.comp_apply, LinearMap.rTensor_tmul, mulByInt_apply,
          TensorProduct.lid_tmul, DistribSMul.toLinearMap_apply]
        exact mul_smul n r b
    | add y z hy hz => simp only [map_add, hy, hz]
  simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe] using congrArg (fun g => g x) key

/-- Hatcher, Proposition 3A.5(5) at the presentation level: the kernel of `(n · id) ⊗ id_B`
inside `ℤ ⊗ B` is carried by `ℤ ⊗ B ≅ B` onto the `n`-torsion of `B`, that is,
`Tor(ℤ/n, B) ≅ B[n]` for this resolution. -/
theorem map_torKernel_mulByInt (n : ℤ) :
    (torKernel (B := B) (mulByInt n)).map (TensorProduct.lid ℤ B).toLinearMap =
      Submodule.torsionBy ℤ B n := by
  ext b
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hx' : (mulByInt n).rTensor B x = 0 := hx
    have h := lid_rTensor_mulByInt (B := B) n x
    rw [hx', map_zero] at h
    exact (Submodule.mem_torsionBy_iff n _).mpr h.symm
  · intro hb
    have hb' : (DistribSMul.toLinearMap ℤ B n) b = 0 :=
      (Submodule.mem_torsionBy_iff n b).mp hb
    refine ⟨(TensorProduct.lid ℤ B).symm b, ?_, ?_⟩
    · have h1 : (TensorProduct.lid ℤ B) ((mulByInt n).rTensor B ((TensorProduct.lid ℤ B).symm b)) =
      0 := by
        rw [lid_rTensor_mulByInt, LinearEquiv.apply_symm_apply, hb']
      exact (TensorProduct.lid ℤ B).injective (by rw [h1, map_zero])
    · exact LinearEquiv.apply_symm_apply (TensorProduct.lid ℤ B) b

/-- If `p • x = 0` forces `x = 0` then `p^k • x = 0` does. -/
theorem eq_zero_of_pow_smul_eq_zero {C : Type*} [AddCommGroup C] {p : ℤ}
    (h : ∀ x : C, p • x = 0 → x = 0) (k : ℕ) : ∀ x : C, p ^ k • x = 0 → x = 0 := by
  induction k with
  | zero => intro x hx; simpa using hx
  | succ k ih =>
      intro x hx
      rw [pow_succ, ← smul_smul] at hx
      exact h x (ih (p • x) hx)

/-- The form the card uses to kill the connecting map: if `C` has no `p`-torsion then
`C[p^k] = 0` for every `k`, and so `Tor(ℤ/p^k, C) = 0` by the identification above. This is
the correct hypothesis in that step: `B/B_p` has no `p`-torsion, but it is *not* torsion-free
(for `p = 2`, `B = ℤ/2 ⊕ ℤ/3` gives `B/B_2 = ℤ/3`). -/
theorem torsionBy_pow_eq_bot_of_no_p_torsion {C : Type*} [AddCommGroup C] {p : ℕ}
    (h : Submodule.torsionBy ℤ C (p : ℤ) = ⊥) (k : ℕ) :
    Submodule.torsionBy ℤ C ((p : ℤ) ^ k) = ⊥ := by
  have h' : ∀ x : C, (p : ℤ) • x = 0 → x = 0 := by
    intro x hx
    have hx' : x ∈ Submodule.torsionBy ℤ C (p : ℤ) :=
      (Submodule.mem_torsionBy_iff (p : ℤ) x).mpr hx
    rwa [h, Submodule.mem_bot] at hx'
  refine le_antisymm ?_ bot_le
  intro x hx
  rw [Submodule.mem_bot]
  exact eq_zero_of_pow_smul_eq_zero h' k x ((Submodule.mem_torsionBy_iff ((p : ℤ) ^ k) x).mp hx)

/-- The premise the card uses, with the hypothesis made explicit. If `P` is a subgroup
containing exactly the elements killed by some power of `p` — the `p`-primary torsion
subgroup `B_p` — then `P` is saturated for multiplication by `p`, which says precisely that
the quotient `B/P` has no `p`-torsion: `p • [x] = 0` means `p • x ∈ P`, hence `x ∈ P`, hence
`[x] = 0`.

This is the correct premise in that step and it is strictly weaker than torsion-freeness:
for `p = 2` and `B = ℤ/2 ⊕ ℤ/3` the quotient `B/B_2 = ℤ/3` is not torsion-free, but it has
no `2`-torsion. Rule (3) of Hatcher's Proposition 3A.5 cannot be applied to it; rule (5)
can, and that is what the card now does. -/
theorem mem_of_p_smul_mem_of_pPrimary {B : Type*} [AddCommGroup B] {p : ℤ}
    {P : Submodule ℤ B} (hP : ∀ x : B, x ∈ P ↔ ∃ k : ℕ, p ^ k • x = 0) {x : B}
    (hx : p • x ∈ P) : x ∈ P := by
  obtain ⟨k, hk⟩ := (hP (p • x)).mp hx
  exact (hP x).mpr ⟨k + 1, by rw [pow_succ, ← smul_smul]; exact hk⟩

/-- Hatcher, Proposition 3A.5(2), the computation: tensoring a product map with `id_B`
commutes with the distributivity isomorphism of `TensorProduct.prodLeft`. This is the
mathematical content of additivity at the presentation level. -/
theorem prodLeft_comp_rTensor {K₁ K₂ F₁ F₂ : Type*} [AddCommGroup K₁] [AddCommGroup K₂]
    [AddCommGroup F₁] [AddCommGroup F₂] (f₁ : K₁ →ₗ[ℤ] F₁) (f₂ : K₂ →ₗ[ℤ] F₂) :
    (TensorProduct.prodLeft ℤ ℤ F₁ F₂ B).toLinearMap.comp ((f₁.prodMap f₂).rTensor B) =
      ((f₁.rTensor B).prodMap (f₂.rTensor B)).comp
        (TensorProduct.prodLeft ℤ ℤ K₁ K₂ B).toLinearMap := by
  refine LinearMap.ext fun x => ?_
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero, Prod.mk_zero_zero]
  | tmul k b => obtain ⟨k₁, k₂⟩ := k; simp [TensorProduct.prodLeft_tmul]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- Hatcher, Proposition 3A.5(2) at the presentation level: the presentation of a direct
sum is the direct sum of the presentations, so the presentation-level `Tor` splits. Here
`torKernel (f₁ ⊕ f₂)` is the kernel of `(f₁ ⊕ f₂) ⊗ id_B` inside `(K₁ × K₂) ⊗ B`, and the
statement says that the distributivity isomorphism
`TensorProduct.prodLeft` carries it onto `Tor(f₁) × Tor(f₂)`.

The proof avoids the `.symm` of `prodLeft` on arbitrary elements — which is where the
earlier attempt stalled, because `prodLeft_tmul` and `apply_symm_apply` are available in
different coercion shapes — by rewriting the kernel as a `comap` and mapping it forward;
`Submodule.map_comap_eq_self` only needs `prodLeft` to be onto its kernel, and the whole
element-level content is the composition identity `prodLeft_comp_rTensor`. -/
theorem map_prodLeft_torKernel {K₁ K₂ F₁ F₂ : Type*} [AddCommGroup K₁] [AddCommGroup K₂]
    [AddCommGroup F₁] [AddCommGroup F₂] (f₁ : K₁ →ₗ[ℤ] F₁) (f₂ : K₂ →ₗ[ℤ] F₂) :
    (torKernel (B := B) (f₁.prodMap f₂)).map
        (TensorProduct.prodLeft ℤ ℤ K₁ K₂ B).toLinearMap =
      (torKernel (B := B) f₁).prod (torKernel (B := B) f₂) := by
  have key := prodLeft_comp_rTensor (B := B) f₁ f₂
  have hcomap : LinearMap.ker ((f₁.prodMap f₂).rTensor B)
      = (LinearMap.ker ((f₁.rTensor B).prodMap (f₂.rTensor B))).comap
          (TensorProduct.prodLeft ℤ ℤ K₁ K₂ B).toLinearMap := by
    ext x
    rw [Submodule.mem_comap, LinearMap.mem_ker, LinearMap.mem_ker]
    have h := LinearMap.congr_fun key x
    simp only [LinearMap.comp_apply] at h
    rw [← h]
    constructor
    · intro hx; rw [hx, map_zero]
    · intro hx
      exact (TensorProduct.prodLeft ℤ ℤ F₁ F₂ B).injective (by simpa using hx)
  simp only [torKernel]
  have hside : ((LinearMap.rTensor B f₁).prodMap (f₂.rTensor B)).ker ≤
      (TensorProduct.prodLeft ℤ ℤ K₁ K₂ B).toLinearMap.range := by
    intro y _
    exact ⟨(TensorProduct.prodLeft ℤ ℤ K₁ K₂ B).symm y, LinearEquiv.apply_symm_apply _ y⟩
  rw [hcomap, Submodule.map_comap_eq_self hside, LinearMap.ker_prodMap]

/-! ## The filtered-colimit passage (Exercise 4 of §3.A): still open

With additivity proved, the remaining step shared by `E-HAT-3.A-6` and `E-HAT-3.A-2` is that
`Tor` commutes with the filtered colimit of the finitely generated subgroups of a torsion-free
group, and with the directed union of the `p`-primary subgroups in `A_p = colim A_{p,α}`. That
needs `⊗` commuting with filtered colimits of abelian groups together with additivity; it is
not proved here and is listed as an obligation in `proofs/README.md`. -/

/-- The vanishing transfers to the finite stage, which is the point of the Tor passage: for a
flat `F` — in the cards `F` is the free middle term of the presentation — the inclusion
`B' ≤ B` induces an injection `F ⊗ B' → F ⊗ B`, so a finite sum that vanishes in `F ⊗ B`
vanishes already in `F ⊗ B'`. Without this, a finitely supported tensor element would only
show that its image vanishes outside the finite stage.

Reused from Mathlib's `Module.Flat.lTensor_preserves_injective_linearMap` applied to
`Submodule.subtype`; nothing is rebuilt. -/
theorem lTensor_subtype_injective_of_flat {F B : Type*} [AddCommGroup F] [AddCommGroup B]
    [Module.Flat ℤ F] (B' : Submodule ℤ B) :
    Function.Injective (LinearMap.lTensor F B'.subtype) :=
  Module.Flat.lTensor_preserves_injective_linearMap _ B'.subtype_injective

/-- The Tor passage the cards use, in the presentation-level model: every element of
`ker (f ⊗ id_B)` already comes from the Tor of a *finitely generated sub-presentation*
`P ≤ K`, together with the witness that its image vanishes there. This is the statement that
lets `E-HAT-3.A-6` say "the component of the class already lies in some stage" and that
`E-HAT-3.A-2` uses when it writes a torsion-free group as the directed union of its finitely
generated subgroups.

The finite support comes from Mathlib's `TensorProduct.exists_of_fg` (pinned
`RingTheory/TensorProduct/DirectLimitFG.lean`), and the vanishing at the stage is
functoriality of `rTensor` (`rTensor_comp`), not a descent argument: the element already
vanishes, and the stage inclusion is a tensor of linear maps. -/
theorem exists_fg_stage {K F B : Type*} [AddCommGroup K] [AddCommGroup F] [AddCommGroup B]
    (f : K →ₗ[ℤ] F) {x : TensorProduct ℤ K B} (hx : (LinearMap.rTensor B f) x = 0) :
    ∃ (P : Submodule ℤ K) (_ : P.FG) (t : TensorProduct ℤ P B),
      (LinearMap.rTensor B P.subtype) t = x ∧
        (LinearMap.rTensor B (f.comp P.subtype)) t = 0 := by
  obtain ⟨P, hP, t, ht⟩ := TensorProduct.exists_of_fg x
  refine ⟨P, hP, t, ht, ?_⟩
  rw [LinearMap.rTensor_comp, LinearMap.comp_apply, ht, hx]

/-- **`E-HAT-3.A-2`, the vanishing direction, at the presentation level.** Let `f : K →ₗ[ℤ] F` be
  the
relation map of a genuine two-term free resolution — injective, with `F` free — and suppose the
quotient `A = F ⧸ range f` is flat. Then the presentation-level kernel vanishes: `f ⊗ id_B` is
injective for every `B`.

This is `LinearMap.lTensor_injective_of_exact_of_flat` applied to the short exact sequence
`0 → K → F → A → 0` (the quotient map is the surjection, `range f` its kernel by
`Submodule.ker_mkQ`), transported from `lTensor` to the `rTensor` factor order that
`torKernel` uses by `LinearMap.lTensor_inj_iff_rTensor_inj`. No connecting map and no snake
lemma is invoked directly: that theory is inside the maintained lemma. -/
theorem rTensor_injective_of_flat_cokernel {K F B : Type*} [AddCommGroup K] [AddCommGroup F]
    [AddCommGroup B] (f : K →ₗ[ℤ] F) (hf : Function.Injective f)
    [Module.Flat ℤ (F ⧸ LinearMap.range f)] :
    Function.Injective (LinearMap.rTensor B f) := by
  have hex : Function.Exact f (LinearMap.range f).mkQ := fun x => by
    simp [Submodule.mkQ_apply, LinearMap.mem_range]
  have hL : Function.Injective (LinearMap.lTensor B f) :=
    LinearMap.lTensor_injective_of_exact_of_flat (LinearMap.range f).mkQ
      (Submodule.mkQ_surjective _) f hf hex B
  exact (LinearMap.lTensor_inj_iff_rTensor_inj B f).mp hL

/-- The kernel form: for a genuine free resolution with flat cokernel, the presentation-level
`Tor` vanishes. -/
theorem torKernel_eq_bot_of_flat_cokernel {K F : Type*} [AddCommGroup K] [AddCommGroup F]
    (f : K →ₗ[ℤ] F) (hf : Function.Injective f) [Module.Flat ℤ (F ⧸ LinearMap.range f)] :
    torKernel (B := B) f = ⊥ := by
  exact LinearMap.ker_eq_bot.mpr (rTensor_injective_of_flat_cokernel (B := B) f hf)

end LeanCategories.Homological.TorReductions

