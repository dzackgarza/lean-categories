/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Lattices.Valued.FanCoarsening
public import Mathlib.GroupTheory.Coxeter.Length
public import Mathlib.Tactic

/-!
# Chamber ascent for the AET root representation

This module supplies the arbitrary-root-index form of Maxwell's Proposition 5.1 needed by the
Wythoff gallery argument.  The root index is not assumed finite and the Weyl group is not assumed
finite.

## Provenance and LC-09

The algebraic root-action lemmas and the strong-exchange proof are ports of TauCeti's
`LinearAlgebra/RootSystem/{Weyl/Group,Inversions/StrongExchange}.lean` (Tau Ceti contributors,
Apache 2.0).  The target sign statement is the invariant-form analogue of TauCeti's named theorem
`TauCeti.coroot'_smul_nonneg_of_not_isLeftDescent` in
`LinearAlgebra/RootSystem/Weyl/ParabolicQuotient.lean`.  TauCeti's theorem has a section-level
`[Finite ι]`; this port replaces its finite inversion-count route by a deletion from one reduced
word, so the AET infinite-parabolic case is retained.

Before writing declarations, `scripts/formalization_corpus.py search` was run for
`content:"coroot'_smul_nonneg_of_not_isLeftDescent"`,
`content:nonneg_simple_apply_of_not_isLeftDescent`,
`content:dominantChamber content:IsLeftDescent content:coroot`,
`content:weylCoxeterSystem content:RootPairing content:Base`,
`content:"geometric representation" content:Coxeter content:chamber`,
`content:"standard geometric" content:Coxeter content:Wythoff`,
`content:Wythoff content:Coxeter content:gallery`,
`content:"double coset" content:Coxeter content:minimal`,
`content:"Tits cone" content:gallery content:chamber`, and
`content:RootPairing content:PerfectPairing content:span_root_eq_top`.  The named TauCeti theorem
was the only direct sign hit; no arbitrary-index Maxwell/Wythoff gallery theorem was found.  The
full source files were then read through the same corpus API.  The query log is
`.scratch/wt181/lc09-foundation-2.txt`.

Maxwell, *Wythoff's Construction for Coxeter Groups*, Proposition 5.1, assumes exactly the standard
geometric representation, a point of the closed chamber and `ℓ(sw) > ℓ(w)`; it has no finiteness
hypothesis.  A `RootPairing` supplies the full root orbit, injective roots and coroots, perfect
pairing and reflection stability; the base supplies simple roots and positive/negative expansions.
-/

@[expose] public section

noncomputable section

namespace RootPairing

open Set Function

universe u v w x

variable {ι : Type u} {R : Type v} {M : Type w} {N : Type x}
  [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (P : RootPairing ι R M N)

/-- Port of TauCeti's `RootPairing.coroot'_smul`. -/
lemma coroot'_smul_aet (g : P.Aut) (i : ι) (x : M) :
    P.coroot' i (g • x) = P.coroot' (g.indexEquiv.symm i) x := by
  change P.coroot' i (g.weightMap x) = _
  simpa using g.coroot'_weightEquiv (g.indexEquiv.symm i) x

/-- Port of TauCeti's `RootPairing.coroot'_weylGroupToPerm_smul`. -/
lemma coroot'_weylGroupToPerm_smul_aet (w : P.weylGroup) (i : ι) (x : M) :
    P.coroot' (P.weylGroupToPerm w i) (w • x) = P.coroot' i x := by
  have h := coroot'_smul_aet P (w : P.Aut) ((w : P.Aut).indexEquiv i) x
  rw [Equiv.symm_apply_apply] at h
  exact h

/-- Port of TauCeti's `RootPairing.weylGroupToPerm_ofIdx_apply`. -/
lemma weylGroupToPerm_ofIdx_apply_aet (i j : ι) :
    P.weylGroupToPerm (weylGroup.ofIdx P i) j = P.reflectionPerm i j := by
  change (Equiv.reflection P i).indexEquiv j = P.reflectionPerm i j
  exact congrArg (fun e : ι ≃ ι ↦ e j) (Equiv.reflection_indexEquiv P i)

/-- Port of TauCeti's `RootPairing.weylGroupToPerm_ofIdx_mul_apply`. -/
lemma weylGroupToPerm_ofIdx_mul_apply_aet (w : P.weylGroup) (i j : ι) :
    P.weylGroupToPerm (weylGroup.ofIdx P i * w) j =
      P.reflectionPerm i (P.weylGroupToPerm w j) := by
  rw [map_mul]
  exact weylGroupToPerm_ofIdx_apply_aet P i (P.weylGroupToPerm w j)

/-- Port of TauCeti's `RootPairing.weylGroup.eq_one_of_smul_eq_self`. -/
lemma weylGroup_eq_one_of_smul_eq_self_aet {w : P.weylGroup}
    (h : ∀ x : M, w • x = x) : w = 1 := by
  have hw : (w : P.Aut) = 1 := by
    refine Equiv.weightHom_injective P ?_
    rw [map_one]
    exact LinearEquiv.ext fun x ↦ h x
  exact Subtype.ext (by simpa using hw)

/-- Port of TauCeti's `RootPairing.weylGroup.ext`. -/
@[ext (iff := false)] lemma weylGroup_ext_aet {v w : P.weylGroup}
    (h : ∀ x : M, v • x = w • x) : v = w := by
  rw [← mul_inv_eq_one]
  refine weylGroup_eq_one_of_smul_eq_self_aet P fun x ↦ ?_
  rw [mul_smul, h, smul_inv_smul]

/-- Port of TauCeti's `RootPairing.weylGroup.ofIdx_inv_eq`. -/
@[simp] lemma weylGroup_ofIdx_inv_eq_aet (i : ι) :
    (weylGroup.ofIdx P i)⁻¹ = weylGroup.ofIdx P i :=
  Subtype.ext (Equiv.reflection_inv P i)

/-- Port of TauCeti's `RootPairing.weylGroup.ofIdx_mul_self`. -/
@[simp] lemma weylGroup_ofIdx_mul_self_aet (i : ι) :
    weylGroup.ofIdx P i * weylGroup.ofIdx P i = 1 := by
  rw [mul_eq_one_iff_eq_inv, weylGroup_ofIdx_inv_eq_aet]

/-- Port of TauCeti's `RootPairing.weylGroup.ofIdx_weylGroupToPerm_eq_conj`. -/
theorem weylGroup_ofIdx_weylGroupToPerm_eq_conj_aet (w : P.weylGroup) (i : ι) :
    weylGroup.ofIdx P (P.weylGroupToPerm w i) =
      w * weylGroup.ofIdx P i * w⁻¹ := by
  refine weylGroup_ext_aet P fun x ↦ ?_
  have hcoroot : P.coroot' i (w⁻¹ • x) = P.coroot' (P.weylGroupToPerm w i) x := by
    conv_rhs => rw [← smul_inv_smul w x]
    exact (coroot'_weylGroupToPerm_smul_aet P w i (w⁻¹ • x)).symm
  have hroot : w • P.root i = P.root (P.weylGroupToPerm w i) := P.weylGroup_apply_root w i
  calc
    weylGroup.ofIdx P (P.weylGroupToPerm w i) • x
        = x - P.coroot' (P.weylGroupToPerm w i) x • P.root (P.weylGroupToPerm w i) := by
      simp [reflection_apply]
    _ = w • (w⁻¹ • x - P.coroot' i (w⁻¹ • x) • P.root i) := by
      rw [smul_sub, smul_inv_smul, smul_comm, hroot, hcoroot]
    _ = (w * weylGroup.ofIdx P i * w⁻¹) • x := by
      simp [mul_smul, reflection_apply]

namespace InvariantForm

variable {ι M N : Type*} [AddCommGroup M] [Module ℝ M]
  [AddCommGroup N] [Module ℝ N] {P : RootPairing ι ℝ M N}

/-- The root functional defined by an invariant form vanishes exactly where the corresponding
coroot functional vanishes.  This is the general linear identity obtained from reflection
orthogonality, specialized to one zero value. -/
lemma coroot'_eq_zero_of_apply_root_eq_zero (B : P.InvariantForm) (i : ι) {x : M}
    (hx : B.form (P.root i) x = 0) : P.coroot' i x = 0 := by
  have h := B.isOrthogonal_reflection i (P.root i) x
  rw [P.reflection_apply_self, P.reflection_apply] at h
  simp only [LinearMap.neg_apply, map_neg, map_sub, map_smul, LinearMap.sub_apply,
    LinearMap.smul_apply, smul_eq_mul, neg_neg] at h
  rw [hx] at h
  have hnorm := B.ne_zero i
  have hzero : P.coroot' i x * B.form (P.root i) (P.root i) = 0 := by
    linear_combination h
  exact (mul_eq_zero.mp hzero).resolve_right hnorm

end InvariantForm

namespace Base

variable [Module ℝ M] [Module ℝ N]
  (P : RootPairing ι ℝ M N) [P.IsCrystallographic] [P.IsReduced]
  (b : P.Base)

/-- The Weyl-group element spelled by a word in the simple reflections of a base. -/
def simpleWordProd (b : P.Base) (l : List b.support) : P.weylGroup :=
  (l.map fun i : b.support ↦ RootPairing.weylGroup.ofIdx P (i : ι)).prod

omit [P.IsCrystallographic] [P.IsReduced] in
@[simp] lemma simpleWordProd_nil (b : P.Base) : simpleWordProd P b [] = 1 :=
  List.prod_nil

omit [P.IsCrystallographic] [P.IsReduced] in
@[simp] lemma simpleWordProd_cons (b : P.Base) (i : b.support) (l : List b.support) :
    simpleWordProd P b (i :: l) =
      RootPairing.weylGroup.ofIdx P (i : ι) * simpleWordProd P b l :=
  List.prod_cons

omit [P.IsCrystallographic] [P.IsReduced] in
@[simp] lemma simpleWordProd_append (b : P.Base) (l l' : List b.support) :
    simpleWordProd P b (l ++ l') = simpleWordProd P b l * simpleWordProd P b l' := by
  rw [simpleWordProd, List.map_append, List.prod_append]
  rfl

/-- The root-level strong exchange condition, ported from TauCeti with the finite-root
assumption removed. -/
theorem exists_simpleWordProd_eraseIdx_eq_mul_ofIdx {k : ι} (hk : b.IsPos k)
    (l : List b.support) (h : ¬b.IsPos (P.weylGroupToPerm (simpleWordProd P b l) k)) :
    ∃ j < l.length, simpleWordProd P b (l.eraseIdx j) =
      simpleWordProd P b l * RootPairing.weylGroup.ofIdx P k := by
  induction l with
  | nil => exact absurd (by simpa using hk) h
  | cons j l ih =>
    rw [simpleWordProd_cons, weylGroupToPerm_ofIdx_mul_apply_aet] at h
    by_cases hpos : b.IsPos (P.weylGroupToPerm (simpleWordProd P b l) k)
    · refine ⟨0, by simp, ?_⟩
      have hkey : P.weylGroupToPerm (simpleWordProd P b l) k = (j : ι) := by
        by_contra hne
        exact h (isPos_reflectionPerm_of_ne P b j.property hpos hne)
      rw [List.eraseIdx_cons_zero, simpleWordProd_cons, ← hkey,
        weylGroup_ofIdx_weylGroupToPerm_eq_conj_aet, inv_mul_cancel_right, mul_assoc,
        weylGroup_ofIdx_mul_self_aet, mul_one]
    · obtain ⟨j', hj', hl'⟩ := ih hpos
      refine ⟨j' + 1, by simpa using hj', ?_⟩
      rw [List.eraseIdx_cons_succ, simpleWordProd_cons, hl', simpleWordProd_cons, mul_assoc]

end Base

end RootPairing

namespace CoxeterSystem

open RootPairing RootPairing.Base

variable {ι M N : Type*} [AddCommGroup M] [Module ℝ M] [AddCommGroup N] [Module ℝ N]

lemma simpleWordProd_eq_wordProd {P : RootPairing ι ℝ M N} (b : P.Base)
    {ℳ : CoxeterMatrix b.support} {cs : CoxeterSystem ℳ P.weylGroup}
    (hsimple : ∀ i, cs.simple i = RootPairing.weylGroup.ofIdx P (i : ι)) (l : List b.support) :
    simpleWordProd P b l = cs.wordProd l := by
  induction l with
  | nil => simp
  | cons i l ih =>
    rw [CoxeterSystem.wordProd_cons, simpleWordProd_cons, ih, hsimple]

/-- A reduced-word form of the right-descent criterion for a simple root sent to a negative
root.  No finiteness of the root index or Weyl group is used. -/
theorem isRightDescent_of_not_isPos_weylGroupToPerm
    {P : RootPairing ι ℝ M N} [P.IsCrystallographic] [P.IsReduced] (b : P.Base)
    {ℳ : CoxeterMatrix b.support} (cs : CoxeterSystem ℳ P.weylGroup)
    (hsimple : ∀ i, cs.simple i = RootPairing.weylGroup.ofIdx P (i : ι))
    {v : P.weylGroup} (i : b.support) (hv : ¬b.IsPos (P.weylGroupToPerm v (i : ι))) :
    cs.IsRightDescent v i := by
  obtain ⟨ω, hω, hprod⟩ := cs.exists_isReduced v
  have hneg : ¬b.IsPos (P.weylGroupToPerm (simpleWordProd P b ω) (i : ι)) := by
    simpa only [simpleWordProd_eq_wordProd b hsimple, ← hprod] using hv
  obtain ⟨j, hj, herase⟩ := exists_simpleWordProd_eraseIdx_eq_mul_ofIdx P b
    (b.isPos_of_mem_support i.property) ω hneg
  have hcs : cs.wordProd (ω.eraseIdx j) = v * cs.simple i := by
    calc
      cs.wordProd (ω.eraseIdx j) = simpleWordProd P b (ω.eraseIdx j) :=
        (simpleWordProd_eq_wordProd b hsimple _).symm
      _ = simpleWordProd P b ω * RootPairing.weylGroup.ofIdx P (i : ι) := herase
      _ = cs.wordProd ω * cs.simple i := by
        rw [simpleWordProd_eq_wordProd b hsimple, hsimple]
      _ = v * cs.simple i := by rw [← hprod]
  rw [CoxeterSystem.IsRightDescent]
  calc
    cs.length (v * cs.simple i) = cs.length (cs.wordProd (ω.eraseIdx j)) := by rw [hcs]
    _ ≤ (ω.eraseIdx j).length := cs.length_wordProd_le _
    _ < ω.length := by
      have hlen := List.length_eraseIdx_add_one hj
      omega
    _ = cs.length v := by rw [hprod, hω.eq]

/-- **Maxwell Proposition 5.1 for the AET invariant-form chamber.**  If `sᵢ` is not a left
descent of `w`, then the `i`-th simple functional is nonnegative on the `w`-translate of every
point of the fundamental chamber.  This is the invariant-form analogue of TauCeti's
`coroot'_smul_nonneg_of_not_isLeftDescent`, proved for an arbitrary root index. -/
theorem nonneg_simple_apply_of_not_isLeftDescent
    {P : RootPairing ι ℝ M N} [P.IsCrystallographic] [P.IsReduced]
    (b : P.Base) (B : P.InvariantForm) {ℳ : CoxeterMatrix b.support}
    (cs : CoxeterSystem ℳ P.weylGroup)
    (hsimple : ∀ i, cs.simple i = RootPairing.weylGroup.ofIdx P (i : ι))
    {w : P.weylGroup} (i : b.support) (hi : ¬cs.IsLeftDescent w i)
    {y : M} (hy : y ∈ LeanCategories.Lattices.Valued.fundamentalChamber P b B) :
    0 ≤ B.form (P.root (i : ι)) (w • y) := by
  by_contra hneg
  have hroot : ¬b.IsPos (P.weylGroupToPerm w⁻¹ (i : ι)) := by
    intro hpos
    have hnonneg : 0 ≤ B.form (P.root (P.weylGroupToPerm w⁻¹ (i : ι))) y :=
      LeanCategories.Lattices.Valued.eval_root_nonneg_of_mem_fundamentalChamber
        P b B hy hpos
    have hnonneg' : 0 ≤ B.form (P.root (i : ι)) (w • y) := by
      rwa [LeanCategories.Lattices.Valued.eval_root_apply_eq_inv_smul,
        P.weylGroup_apply_root]
    exact hneg hnonneg'
  have hright := isRightDescent_of_not_isPos_weylGroupToPerm b cs hsimple (v := w⁻¹) i hroot
  exact hi (cs.isRightDescent_inv_iff.mp hright)

end CoxeterSystem
