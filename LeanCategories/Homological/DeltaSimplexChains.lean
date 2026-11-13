/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 License as described in the file LICENSE.
-/
module

public import Mathlib.LinearAlgebra.Dimension.RankNullity
public import Mathlib.LinearAlgebra.Dimension.Localization
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
public import Mathlib.RingTheory.PrincipalIdealDomain
public import Mathlib.Algebra.EuclideanDomain.Int

@[expose] public section

/-!
# `E-HAT-2.2-16`: the Δ-complex chain model of the standard simplex

Card `E-HAT-2.2-16` of the qualifying-exam corpus.  Source: Hatcher, *Algebraic
Topology*, Section 2.2, exercise 16 (printed p. 156): the ranks of the simplicial
chain groups of `Δ^n` and of their subgroups of cycles and boundaries, and the
reduced homology of the `k`-skeleton.  Certificate: new-qual-site
`proofs/cards/DeltaSimplexChains.lean` at commit `16c09abaa4`.

LC-09 search record (queries run against the formalization corpus and local
Mathlib): the model below is the card's own, written out on the `(i+1)`-element
vertex subsets; Mathlib has no simplicial-chain model of `Δ^n` to import (the
`Simplices`/`chains` abbreviations are this file's), so the certificate is
ported whole and the boxed claims come with it.

Provenance: ported from new-qual-site at commit `16c09abaa4`,
`proofs/cards/DeltaSimplexChains.lean`, with the three `def` names carrying
underscores renamed per the `defsWithUnderscore` lint (`gen_c` -> `genC`,
`h_minus` -> `hMinus`, `cycles_aug` -> `cyclesAug`); theorem names keep the
certificate's spelling.
-/


/-!
# `E-HAT-2.2-16`: the Δ-complex chain model of the standard simplex

`E-HAT-2.2-16` asks for the ranks of the simplicial chain groups $C_i(\Delta^n)$ and of their
subgroups of cycles and boundaries, and then for the reduced homology of the $k$-skeleton of
$\Delta^n$: it must vanish below degree $k$ and be free of rank $\binom{n}{k+1}$ in degree
$k$. The stored proof works in the Δ-complex chain model: the group of $i$-chains is free
on the $(i+1)$-element vertex subsets, the boundary is the alternating sum over ordered
deletions, and the $k$-skeleton is the truncation of that model.

This file certifies that model, from maintained API and nothing bespoke:

* `finrank_chains`: $\operatorname{rank} C_i(\Delta^n) = \binom{n+1}{i+1}$, the count of
  $(i+1)$-element subsets (`Finset.powersetCard`);
* `aug_comp_boundary`, `boundary_comp_boundary`: the augmented complex is a complex
  ($\varepsilon\partial_1 = 0$, $\partial_i\partial_{i+1} = 0$);
* `homotopy_succ`, `homotopy_zero`, `aug_hMinus`: the cone contraction
  $h_i(s) = (-1)^i \cdot (0$ if $n \in s$, else $s \cup \{n\})$ with
  $(\partial h + h\partial)(x) = -x$ on the augmented complex, degree by degree;
* `exact_zero`, `exact_succ`: the augmented complex of $\Delta^n$ is exact;
* `finrank_boundaries`, `finrank_cycles_aug`: the rank induction
  $\operatorname{rank} B_i = \operatorname{rank} Z_i = \binom{n}{i+1}$ (Pascal's identity and
  rank-nullity over $\mathbb{Z}$), with $\operatorname{rank} B_0 = n$ and
  $\operatorname{rank} C_0 = n+1$;
* `sk_cycles_aug_eq_sk_boundaries`, `subsingleton_sk_homology`:
  $\widetilde H_i((\Delta^n)^k) = 0$ for $i < k$;
* `sk_homology_top_basis`: $\widetilde H_k((\Delta^n)^k)$ is free of rank $\binom{n}{k+1}$.

The three files `cards/SimplexChains.lean`, `cards/ChainLevelSteps.lean` and
`cards/SkeletonHomology.lean` certify the same homological statements in Mathlib's
alternating-face-map model. This file is the certificate of the card's own model, and it is
self-contained, as the directory's convention requires.
-/

namespace LeanCategories.Homological.DeltaSimplexChains

open Cardinal

/-! ## The model -/

/-- The `i`-simplices of `Δ^n` in its Δ-complex structure: the `(i+1)`-element vertex
subsets (Hatcher p. 104, p. 105: the chain group `Δ_i(X)` of a Δ-complex is free on the open
`i`-simplices, here the increasing vertex lists `v_{i_0} < ⋯ < v_{i_k}`). -/
abbrev Simplices (n i : ℕ) : Type := {s : Finset (Fin (n+1)) // s.card = i + 1}

/-- The `i`-chains of `Δ^n`: the free abelian group on the `i`-simplices. -/
abbrev chains (n i : ℕ) : Type := Simplices n i →₀ ℤ

/-- The position of `v` in the increasing enumeration of `s`. -/
def posOf {m : ℕ} (s : Finset (Fin m)) (v : Fin m) : ℕ := (s.filter (· < v)).card

/-- The chain `c • [t]` in degree `i`: the generator indexed by `t` when `t` is an
`i`-simplex (an `(i+1)`-element vertex subset), `0` otherwise. Total on all vertex subsets,
which is what the pair-indexed sums of the boundary-square computation need. -/
noncomputable def genC (n i : ℕ) (t : Finset (Fin (n+1))) (c : ℤ) : chains n i :=
  if h : t.card = i + 1 then Finsupp.single ⟨t, h⟩ c else 0

/-- The boundary `∂ : C_{j+1} → C_j`: on a simplex, the alternating sum over the deletions
of its vertices in increasing order. -/
noncomputable def boundary (n j : ℕ) : chains n (j+1) →ₗ[ℤ] chains n j :=
  (Finsupp.llift (chains n j) ℤ ℤ (Simplices n (j+1))) (fun s =>
    ∑ v ∈ s.1, genC n j (s.1.erase v) ((-1 : ℤ) ^ posOf s.1 v))

/-- The cone contraction `h : C_j → C_{j+1}`, `s ↦ (-1)^j (0 if n ∈ s, else s ∪ {n})`: on a
simplex not containing the last vertex `n`, the signed simplex `s ∪ {n}`; the cardinality
guard sends `s ∪ {n} = s` to `0` when `n ∈ s`. -/
noncomputable def h (n j : ℕ) : chains n j →ₗ[ℤ] chains n (j+1) :=
  (Finsupp.llift (chains n (j+1)) ℤ ℤ (Simplices n j))
    (fun s => genC n (j+1) (insert (Fin.last n) s.1) ((-1 : ℤ) ^ j))

/-- The augmentation `ε : C_0 → ℤ`, reading off the sum of the coefficients. -/
noncomputable def aug (n : ℕ) : chains n 0 →ₗ[ℤ] ℤ :=
  (Finsupp.llift ℤ ℤ ℤ (Simplices n 0)) (fun _ => (1 : ℤ))

/-- The degree `-1` part of the cone contraction: `h₋₁(z) = -z • [n]`. -/
noncomputable def hMinus (n : ℕ) : ℤ →ₗ[ℤ] chains n 0 :=
  LinearMap.toSpanSingleton ℤ (chains n 0) (-(genC n 0 {Fin.last n} (1 : ℤ)))

/-! ## The deletion position -/

lemma pos_of_erase_lt {m : ℕ} {v w : Fin m} (s : Finset (Fin m)) (hv : v ∈ s)
    (hvw : v < w) : posOf (s.erase v) w = posOf s w - 1 := by
  rw [posOf, posOf, Finset.filter_erase,
    Finset.card_erase_of_mem (Finset.mem_filter.2 ⟨hv, hvw⟩)]

lemma pos_of_erase_of_notMem {m : ℕ} {v w : Fin m} (s : Finset (Fin m)) (h : ¬ v < w) :
    posOf (s.erase v) w = posOf s w := by
  have hvf : v ∉ s.filter (· < w) := fun hmem => h (Finset.mem_filter.1 hmem).2
  rw [posOf, posOf, Finset.filter_erase, Finset.erase_eq_of_notMem hvf]

lemma pos_of_last {n : ℕ} (s : Finset (Fin (n+1))) (h : Fin.last n ∉ s) :
    posOf s (Fin.last n) = s.card := by
  have h2 : s.filter (· < Fin.last n) = s := Finset.filter_eq_self.2
    fun u hu => Fin.lt_last_iff_ne_last.2 (fun heq => h (heq ▸ hu))
  rw [posOf, h2]

lemma pos_of_insert_last {n : ℕ} (t : Finset (Fin (n+1))) (h : Fin.last n ∉ t) :
    posOf (insert (Fin.last n) t) (Fin.last n) = t.card := by
  have h1 : (insert (Fin.last n) t).filter (· < Fin.last n) = t.filter (· < Fin.last n) := by
    rw [Finset.filter_insert]
    simp
  rw [posOf, h1]
  exact pos_of_last t h

/-! ## The generators -/

lemma gen_c_of_card (n i : ℕ) {t : Finset (Fin (n+1))} (c : ℤ) (ht : t.card = i + 1) :
    genC n i t c = Finsupp.single ⟨t, ht⟩ c := by
  simp only [genC, dite_eq_left ht]

lemma gen_c_smul (n i : ℕ) (t : Finset (Fin (n+1))) (c d : ℤ) :
    c • genC n i t d = genC n i t (c * d) := by
  by_cases ht : t.card = i + 1
  · rw [gen_c_of_card _ _ _ ht, gen_c_of_card _ _ _ ht, Finsupp.smul_single']
  · simp only [genC, dite_eq_right ht, smul_zero]

lemma single_smul_one {α : Type} {a : α} (c : ℤ) :
    Finsupp.single a c = c • Finsupp.single a (1 : ℤ) := by
  rw [Finsupp.smul_single', mul_one]

lemma boundary_single (n j : ℕ) (s : Simplices n (j+1)) :
    boundary n j (Finsupp.single s 1) =
      ∑ v ∈ s.1, genC n j (s.1.erase v) ((-1 : ℤ) ^ posOf s.1 v) := by
  simp only [boundary, Finsupp.llift_apply, Finsupp.lift_apply, Finsupp.sum_single_index,
    one_smul, zero_smul]

lemma boundary_gen_c (n j : ℕ) {t : Finset (Fin (n+1))} (c : ℤ) (ht : t.card = j + 2) :
    boundary n j (genC n (j+1) t c) =
      ∑ v ∈ t, genC n j (t.erase v) (c * (-1 : ℤ) ^ posOf t v) := by
  rw [gen_c_of_card _ _ c (by simpa using ht), single_smul_one, map_smul, boundary_single,
    Finset.smul_sum]
  exact Finset.sum_congr rfl fun v _ => gen_c_smul n j (t.erase v) c _

lemma h_single (n j : ℕ) (s : Simplices n j) :
    h n j (Finsupp.single s 1) = genC n (j+1) (insert (Fin.last n) s.1) ((-1 : ℤ) ^ j) := by
  simp only [h, Finsupp.llift_apply, Finsupp.lift_apply, Finsupp.sum_single_index,
    one_smul, zero_smul]

lemma h_gen_c (n j : ℕ) {t : Finset (Fin (n+1))} (c : ℤ) (ht : t.card = j + 1) :
    h n j (genC n j t c) = genC n (j+1) (insert (Fin.last n) t) (c * (-1 : ℤ) ^ j) := by
  rw [gen_c_of_card _ _ c ht, single_smul_one, map_smul, h_single]
  exact gen_c_smul n (j+1) (insert (Fin.last n) t) c _

lemma aug_single (n : ℕ) (s : Simplices n 0) : aug n (Finsupp.single s 1) = 1 := by
  simp only [aug, Finsupp.llift_apply, Finsupp.lift_apply, Finsupp.sum_single_index,
    one_smul, zero_smul]

lemma aug_gen_c (n : ℕ) {t : Finset (Fin (n+1))} (c : ℤ) (ht : t.card = 0 + 1) :
    aug n (genC n 0 t c) = c := by
  rw [gen_c_of_card _ _ c (by simpa using ht), single_smul_one, map_smul, aug_single,
    smul_eq_mul, mul_one]

/-! ## Generators: auxiliary lemmas -/

lemma linearMap_ext_single {X M : Type} [AddCommGroup M] [Module ℤ M]
    {f g : (X →₀ ℤ) →ₗ[ℤ] M}
    (h : ∀ s : X, f (Finsupp.single s 1) = g (Finsupp.single s 1)) :
    f = g :=
  Finsupp.basisSingleOne.ext fun s => by simpa using h s

lemma gen_c_of_ne_card (n i : ℕ) {t : Finset (Fin (n+1))} (c : ℤ) (ht : t.card ≠ i + 1) :
    genC n i t c = 0 := by
  simp only [genC, dite_eq_right (fun h => ht h)]

lemma gen_c_add (n i : ℕ) (t : Finset (Fin (n+1))) (c d : ℤ) :
    genC n i t c + genC n i t d = genC n i t (c + d) := by
  by_cases ht : t.card = i + 1
  · rw [gen_c_of_card _ _ c ht, gen_c_of_card _ _ d ht, gen_c_of_card _ _ (c + d) ht,
      ← Finsupp.single_add]
  · rw [gen_c_of_ne_card _ _ c ht, gen_c_of_ne_card _ _ d ht,
      gen_c_of_ne_card _ _ (c + d) ht, add_zero]

lemma gen_c_zero (n i : ℕ) (t : Finset (Fin (n+1))) : genC n i t 0 = 0 := by
  by_cases ht : t.card = i + 1
  · rw [gen_c_of_card _ _ (0 : ℤ) ht, Finsupp.single_zero]
  · exact gen_c_of_ne_card _ _ 0 ht

lemma gen_c_smul_single (n i : ℕ) (s : Simplices n i) (c : ℤ) :
    genC n i s.1 c = c • Finsupp.single s (1 : ℤ) := by
  rw [gen_c_of_card _ _ c s.2, ← single_smul_one]

lemma neg_one_pow_odd (m : ℕ) : (-1 : ℤ) ^ (2 * m + 1) = -1 := by
  induction m with
  | zero => norm_num
  | succ m ih => rw [show 2 * (m + 1) + 1 = 2 * m + 1 + 2 by omega, pow_add, ih]; norm_num

lemma neg_one_pow_succ (j : ℕ) : (-1 : ℤ) ^ (j + 1) = -(-1 : ℤ) ^ j := by
  rw [pow_succ, mul_neg_one]

/-- The two exponents that the boundary-square computation compares. -/
lemma neg_one_pow_pair_cancel (A B : ℕ) (h : 1 ≤ B) :
    (-1 : ℤ) ^ A * (-1 : ℤ) ^ (B - 1) + (-1 : ℤ) ^ B * (-1 : ℤ) ^ A = 0 := by
  rw [← pow_add, ← pow_add, show B + A = A + (B - 1) + 1 by omega, pow_succ, mul_neg_one]
  ring

/-! ## The augmented complex is a complex -/

/-- The alternating sum of the deletion positions over a two-element set. -/
lemma sum_neg_one_pow_pair {m : ℕ} (v w : Fin m) (hvw : v < w) :
    ∑ u ∈ insert v (insert w (∅ : Finset (Fin m))),
        (-1 : ℤ) ^ posOf (insert v (insert w (∅ : Finset (Fin m)))) u = 0 := by
  have h0 : posOf (insert v (insert w (∅ : Finset (Fin m)))) v = 0 := by
    rw [posOf]
    have h : (insert v (insert w (∅ : Finset (Fin m)))).filter (· < v) = ∅ := by
      ext u
      simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨rfl | rfl | hu, hult⟩
        · exact absurd hult (lt_irrefl _)
        · exact absurd hult (lt_asymm hvw)
        · exact absurd hu (Finset.notMem_empty u)
      · intro hu
        exact absurd hu (Finset.notMem_empty u)
    rw [h]
    simp
  have h1 : posOf (insert v (insert w (∅ : Finset (Fin m)))) w = 1 := by
    rw [posOf]
    have h : (insert v (insert w (∅ : Finset (Fin m)))).filter (· < w) = {v} := by
      ext u
      simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨rfl | rfl | hu, hult⟩
        · exact rfl
        · exact absurd hult (lt_irrefl _)
        · exact absurd hu (Finset.notMem_empty u)
      · rintro rfl
        exact ⟨Or.inl rfl, hvw⟩
    rw [h]
    simp
  rw [Finset.sum_insert (by simp [ne_of_lt hvw] :
      v ∉ (insert w (∅ : Finset (Fin m)))), Finset.sum_insert (by simp),
    Finset.sum_empty, add_zero, h0, h1]
  norm_num

/-- **`ε ∘ ∂₁ = 0`.** The augmentation kills the first boundary: on a one-simplex the
boundary
is a difference of two vertices, whose coefficients sum to zero. -/
theorem aug_comp_boundary (n : ℕ) : (aug n).comp (boundary n 0) = 0 := by
  refine linearMap_ext_single fun s => ?_
  have hs2 : s.1.card = 2 := s.2
  rw [LinearMap.comp_apply, LinearMap.zero_apply, boundary_single, map_sum,
    Finset.sum_congr rfl (fun v hv => aug_gen_c n _
      (by rw [Finset.card_erase_of_mem hv, hs2]))]
  obtain ⟨v, w, hvw, hs⟩ := Finset.card_eq_two.mp hs2
  rw [hs]
  rcases lt_or_gt_of_ne hvw with hlt | hlt
  · exact sum_neg_one_pow_pair v w hlt
  · have hsw : ({v, w} : Finset (Fin (n+1))) = {w, v} := by ext u; simp [or_comm]
    rw [hsw]
    exact sum_neg_one_pow_pair w v hlt

/-- A double sum over the deletions is a sum over the ordered pairs of distinct elements. -/
lemma sum_pairs_erase {α M : Type} [AddCommMonoid M] [DecidableEq α] (s : Finset α)
    (f : α → α → M) :
    ∑ v ∈ s, ∑ w ∈ s.erase v, f v w =
      ∑ p ∈ (s ×ˢ s).filter (fun q : α × α => q.2 ≠ q.1), f p.1 p.2 := by
  rw [Finset.sum_filter, Finset.sum_product]
  have hEF : ∀ v : α, s.erase v = s.filter (fun w => w ≠ v) := fun v =>
    Finset.ext fun u => by simp [Finset.mem_erase, Finset.mem_filter, and_comm]
  simp_rw [hEF, Finset.sum_filter]

/-- **`∂ ∘ ∂ = 0`.** The boundary squares to zero: deleting `v` then `w` and deleting `w`
then `v` give the same simplex with opposite signs — the exponents `pos s v + pos (s∖v) w`
and `pos s w + pos (s∖w) v` differ by exactly one — so the sum over the ordered pairs of
distinct vertices cancels under the swap. -/
theorem boundary_comp_boundary (n i : ℕ) : (boundary n i).comp (boundary n (i+1)) = 0 := by
  refine linearMap_ext_single fun s => ?_
  have hs3 : s.1.card = i + 3 := s.2
  rw [LinearMap.comp_apply, LinearMap.zero_apply, boundary_single, map_sum,
    Finset.sum_congr rfl (fun v hv => boundary_gen_c n i _
      (by rw [Finset.card_erase_of_mem hv, hs3]; omega)),
    sum_pairs_erase]
  refine Finset.sum_involution (fun p _ => Prod.swap p) (fun p hp => ?_)
    (fun p hp _ => fun hcon => (Finset.mem_filter.1 hp).2
      (Prod.fst_swap.symm.trans (congrArg Prod.fst hcon)))
    (fun p hp => Finset.mem_filter.2 ⟨Finset.mem_product.2
      ⟨(Finset.mem_product.1 (Finset.mem_filter.1 hp).1).2,
        (Finset.mem_product.1 (Finset.mem_filter.1 hp).1).1⟩,
      Ne.symm (Finset.mem_filter.1 hp).2⟩)
    (fun p _ => Prod.swap_swap p)
  obtain ⟨hp1, hp2⟩ := Finset.mem_product.1 (Finset.mem_filter.1 hp).1
  have hpne : p.2 ≠ p.1 := (Finset.mem_filter.1 hp).2
  have hcard : ((s.1.erase p.1).erase p.2).card = i + 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_erase_of_ne_of_mem hpne hp2),
      Finset.card_erase_of_mem hp1, hs3]
    omega
  have hswap : ((s.1.erase p.2).erase p.1) = (s.1.erase p.1).erase p.2 := by
    ext u
    simp only [Finset.mem_erase]
    constructor
    · rintro ⟨h1, h2, h3⟩; exact ⟨h2, h1, h3⟩
    · rintro ⟨h1, h2, h3⟩; exact ⟨h2, h1, h3⟩
  simp only [Prod.fst_swap, Prod.snd_swap]
  rw [gen_c_of_card _ _ _ hcard, hswap, gen_c_of_card _ _ _ hcard, ← Finsupp.single_add]
  rcases lt_or_gt_of_ne (Ne.symm hpne) with hlt | hlt
  · have e1 := pos_of_erase_lt s.1 hp1 hlt
    have e2 := pos_of_erase_of_notMem s.1 (lt_asymm hlt)
    have hB : 1 ≤ posOf s.1 p.2 :=
      Finset.card_pos.2 ⟨p.1, Finset.mem_filter.2 ⟨hp1, hlt⟩⟩
    rw [e1, e2, neg_one_pow_pair_cancel _ _ hB, Finsupp.single_zero]
  · have e1 := pos_of_erase_lt s.1 hp2 hlt
    have e2 := pos_of_erase_of_notMem s.1 (lt_asymm hlt)
    have hA : 1 ≤ posOf s.1 p.1 :=
      Finset.card_pos.2 ⟨p.2, Finset.mem_filter.2 ⟨hp2, hlt⟩⟩
    rw [e1, e2,
      add_comm (((-1 : ℤ) ^ posOf s.1 p.1) * ((-1 : ℤ) ^ posOf s.1 p.2)),
      neg_one_pow_pair_cancel _ _ hA, Finsupp.single_zero]

lemma gen_c_neg (n i : ℕ) (t : Finset (Fin (n+1))) (c : ℤ) :
    genC n i t (-c) = -(genC n i t c) := by
  by_cases ht : t.card = i + 1
  · rw [gen_c_of_card _ _ _ ht, gen_c_of_card _ _ c ht, Finsupp.single_neg]
  · rw [gen_c_of_ne_card _ _ _ ht, gen_c_of_ne_card _ _ c ht, neg_zero]

lemma pos_of_last_mem {n : ℕ} (s : Finset (Fin (n+1))) (h : Fin.last n ∈ s) :
    posOf s (Fin.last n) = s.card - 1 := by
  have h1 : s.filter (· < Fin.last n) = s.erase (Fin.last n) := by
    ext u
    simp only [Finset.mem_filter, Finset.mem_erase]
    constructor
    · rintro ⟨hus, hult⟩
      exact ⟨Fin.ne_of_lt hult, hus⟩
    · rintro ⟨hune, hus⟩
      exact ⟨hus, Fin.lt_last_iff_ne_last.mpr hune⟩
  rw [posOf, h1, Finset.card_erase_of_mem h]

/-! ## The cone contraction -/

/-- **The cone contraction in positive degrees: `(∂h + h∂)(x) = -x`.** On a simplex `s` not
containing the apex `n`, `h` appends `n` and signs by `(-1)^degree`; the boundary of
`s ∪ {n}` produces `s` with the sign `(-1)^{deg+2}`, and the `h`-image of the boundary of
`s` produces the remaining terms, which cancel against the first because
`(-1)^{j+1} = -(-1)^j`. On a simplex containing `n`, `h` vanishes and only the
deletion of `n` survives. -/
theorem homotopy_succ (n j : ℕ) (x : chains n (j+1)) :
    boundary n (j+1) (h n (j+1) x) + h n j (boundary n j x) = -x := by
  have hL : ((boundary n (j+1)).comp (h n (j+1)) + (h n j).comp (boundary n j)
      + LinearMap.id) = 0 := by
    refine linearMap_ext_single fun s => ?_
    rw [LinearMap.add_apply, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.comp_apply,
      LinearMap.id_apply, LinearMap.zero_apply, h_single, boundary_single]
    by_cases hl : Fin.last n ∈ s.1
    · rw [Finset.insert_eq_of_mem hl, gen_c_of_ne_card _ _ _ (by rw [s.2]; omega),
        map_zero, zero_add, map_sum,
        Finset.sum_congr rfl (fun v hv => h_gen_c n j _
          (by rw [Finset.card_erase_of_mem hv, s.2]; omega)),
        Finset.sum_eq_single (Fin.last n)]
      · rw [Finset.insert_erase hl, pos_of_last_mem s.1 hl]
        have hcoef : (-1 : ℤ) ^ ((j + 1 + 1) - 1) * (-1 : ℤ) ^ j = -1 := by
          rw [show (j + 1 + 1) - 1 = j + 1 by omega, ← pow_add,
            show j + 1 + j = 2 * j + 1 by omega]
          exact neg_one_pow_odd j
        rw [s.2, hcoef, gen_c_smul_single, neg_one_smul, neg_add_cancel]
      · intro v hv hvne
        rw [Finset.insert_eq_of_mem (Finset.mem_erase_of_ne_of_mem hvne.symm hl),
          gen_c_of_ne_card _ _ _ (by rw [Finset.card_erase_of_mem hv, s.2]; omega)]
      · intro hcon
        exact absurd hl hcon
    · have hcard : (insert (Fin.last n) s.1).card = j + 1 + 2 := by
        rw [Finset.card_insert_of_notMem hl, s.2]
      have hpos : ∀ u ∈ s.1, posOf (insert (Fin.last n) s.1) u = posOf s.1 u := by
        intro u hu
        have hlt : u < Fin.last n :=
          Fin.lt_last_iff_ne_last.mpr (fun heq => hl (heq ▸ hu))
        rw [posOf, posOf, Finset.filter_insert, ite_eq_right (lt_asymm hlt)]
      have hnelast : ∀ u ∈ s.1, Fin.last n ≠ u := fun u hu heq => hl (heq ▸ hu)
      have hsum1 : (∑ u ∈ s.1, genC n (j+1) ((insert (Fin.last n) s.1).erase u)
            ((-1 : ℤ) ^ (j+1) * (-1 : ℤ) ^ posOf (insert (Fin.last n) s.1) u))
          = (∑ u ∈ s.1, genC n (j+1) (insert (Fin.last n) (s.1.erase u))
            ((-1 : ℤ) ^ (j+1) * (-1 : ℤ) ^ posOf s.1 u)) := by
        refine Finset.sum_congr rfl fun u hu => ?_
        rw [Finset.erase_insert_of_ne (hnelast u hu), hpos u hu]
      have hsum2 : (∑ v ∈ s.1, genC n (j+1) (insert (Fin.last n) (s.1.erase v))
            ((-1 : ℤ) ^ posOf s.1 v * (-1 : ℤ) ^ j))
          = -(∑ u ∈ s.1, genC n (j+1) (insert (Fin.last n) (s.1.erase u))
            ((-1 : ℤ) ^ (j+1) * (-1 : ℤ) ^ posOf s.1 u)) := by
        rw [← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun u _ => ?_
        rw [← gen_c_neg, neg_one_pow_succ]
        ring
      rw [boundary_gen_c n (j+1) ((-1 : ℤ) ^ (j+1)) hcard, Finset.sum_insert hl,
        Finset.erase_insert hl, pos_of_insert_last s.1 hl, s.2, map_sum,
        Finset.sum_congr rfl (fun v hv => h_gen_c n j _
          (by rw [Finset.card_erase_of_mem hv, s.2]; omega)),
        hsum1, hsum2]
      have hcancel : genC n (j+1) s.1 ((-1 : ℤ) ^ (j + 1) * (-1 : ℤ) ^ (j + 1 + 1))
          + (∑ u ∈ s.1, genC n (j+1) (insert (Fin.last n) (s.1.erase u))
            ((-1 : ℤ) ^ (j+1) * (-1 : ℤ) ^ posOf s.1 u))
          + -(∑ u ∈ s.1, genC n (j+1) (insert (Fin.last n) (s.1.erase u))
            ((-1 : ℤ) ^ (j+1) * (-1 : ℤ) ^ posOf s.1 u))
          + Finsupp.single s (1 : ℤ)
          = genC n (j+1) s.1 ((-1 : ℤ) ^ (j + 1) * (-1 : ℤ) ^ (j + 1 + 1))
            + Finsupp.single s (1 : ℤ) := by
        abel
      rw [hcancel, gen_c_smul_single,
        show (-1 : ℤ) ^ (j + 1) * (-1 : ℤ) ^ (j + 2) = -1 by
          rw [← pow_add, show j + 1 + (j + 2) = 2 * (j + 1) + 1 by omega]
          exact neg_one_pow_odd (j + 1),
        neg_one_smul, neg_add_cancel]
  have hx := congrArg (fun (f : chains n (j+1) →ₗ[ℤ] chains n (j+1)) => f x) hL
  simp only [LinearMap.zero_apply, LinearMap.add_apply, LinearMap.comp_apply,
    LinearMap.id_apply] at hx
  exact eq_neg_of_add_eq_zero_left hx

/-- **The cone contraction in degree zero.** -/
theorem homotopy_zero (n : ℕ) (x : chains n 0) :
    boundary n 0 (h n 0 x) + hMinus n (aug n x) = -x := by
  have hL : ((boundary n 0).comp (h n 0) + (hMinus n).comp (aug n) + LinearMap.id) = 0 := by
    refine linearMap_ext_single fun s => ?_
    rw [LinearMap.add_apply, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.comp_apply,
      LinearMap.id_apply, LinearMap.zero_apply, h_single, aug_single]
    by_cases hl : Fin.last n ∈ s.1
    · obtain ⟨a, ha⟩ := Finset.card_eq_one.mp s.2
      rw [ha] at hl ⊢
      have hlast : Fin.last n = a := Finset.mem_singleton.mp hl
      subst hlast
      rw [pow_zero, Finset.insert_eq_of_mem (Finset.mem_singleton_self _),
        gen_c_of_ne_card _ _ _ (by simp), map_zero, zero_add, hMinus,
        LinearMap.toSpanSingleton_apply, one_smul]
      have hkey : genC n 0 {Fin.last n} (1 : ℤ) = Finsupp.single s (1 : ℤ) := by
        rw [show genC n 0 {Fin.last n} (1 : ℤ) = genC n 0 s.1 (1 : ℤ) from by rw [ha],
          gen_c_smul_single, one_smul]
      rw [hkey, neg_add_cancel]
    · obtain ⟨a, ha⟩ := Finset.card_eq_one.mp s.2
      rw [ha] at hl ⊢
      have hne : a ≠ Fin.last n := fun heq => hl (heq ▸ Finset.mem_singleton_self a)
      have halt : a < Fin.last n := Fin.lt_last_iff_ne_last.mpr hne
      have hposa : posOf (insert (Fin.last n) {a}) a = 0 := by
        rw [posOf, Finset.filter_insert, ite_eq_right (lt_asymm halt),
          Finset.filter_singleton, ite_eq_right (lt_irrefl a), Finset.card_empty]
      rw [pow_zero, boundary_gen_c n 0 (1 : ℤ) (by rw [Finset.card_insert_of_notMem hl,
        Finset.card_singleton]), Finset.sum_insert hl, Finset.erase_insert hl,
        pos_of_insert_last _ hl, Finset.card_singleton, Finset.sum_singleton,
        Finset.erase_insert_of_ne (Ne.symm hne), Finset.erase_singleton,
        Finset.insert_empty, hposa, hMinus, LinearMap.toSpanSingleton_apply, one_smul]
      norm_num
      have hkey : genC n 0 {a} (-1 : ℤ) = -(Finsupp.single s (1 : ℤ)) := by
        rw [show genC n 0 {a} (-1 : ℤ) = genC n 0 s.1 (-1 : ℤ) from by rw [ha],
          gen_c_smul_single, neg_one_smul]
      rw [hkey, neg_add_cancel]
  have hx := congrArg (fun (f : chains n 0 →ₗ[ℤ] chains n 0) => f x) hL
  simp only [LinearMap.zero_apply, LinearMap.add_apply, LinearMap.comp_apply,
    LinearMap.id_apply] at hx
  exact eq_neg_of_add_eq_zero_left hx

/-- **The cone contraction in degree `-1`: `ε ∘ h₋₁ = -id`.** -/
theorem aug_h_minus (n : ℕ) (z : ℤ) : aug n (hMinus n z) = -z := by
  rw [hMinus, LinearMap.toSpanSingleton_apply, map_smul, map_neg, aug_gen_c n 1 (by simp),
    smul_eq_mul, mul_neg_one]

/-! ## The augmented complex is exact -/

/-- The group of `i`-boundaries: the image of `∂ : C_{i+1} → C_i`. -/
noncomputable def boundaries (n i : ℕ) : Submodule ℤ (chains n i) :=
  LinearMap.range (boundary n i)

/-- The group of `i`-cycles of the augmented complex: `ker ∂_i` for `i ≥ 1`, `ker ε` in
degree zero. -/
noncomputable def cyclesAug (n : ℕ) : ∀ i, Submodule ℤ (chains n i)
  | 0 => LinearMap.ker (aug n)
  | i + 1 => LinearMap.ker (boundary n i)

theorem mem_boundaries {n i : ℕ} {x : chains n i} :
    x ∈ boundaries n i ↔ ∃ y : chains n (i+1), boundary n i y = x :=
  LinearMap.mem_range

/-- **Exactness in degree zero: `ker ε = im ∂₁`.** The inclusion `im ∂₁ ⊆ ker ε` is
`aug_comp_boundary`; the converse is the cone contraction, which exhibits any `x` with
`ε x = 0` as `∂₁ (-h₀ x)`. -/
theorem exact_zero (n : ℕ) : LinearMap.ker (aug n) = boundaries n 0 := by
  ext x
  constructor
  · intro hx
    rw [LinearMap.mem_ker] at hx
    rw [mem_boundaries]
    refine ⟨-(h n 0 x), ?_⟩
    have hh := homotopy_zero n x
    rw [hx, map_zero, add_zero] at hh
    rw [map_neg, hh, neg_neg]
  · intro hx
    obtain ⟨y, hy⟩ := hx
    rw [← hy, LinearMap.mem_ker, ← LinearMap.comp_apply, aug_comp_boundary,
      LinearMap.zero_apply]

/-- **Exactness in positive degrees: `ker ∂_i = im ∂_{i+1}`.** The inclusion
`im ∂_{i+1} ⊆ ker ∂_i` is `boundary_comp_boundary`; the converse is the cone contraction. -/
theorem exact_succ (n i : ℕ) : LinearMap.ker (boundary n i) = boundaries n (i+1) := by
  ext x
  constructor
  · intro hx
    rw [LinearMap.mem_ker] at hx
    rw [mem_boundaries]
    refine ⟨-(h n (i+1) x), ?_⟩
    have hh := homotopy_succ n i x
    rw [hx, map_zero, add_zero] at hh
    rw [map_neg, hh, neg_neg]
  · intro hx
    obtain ⟨y, hy⟩ := hx
    rw [← hy, LinearMap.mem_ker, ← LinearMap.comp_apply, boundary_comp_boundary,
      LinearMap.zero_apply]

/-- **The augmented chain complex of `Δ^n` is exact**: in every degree the augmented cycles
are the boundaries. This is the form the card's rank induction consumes. -/
theorem cycles_aug_eq_boundaries (n i : ℕ) : cyclesAug n i = boundaries n i := by
  cases i with
  | zero => exact exact_zero n
  | succ i => exact exact_succ n i

lemma aug_single_coeff (n : ℕ) (s : Simplices n 0) (c : ℤ) :
    aug n (Finsupp.single s c) = c := by
  simp [aug, Finsupp.lift_apply, Finsupp.sum_single_index]

def augSurjSimplex (m : ℕ) : Simplices m 0 := ⟨{Fin.mk 0 (Nat.succ_pos m)}, by simp⟩

theorem aug_surjective (n : ℕ) : Function.Surjective (aug n) := fun z =>
  ⟨Finsupp.single (augSurjSimplex n) z, aug_single_coeff n (augSurjSimplex n) z⟩

/-! ## The ranks -/

/-- Pascal's identity in the `+ 1` form the rank induction uses. -/
lemma pascal (m k : ℕ) : (m+1).choose (k+1) = m.choose k + m.choose (k+1) :=
  Nat.choose_succ_succ m k

/-- **The count of the simplices**: the `(i+1)`-element vertex subsets of `Fin (n+1)` number
`C(n+1, i+1)` (`Finset.powersetCard`). -/
theorem card_simplices (n i : ℕ) : Fintype.card (Simplices n i) = (n+1).choose (i+1) := by
  have h1 : (Finset.univ.filter (fun s : Finset (Fin (n+1)) => s.card = i + 1))
      = Finset.powersetCard (i+1) (Finset.univ : Finset (Fin (n+1))) := by
    ext s
    simp [Finset.mem_powersetCard]
  rw [Fintype.card_subtype, h1, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]

/-- **The rank of the chain groups**: `rank C_i(Δ^n) = C(n+1, i+1)` (the card's first
displayed formula, `Finset.powersetCard`). -/
theorem finrank_chains (n i : ℕ) : Module.finrank ℤ (chains n i) = (n+1).choose (i+1) := by
  rw [Module.finrank_finsupp_self, card_simplices]

/-- Rank-nullity in finrank form over a domain: for a map out of a finite module, the
ranks of the range and the kernel add up to the rank of the source. -/
theorem finrank_range_add_finrank_ker {R M M' : Type} [CommRing R] [IsDomain R] [AddCommGroup M]
    [AddCommGroup M'] [Module R M] [Module R M'] [Module.Finite R M] (f : M →ₗ[R] M') :
    Module.finrank R ↥(LinearMap.range f) + Module.finrank R ↥(LinearMap.ker f)
      = Module.finrank R M := by
  have h := LinearMap.rank_range_add_rank_ker f
  have hf : Module.rank R M < ℵ₀ := Module.rank_lt_aleph0 R M
  have hf2 : Module.rank R ↥(LinearMap.range f) + Module.rank R ↥(LinearMap.ker f) < ℵ₀ :=
    h ▸ hf
  rw [Cardinal.add_lt_aleph0_iff] at hf2
  obtain ⟨h1, h2⟩ := hf2
  simp only [Module.finrank]
  rw [← Cardinal.toNat_add h1 h2]
  exact congrArg Cardinal.toNat h

/-- **The rank of the boundary groups**: `rank B_i(Δ^n) = C(n, i+1)` — the card's rank
induction. The base is the augmentation, whose range is `ℤ` itself; the step is rank-nullity
with Pascal's identity `C(n+1, i+2) = C(n, i+1) + C(n, i+2)`. -/
theorem finrank_boundaries (n : ℕ) : ∀ i,
    Module.finrank ℤ ↥(boundaries n i) = n.choose (i+1)
  | 0 => by
      have hf := finrank_range_add_finrank_ker (R := ℤ) (M := chains n 0)
        (M' := ℤ) (aug n)
      rw [show LinearMap.range (aug n) = (⊤ : Submodule ℤ ℤ) from
        LinearMap.range_eq_top.mpr (aug_surjective n), finrank_top, Module.finrank_self,
        finrank_chains n 0, exact_zero n] at hf
      have h1 : (n + 1).choose 1 = n + 1 := Nat.choose_one_right _
      have h2 : n.choose (0 + 1) = n := Nat.choose_one_right _
      rw [h1] at hf
      omega
  | i+1 => by
      have hf := finrank_range_add_finrank_ker (R := ℤ) (M := chains n (i+1))
        (M' := chains n i) (boundary n i)
      rw [show LinearMap.range (boundary n i) = boundaries n i from rfl,
        show LinearMap.ker (boundary n i) = boundaries n (i+1) from exact_succ n i,
        finrank_chains n (i+1), pascal n (i+1)] at hf
      have hIH := finrank_boundaries n i
      omega

/-- **The rank of the augmented cycle groups**: `rank Z_i = C(n, i+1)`. -/
theorem finrank_cycles_aug (n i : ℕ) :
    Module.finrank ℤ ↥(cyclesAug n i) = n.choose (i+1) := by
  rw [cycles_aug_eq_boundaries n i, finrank_boundaries n i]

/-! ## The `k`-skeleton -/

/-- The augmented `i`-cycles of the `k`-skeleton `(Δ^n)^k`, as a subgroup of the simplex's
`i`-chains. The skeleton is the subcomplex of `Δ^n` on the simplices of dimension at most
`k`: its `i`-chains are the simplex's for `i ≤ k` and trivial above `k`, its differentials
in degrees `i ≤ k` are the simplex's — deleting a vertex from an `i`-simplex of the
skeleton leaves an `(i-1)`-simplex of the skeleton — and its augmentation is the
simplex's. So its augmented cycles (`ker ε` in degree `0`, `ker ∂_i` in positive degrees)
are the simplex's `cyclesAug n i` in degrees `i ≤ k`, and trivial above `k`, where the
skeleton has no chains at all. -/
noncomputable def skCycles (n k i : ℕ) : Submodule ℤ (chains n i) :=
  if i ≤ k then cyclesAug n i else ⊥

/-- The augmented `i`-boundaries of the `k`-skeleton, as a subgroup of the simplex's
`i`-chains: the simplex's `boundaries n i` whenever the boundary map
`∂_{i+1} : C_{i+1} → C_i` is present in the skeleton — that is, for `i + 1 ≤ k` — and
trivial from degree `k` up, where the skeleton has no `(i+1)`-chains. -/
noncomputable def skBoundaries (n k i : ℕ) : Submodule ℤ (chains n i) :=
  if i + 1 ≤ k then boundaries n i else ⊥

/-- The `i`-th reduced homology of the `k`-skeleton `(Δ^n)^k` in this Δ-complex chain
model: the augmented `i`-cycles modulo the augmented `i`-boundaries, the latter read
inside the former (they are contained in them, the skeleton's `i`-boundaries being
boundaries and hence cycles). An `abbrev` so that the quotient's module instances are
found through it. -/
abbrev skHomology (n k i : ℕ) : Type :=
  (skCycles n k i) ⧸ ((skBoundaries n k i).comap (skCycles n k i).subtype)

/-- In degrees `i ≤ k` the skeleton's cycles are the simplex's: its differentials there
are the simplex's. -/
theorem skCycles_eq (n k i : ℕ) (hik : i ≤ k) :
    skCycles n k i = cyclesAug n i := by
  unfold skCycles
  rw [ite_eq_left hik]

/-- Below degree `k` the skeleton's boundaries are the simplex's: the boundary map
`∂_{i+1}` is present in the skeleton there. -/
theorem skBoundaries_eq (n k i : ℕ) (hik : i + 1 ≤ k) :
    skBoundaries n k i = boundaries n i := by
  unfold skBoundaries
  rw [ite_eq_left hik]

/-- **Below degree `k` the skeleton's cycles are its boundaries** — the card's skeleton
step, in the form its rank computation consumes: both sides are the simplex's
(`skCycles_eq`, `skBoundaries_eq`), and the simplex's augmented complex is exact
(`cycles_aug_eq_boundaries`). -/
theorem sk_cycles_aug_eq_sk_boundaries (n k i : ℕ) (hik : i < k) :
    skCycles n k i = skBoundaries n k i := by
  rw [skCycles_eq n k i (Nat.le_of_lt hik), skBoundaries_eq n k i hik,
    cycles_aug_eq_boundaries n i]

/-- **`H̃_i((Δ^n)^k) = 0` for `i < k`** — the card's boxed claim's first half. Below
degree `k` the skeleton's cycles and boundaries are the simplex's, and the simplex's
augmented complex is exact, so inside the skeleton's `i`-cycles the `i`-boundaries fill
everything: the quotient is trivial. -/
theorem subsingleton_sk_homology (n k i : ℕ) (hik : i < k) :
    Subsingleton (skHomology n k i) := by
  have h : (skBoundaries n k i).comap (skCycles n k i).subtype = ⊤ := by
    rw [skCycles_eq n k i (Nat.le_of_lt hik), skBoundaries_eq n k i hik,
      ← cycles_aug_eq_boundaries n i]
    exact Submodule.comap_subtype_self _
  exact Submodule.Quotient.subsingleton_iff.mpr h

/-- In degree `k` there are no `(k+1)`-chains in the skeleton, so its `k`-boundaries are
trivial. -/
theorem skBoundaries_top (n k : ℕ) : skBoundaries n k k = ⊥ := by
  unfold skBoundaries
  rw [ite_eq_right (by omega : ¬ (k + 1 ≤ k))]

/-- In degree `k` the boundary out of the `k`-chains is the simplex's, so the skeleton's
`k`-cycles are the simplex's. -/
theorem skCycles_top (n k : ℕ) : skCycles n k k = cyclesAug n k := by
  unfold skCycles
  rw [ite_eq_left (Nat.le_refl k)]

/-- Pulling the trivial subgroup back along an inclusion of cycles is trivial. -/
lemma comap_bot_subtype (n k i : ℕ) :
    (⊥ : Submodule ℤ (chains n i)).comap (skCycles n k i).subtype = ⊥ := by
  ext x
  simp

/-- **The reduced homology of the `k`-skeleton in degree `k` is the simplex's `k`-cycles.**
There are no `(k+1)`-chains in the skeleton, so its `k`-boundaries are trivial
(`skBoundaries_top`), and its `k`-cycles are the simplex's (`skCycles_top`). This is the
identification the card's degree-`k` computation uses: `H̃_k((Δ^n)^k) = Z_k(Δ^n)`. -/
noncomputable def skHomologyTopIso (n k : ℕ) :
    skHomology n k k ≃ₗ[ℤ] ↥(skCycles n k k) :=
  Submodule.quotEquivOfEqBot ((skBoundaries n k k).comap (skCycles n k k).subtype)
    (by rw [skBoundaries_top n k]; exact comap_bot_subtype n k k)

/-- **`H̃_k((Δ^n)^k)` is free of rank `C(n, k+1)`** — the card's boxed claim's second half.
The top homology is the simplex's `k`-cycles (`skHomologyTopIso`), a subgroup of the free
abelian group on the `k`-simplices `Simplices n k`; over `ℤ` such a subgroup of a finite
free module is free with a basis indexed by a `Fin n` (`Submodule.basisOfPid`, the
structure theorem for submodules of a finite free module over a PID), and transporting
that basis through the isomorphism is the basis of the homology. The rank is `C(n, k+1)`
by `finrank_cycles_aug`. -/
theorem sk_homology_top_basis (n k : ℕ) :
    Module.Free ℤ (skHomology n k k) ∧
      Module.finrank ℤ (skHomology n k k) = n.choose (k + 1) := by
  refine ⟨?_, ?_⟩
  · exact Module.Free.of_basis
      ((Submodule.basisOfPid (Finsupp.basisSingleOne :
        Module.Basis (Simplices n k) ℤ (chains n k)) (skCycles n k k)).2.map
        (skHomologyTopIso n k).symm)
  · rw [LinearEquiv.finrank_eq (skHomologyTopIso n k), skCycles_top,
    finrank_cycles_aug]

end LeanCategories.Homological.DeltaSimplexChains

