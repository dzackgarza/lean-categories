/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 License as described in the file LICENSE.
-/
module

public import Mathlib.LinearAlgebra.Dimension.RankNullity
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.Algebra.EuclideanDomain.Int
public import LeanCategories.Topology.BarycentricSubdivision

/-!
# `E-HAT-2.2-16`: the barycentric chain model of the standard simplex

The barycentric chain claim the card's repaired proof uses is that the chains it writes
down — the free abelian groups on the `(i+1)`-element vertex subsets of `Δ^n` — are the
chains of the **barycentric subdivision** of `Δ^n`.  This file certifies it, and
certifies the barycentric chain complex itself, without routing through a barycentric
subdivision functor.

## Why no `SSet.B` and no `sd ⟶ B` is needed

Mathlib at the pin has the subdivision functor `SSet.sd` and its right adjoint `ex`
(`Mathlib/AlgebraicTopology/SimplicialSet/Subdivision.lean:29-61`) but neither `SSet.B`
(the functor sending `X` to the nerve of the poset of its nondegenerate simplices) nor a
natural transformation `sd ⟶ B`; the file says so itself, in its TODO at
`Subdivision.lean:19-23`.  `B` is wanted for an *arbitrary* simplicial set, where the
identification `sd X ≅ B X` has to be compared map by map.  For the standard simplex it
does not:

* `SSet.sd` is the left Kan extension of `SimplexCategory.sd`, and
  `SSet.stdSimplex.sdIso : stdSimplex ⋙ sd ≅ SimplexCategory.sd` (`:66-70`) identifies
  the subdivision of `Δ^n` with `SimplexCategory.sd.obj ⦋n⦌` on the nose;
* that object is, by its definition (`:29-38`), the **nerve of the poset of nonempty
  vertex subsets** of `Fin (n+1)`, so its `k`-simplices are the chains of `k+1` nonempty
  faces and its nondegenerate ones are the *strict* chains — the flags below;
* the poset of nondegenerate simplices of `Δ^n` *is* the poset of nonempty vertex
  subsets (a nondegenerate `i`-simplex of the representable `Δ^n` is an injective
  monotone `⦋i⦌ ↪ ⦋n⦌`, i.e. an `(i+1)`-element subset), so the two nerves `B (Δ^n)`
  and `sd (Δ^n)` are the same nerve.

So at `Δ^n` the identification of `sd` with `B` is an unfolding of the definition of the
nerve, not a comparison of two constructions: what is left to prove is exactly the
chain-level content below, and it is proved for every `n` and every degree.  The scope of
this file is that content, on the standard simplex; the functor `B` and the natural
transformation `sd ⟶ B` are **not** defined here, and nothing below is a statement about
an arbitrary simplicial set.

## What is proved

* `IsFlagChain`, `Flag`: a `k`-simplex of the barycentric subdivision of `Δ^n` is a chain
  of `k+1` nonempty faces, i.e. a flag `F₀ ⊂ F₁ ⊂ ⋯ ⊂ F_k`;
* `bchains`, `boundary`: the barycentric chain group in degree `k` is the free abelian
  group on those flags, with the alternating-deletion boundary;
* `aug_comp_boundary`, `boundary_comp_boundary`: the augmented complex is a complex;
* `homotopy_succ`, `homotopy_zero`, `aug_h_minus`: the cone contraction that appends the
  full face `Finset.univ`, which is where the contractibility of the subdivision enters;
* `exact_zero`, `exact_succ`, `cycles_aug_eq_boundaries`, `subsingleton_baryHomology`: the
  barycentric chain complex of `Δ^n` is augmented-exact and its reduced homology
  vanishes, so it is a model of the simplex's chains and not a formal device;
* `isFlagChain_image`, `card_image`: the repo's own barycentric-subdivision data
  (`LeanCategories.Topology.IsBarycentricFaceFlag`, the `Fin`-indexed flags of
  `BarycentricSubdivision.lean`) map onto the flags of this model, so the two
  presentations of a subdivision simplex agree;
* `exists_faceFlag_top`: **the card's chains are the barycentric ones** — for every
  `(k+1)`-element vertex subset `s` there is a barycentric `k`-simplex of `Δ^n` with face
  sizes `1, 2, …, k+1` whose top face is `s`.  Its `k`-chains are therefore the
  maximal simplices of the subdivision of the `k`-simplex `s`, one per ordering of `s`,
  and the ordering the card leaves implicit is the one `Finset` carries.

LC-09 search record (queries against this repository and the pinned Mathlib): `rg
-barycentric chain`, `rg -IsBarycentricFaceFlag`, `rg -SSet.B`, `rg -Subdivision` over
`LeanCategories/`, `corpus/` and `/opt/mathlib/Mathlib/AlgebraicTopology/SimplicialSet/`.
The flag data is the local `LeanCategories.Topology.BarycentricFaceFlag` (ported from
`deancureton/sphere-six-complex`, corpus row `FC07-C02-U035`); the chain complex and its
contraction are not in Mathlib at the pin and mirror the shape of
`LeanCategories.Homological.DeltaSimplexChains` — same card, same contraction, on flags
instead of vertex subsets.
-/

@[expose] public section

namespace LeanCategories.Homological.BarycentricChains

open Finset LeanCategories.Topology

/-! ## The model -/

/-- A set of faces of `Δ^n` is a **flag** when its members are nonempty and pairwise
nested.  Read as a simplex of the barycentric subdivision: `S` is a chain of `S.card`
nonempty faces, and its members are the barycentres the simplex is spanned by. -/
def IsFlagChain {n : ℕ} (S : Finset (Finset (Fin (n + 1)))) : Prop :=
  (∀ F ∈ S, F.Nonempty) ∧ ∀ F ∈ S, ∀ G ∈ S, F ≠ G → (F ⊆ G ∨ G ⊆ F)

/-- The `i`-simplices of the barycentric subdivision of `Δ^n`: the flags of `i+1`
nonempty faces.  An `i`-simplex of the subdivision spans the barycentres of its faces, so
its faces are what this indexes — the faces of the original simplex, `i+1` of them. -/
abbrev Flag (n i : ℕ) : Type :=
  {S : Finset (Finset (Fin (n + 1))) // S.card = i + 1 ∧ IsFlagChain S}

/-- The `i`-chains of the barycentric subdivision of `Δ^n`: the free abelian group on its
`i`-simplices, i.e. on the flags of `i+1` nonempty faces. -/
abbrev bchains (n i : ℕ) : Type := Flag n i →₀ ℤ

/-- The position of the face `F` in a flag `S`, read as the number of faces of `S` smaller
than it.  On a flag this is a bijection onto `Fin S.card`; the total definition is what
lets the boundary and its square be stated without side conditions. -/
def posOf {n : ℕ} (S : Finset (Finset (Fin (n + 1)))) (F : Finset (Fin (n + 1))) : ℕ :=
  (S.filter (· ⊂ F)).card

/-- The chain `c • [S]` in degree `i`: the generator indexed by `S` when `S` is an
`i`-simplex (a flag of `i+1` faces), `0` otherwise.  Total, as in the card's model, which
is what the pair-indexed sums of the boundary-square computation need. -/
noncomputable def genC (n i : ℕ) (S : Finset (Finset (Fin (n + 1)))) (c : ℤ) :
    bchains n i := by
  classical
  exact if h : S.card = i + 1 ∧ IsFlagChain S then Finsupp.single ⟨S, h⟩ c else 0

/-- The boundary `∂ : C_{j+1} → C_j` of the barycentric subdivision: on a flag, the
alternating sum over the deletions of its faces, the sign of a deletion being the position
of the deleted face. -/
noncomputable def boundary (n j : ℕ) : bchains n (j + 1) →ₗ[ℤ] bchains n j :=
  (Finsupp.llift (bchains n j) ℤ ℤ (Flag n (j + 1))) fun S =>
    ∑ F ∈ S.1, genC n j (S.1.erase F) ((-1 : ℤ) ^ posOf S.1 F)

/-- The cone contraction `h : C_j → C_{j+1}` appending the full face: `S ↦ (-1)^j`
times the flag `S ∪ {univ}`, the cardinality guard in `genC` sending a repeated `univ` to
`0`.  The apex is the full face because it contains every face, which is what makes the
subdivision of a simplex contractible. -/
noncomputable def h (n j : ℕ) : bchains n j →ₗ[ℤ] bchains n (j + 1) :=
  (Finsupp.llift (bchains n (j + 1)) ℤ ℤ (Flag n j)) fun S =>
    genC n (j + 1) (insert (Finset.univ : Finset (Fin (n + 1))) S.1) ((-1 : ℤ) ^ j)

/-- The augmentation `ε : C_0 → ℤ` of the barycentric subdivision: the sum of the
coefficients of the vertices, i.e. of the barycentres of the nonempty faces. -/
noncomputable def aug (n : ℕ) : bchains n 0 →ₗ[ℤ] ℤ :=
  (Finsupp.llift ℤ ℤ ℤ (Flag n 0)) fun _ => 1

/-- The degree `-1` part of the cone contraction: `h₋₁(z) = -z • [univ]`, the signed
vertex at the barycentre of the whole simplex. -/
noncomputable def hMinus (n : ℕ) : ℤ →ₗ[ℤ] bchains n 0 :=
  LinearMap.toSpanSingleton ℤ (bchains n 0)
    (-(genC n 0 ({Finset.univ} : Finset (Finset (Fin (n + 1)))) (1 : ℤ)))

/-! ## Flags: subsets of flags are flags, and the full face may be appended -/

lemma isFlagChain_empty {n : ℕ} : IsFlagChain (∅ : Finset (Finset (Fin (n + 1)))) := by
  refine ⟨?_, ?_⟩
  · intro F hF
    simp at hF
  · intro F hF
    simp at hF

lemma IsFlagChain.subset {n : ℕ} {S T : Finset (Finset (Fin (n + 1)))} (h : IsFlagChain S)
    (hTS : T ⊆ S) : IsFlagChain T :=
  ⟨fun F hF => h.1 F (hTS hF),
    fun F hF G hG hne => h.2 F (hTS hF) G (hTS hG) hne⟩

lemma IsFlagChain.insert_univ {n : ℕ} {S : Finset (Finset (Fin (n + 1)))}
    (h : IsFlagChain S) :
    IsFlagChain (insert (Finset.univ : Finset (Fin (n + 1))) S) := by
  constructor
  · intro F hF
    rcases Finset.mem_insert.1 hF with rfl | hF
    · exact Finset.univ_nonempty
    · exact h.1 F hF
  · intro F hF G hG hne
    rcases Finset.mem_insert.1 hF with rfl | hF <;>
      rcases Finset.mem_insert.1 hG with rfl | hG
    · exact absurd rfl hne
    · exact Or.inr (Finset.subset_univ G)
    · exact Or.inl (Finset.subset_univ F)
    · exact h.2 F hF G hG hne

lemma IsFlagChain.erase {n : ℕ} {S : Finset (Finset (Fin (n + 1)))} (h : IsFlagChain S)
    (F : Finset (Fin (n + 1))) : IsFlagChain (S.erase F) :=
  h.subset (Finset.erase_subset F S)

lemma ssubset_univ_iff {n : ℕ} {F : Finset (Fin (n + 1))} :
    F ⊂ Finset.univ ↔ F ≠ Finset.univ := by
  rw [Finset.ssubset_iff_subset_ne]
  exact ⟨fun h => h.2, fun h => ⟨Finset.subset_univ F, h⟩⟩

lemma not_ssubset_self {n : ℕ} (F : Finset (Fin (n + 1))) : ¬ F ⊂ F :=
  fun h => (Finset.ssubset_iff_subset_ne.1 h).2 rfl

lemma not_univ_ssubset {n : ℕ} (F : Finset (Fin (n + 1))) : ¬ Finset.univ ⊂ F := by
  intro h
  refine (Finset.ssubset_iff_subset_ne.1 h).2 ?_
  exact Finset.Subset.antisymm (Finset.ssubset_iff_subset_ne.1 h).1 (Finset.subset_univ F)

/-! ## The position of a deleted face -/

lemma not_ssubset_of_ssubset {n : ℕ} {F G : Finset (Fin (n + 1))} (h : F ⊂ G) : ¬ G ⊂ F :=
  fun h' => (Finset.ssubset_iff_subset_ne.1 h).2
    (Finset.Subset.antisymm (Finset.ssubset_iff_subset_ne.1 h).1
      (Finset.ssubset_iff_subset_ne.1 h').1)

lemma pos_of_erase_lt {n : ℕ} {S : Finset (Finset (Fin (n + 1)))} {F G : Finset (Fin (n + 1))}
    (hF : F ∈ S) (hFG : F ⊂ G) : posOf (S.erase F) G = posOf S G - 1 := by
  rw [posOf, posOf, Finset.filter_erase,
    Finset.card_erase_of_mem (Finset.mem_filter.2 ⟨hF, hFG⟩)]

lemma pos_of_erase_of_notMem {n : ℕ} {S : Finset (Finset (Fin (n + 1)))}
    {F G : Finset (Fin (n + 1))} (h : ¬ F ⊂ G) : posOf (S.erase F) G = posOf S G := by
  have hF : F ∉ S.filter (· ⊂ G) := fun hmem => h (Finset.mem_filter.1 hmem).2
  rw [posOf, posOf, Finset.filter_erase, Finset.erase_eq_of_notMem hF]

lemma pos_of_univ {n : ℕ} {S : Finset (Finset (Fin (n + 1)))}
    (h : (Finset.univ : Finset (Fin (n + 1))) ∉ S) :
    posOf S (Finset.univ : Finset (Fin (n + 1))) = S.card := by
  have h2 : S.filter (· ⊂ (Finset.univ : Finset (Fin (n + 1)))) = S := by
    refine Finset.filter_true_of_mem fun F hF => ?_
    exact ssubset_univ_iff.2 fun heq => h (heq ▸ hF)
  rw [posOf, h2]

lemma pos_of_insert_univ {n : ℕ} (S : Finset (Finset (Fin (n + 1))))
    (h : (Finset.univ : Finset (Fin (n + 1))) ∉ S) :
    posOf (insert (Finset.univ : Finset (Fin (n + 1))) S)
      (Finset.univ : Finset (Fin (n + 1))) = S.card := by
  have h1 : (insert (Finset.univ : Finset (Fin (n + 1))) S).filter
      (· ⊂ (Finset.univ : Finset (Fin (n + 1)))) = S := by
    rw [Finset.filter_insert]
    simp only [not_ssubset_self, ite_false]
    refine Finset.filter_true_of_mem fun F hF => ?_
    exact ssubset_univ_iff.2 fun heq => h (heq ▸ hF)
  rw [posOf, h1]

lemma pos_of_univ_mem {n : ℕ} {S : Finset (Finset (Fin (n + 1)))}
    (h : (Finset.univ : Finset (Fin (n + 1))) ∈ S) :
    posOf S (Finset.univ : Finset (Fin (n + 1))) = S.card - 1 := by
  have h1 : S.filter (· ⊂ (Finset.univ : Finset (Fin (n + 1)))) =
      S.erase Finset.univ := by
    ext F
    simp only [Finset.mem_filter, Finset.mem_erase]
    exact ⟨fun hm => ⟨ssubset_univ_iff.1 hm.2, hm.1⟩,
      fun hm => ⟨hm.2, ssubset_univ_iff.2 hm.1⟩⟩
  rw [posOf, h1, Finset.card_erase_of_mem h]

lemma pos_of_univ_notMem_eq {n : ℕ} {S : Finset (Finset (Fin (n + 1)))}
    {F : Finset (Fin (n + 1))} :
    posOf (insert (Finset.univ : Finset (Fin (n + 1))) S) F = posOf S F := by
  have h1 : (insert (Finset.univ : Finset (Fin (n + 1))) S).filter (· ⊂ F)
      = S.filter (· ⊂ F) := by
    rw [Finset.filter_insert]
    exact ite_eq_right (not_univ_ssubset F)
  rw [posOf, posOf, h1]


/-! ## The generators -/

lemma gen_c_of_card (n i : ℕ) {S : Finset (Finset (Fin (n + 1)))} (c : ℤ)
    (h : S.card = i + 1 ∧ IsFlagChain S) : genC n i S c = Finsupp.single ⟨S, h⟩ c := by
  classical
  simp only [genC, dite_eq_left h]

lemma gen_c_smul (n i : ℕ) (S : Finset (Finset (Fin (n + 1)))) (c d : ℤ) :
    c • genC n i S d = genC n i S (c * d) := by
  classical
  by_cases h : S.card = i + 1 ∧ IsFlagChain S
  · rw [gen_c_of_card _ _ _ h, gen_c_of_card _ _ _ h, Finsupp.smul_single', mul_comm]
  · simp only [genC, dite_eq_right h, smul_zero]

lemma single_smul_one {α : Type} {a : α} (c : ℤ) :
    Finsupp.single a c = c • Finsupp.single a (1 : ℤ) := by
  rw [Finsupp.smul_single', mul_one]

lemma boundary_single (n j : ℕ) (s : Flag n (j + 1)) :
    boundary n j (Finsupp.single s 1) =
      ∑ F ∈ s.1, genC n j (s.1.erase F) ((-1 : ℤ) ^ posOf s.1 F) := by
  simp only [boundary, Finsupp.llift_apply, Finsupp.lift_apply, Finsupp.sum_single_index,
    one_smul, zero_smul]

lemma boundary_gen_c (n j : ℕ) {t : Finset (Finset (Fin (n + 1)))} (c : ℤ)
    (ht : t.card = j + 2 ∧ IsFlagChain t) :
    boundary n j (genC n (j + 1) t c) =
      ∑ F ∈ t, genC n j (t.erase F) (c * (-1 : ℤ) ^ posOf t F) := by
  rw [gen_c_of_card _ _ c (by simpa using ht), single_smul_one, map_smul, boundary_single,
    Finset.smul_sum]
  exact Finset.sum_congr rfl fun F _ => gen_c_smul n j (t.erase F) c _

lemma h_single (n j : ℕ) (s : Flag n j) :
    h n j (Finsupp.single s 1) =
      genC n (j + 1) (insert (Finset.univ : Finset (Fin (n + 1))) s.1) ((-1 : ℤ) ^ j) := by
  simp only [h, Finsupp.llift_apply, Finsupp.lift_apply, Finsupp.sum_single_index,
    one_smul, zero_smul]

lemma h_gen_c (n j : ℕ) {t : Finset (Finset (Fin (n + 1)))} (c : ℤ)
    (ht : t.card = j + 1 ∧ IsFlagChain t) :
    h n j (genC n j t c) =
      genC n (j + 1) (insert (Finset.univ : Finset (Fin (n + 1))) t) (c * (-1 : ℤ) ^ j) := by
  rw [gen_c_of_card _ _ c ht, single_smul_one, map_smul, h_single]
  exact gen_c_smul n (j + 1) (insert (Finset.univ : Finset (Fin (n + 1))) t) c _

lemma aug_single (n : ℕ) (s : Flag n 0) : aug n (Finsupp.single s 1) = 1 := by
  simp only [aug, Finsupp.llift_apply, Finsupp.lift_apply, Finsupp.sum_single_index,
    one_smul, zero_smul]

lemma aug_gen_c (n : ℕ) {t : Finset (Finset (Fin (n + 1)))} (c : ℤ)
    (ht : t.card = 0 + 1 ∧ IsFlagChain t) : aug n (genC n 0 t c) = c := by
  rw [gen_c_of_card _ _ c (by simpa using ht), single_smul_one, map_smul, aug_single,
    smul_eq_mul, mul_one]

/-! ## Generators: auxiliary lemmas -/

lemma linearMap_ext_single {X M : Type} [AddCommGroup M] [Module ℤ M]
    {f g : (X →₀ ℤ) →ₗ[ℤ] M}
    (h : ∀ s : X, f (Finsupp.single s 1) = g (Finsupp.single s 1)) :
    f = g :=
  Finsupp.basisSingleOne.ext fun s => by simpa using h s

lemma gen_c_of_ne_card (n i : ℕ) {S : Finset (Finset (Fin (n + 1)))} (c : ℤ)
    (h : ¬ (S.card = i + 1 ∧ IsFlagChain S)) : genC n i S c = 0 := by
  classical
  simp only [genC, dite_eq_right h]

lemma gen_c_add (n i : ℕ) (S : Finset (Finset (Fin (n + 1)))) (c d : ℤ) :
    genC n i S c + genC n i S d = genC n i S (c + d) := by
  classical
  by_cases h : S.card = i + 1 ∧ IsFlagChain S
  · rw [gen_c_of_card _ _ c h, gen_c_of_card _ _ d h, gen_c_of_card _ _ (c + d) h,
      ← Finsupp.single_add]
  · rw [gen_c_of_ne_card _ _ c h, gen_c_of_ne_card _ _ d h,
      gen_c_of_ne_card _ _ (c + d) h, add_zero]

lemma gen_c_zero (n i : ℕ) (S : Finset (Finset (Fin (n + 1)))) : genC n i S 0 = 0 := by
  classical
  by_cases h : S.card = i + 1 ∧ IsFlagChain S
  · rw [gen_c_of_card _ _ (0 : ℤ) h, Finsupp.single_zero]
  · exact gen_c_of_ne_card _ _ 0 h

lemma gen_c_neg (n i : ℕ) (S : Finset (Finset (Fin (n + 1)))) (c : ℤ) :
    genC n i S (-c) = -(genC n i S c) := by
  classical
  by_cases h : S.card = i + 1 ∧ IsFlagChain S
  · rw [gen_c_of_card _ _ _ h, gen_c_of_card _ _ c h, Finsupp.single_neg]
  · rw [gen_c_of_ne_card _ _ _ h, gen_c_of_ne_card _ _ c h, neg_zero]

lemma gen_c_smul_single (n i : ℕ) (s : Flag n i) (c : ℤ) :
    genC n i s.1 c = c • Finsupp.single s (1 : ℤ) := by
  rw [gen_c_of_card _ _ c s.2, ← single_smul_one]

lemma neg_one_pow_odd (m : ℕ) : (-1 : ℤ) ^ (2 * m + 1) = -1 := by
  induction m with
  | zero => norm_num
  | succ m ih => rw [show 2 * (m + 1) + 1 = 2 * m + 1 + 2 by omega, pow_add, ih]; norm_num

lemma neg_one_pow_succ (j : ℕ) : (-1 : ℤ) ^ (j + 1) = -(-1 : ℤ) ^ j := by
  rw [pow_succ, mul_neg_one]

lemma neg_one_pow_pair_cancel (A B : ℕ) (h : 1 ≤ B) :
    (-1 : ℤ) ^ A * (-1 : ℤ) ^ (B - 1) + (-1 : ℤ) ^ B * (-1 : ℤ) ^ A = 0 := by
  rw [← pow_add, ← pow_add, show B + A = A + (B - 1) + 1 by omega, pow_succ, mul_neg_one]
  ring

/-! ## A two-element flag -/

lemma pos_two {n : ℕ} {F G : Finset (Fin (n + 1))} (hFG : F ⊂ G) :
    posOf ({F, G} : Finset (Finset (Fin (n + 1)))) F = 0 ∧
      posOf ({F, G} : Finset (Finset (Fin (n + 1)))) G = 1 := by
  have hGF : ¬ G ⊂ F := fun h => (Finset.ssubset_iff_subset_ne.1 hFG).2
    (Finset.Subset.antisymm (Finset.ssubset_iff_subset_ne.1 hFG).1
      (Finset.ssubset_iff_subset_ne.1 h).1)
  have hempty : ({F, G} : Finset (Finset (Fin (n + 1)))).filter (· ⊂ F) = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro x hx
    obtain ⟨hxs, hlt⟩ := Finset.mem_filter.1 hx
    rcases Finset.mem_insert.1 hxs with hxF | hxG
    · rw [hxF] at hlt
      exact not_ssubset_self F hlt
    · rw [Finset.mem_singleton.1 hxG] at hlt
      exact hGF hlt
  have hsingle : ({F, G} : Finset (Finset (Fin (n + 1)))).filter (· ⊂ G) = {F} := by
    ext x
    constructor
    · intro hx
      obtain ⟨hxs, hlt⟩ := Finset.mem_filter.1 hx
      rcases Finset.mem_insert.1 hxs with hxF | hxG
      · rw [Finset.mem_singleton]
        exact hxF
      · rw [Finset.mem_singleton.1 hxG] at hlt
        exact absurd hlt (not_ssubset_self G)
    · intro hx
      rw [Finset.mem_singleton] at hx
      rw [hx]
      exact Finset.mem_filter.2 ⟨Finset.mem_insert_self F {G}, hFG⟩
  constructor
  · rw [posOf, hempty, Finset.card_empty]
  · rw [posOf, hsingle, Finset.card_singleton]

lemma pos_two_swap {n : ℕ} {F G : Finset (Fin (n + 1))} (hGF : G ⊂ F) :
    posOf ({F, G} : Finset (Finset (Fin (n + 1)))) F = 1 ∧
      posOf ({F, G} : Finset (Finset (Fin (n + 1)))) G = 0 := by
  obtain ⟨hG0, hF1⟩ := pos_two hGF
  rw [Finset.pair_comm]
  exact ⟨hF1, hG0⟩

lemma erase_insert_self {n : ℕ} {F G : Finset (Fin (n + 1))} (hne : F ≠ G) :
    ({F, G} : Finset (Finset (Fin (n + 1)))).erase F = {G} := by
  ext x
  simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hxF, hx | hx⟩
    · exact absurd hx hxF
    · exact hx
  · intro hx
    exact ⟨fun h => hne (h.symm.trans (hx ▸ rfl)), Or.inr hx⟩

lemma erase_insert_other {n : ℕ} {F G : Finset (Fin (n + 1))} (hne : F ≠ G) :
    ({F, G} : Finset (Finset (Fin (n + 1)))).erase G = {F} := by
  rw [Finset.pair_comm]
  exact erase_insert_self (Ne.symm hne)

lemma singleton_isFlagChain {n : ℕ} {F : Finset (Fin (n + 1))} (h : F.Nonempty) :
    IsFlagChain ({F} : Finset (Finset (Fin (n + 1)))) := by
  constructor
  · intro X hX
    rw [Finset.mem_singleton] at hX
    rw [hX]
    exact h
  · intro X hX Y hY _
    rw [Finset.mem_singleton] at hX hY
    rw [hX, hY]
    exact Or.inl (Finset.Subset.refl F)

/-! ## The augmented complex is a complex -/

lemma sum_neg_one_pow_pair {n : ℕ} {F G : Finset (Fin (n + 1))} (hFG : F ⊂ G) :
    ∑ X ∈ ({F, G} : Finset (Finset (Fin (n + 1)))),
        (-1 : ℤ) ^ posOf ({F, G} : Finset (Finset (Fin (n + 1)))) X = 0 := by
  obtain ⟨hF0, hG1⟩ := pos_two hFG
  have hne : F ≠ G := fun h => (Finset.ssubset_iff_subset_ne.1 hFG).2 h
  rw [Finset.sum_pair hne, hF0, hG1]
  norm_num

/-- **`ε ∘ ∂₁ = 0`**, on a two-face flag. -/
lemma aug_boundary_two (n : ℕ) (S : Finset (Finset (Fin (n + 1)))) (hS : S.card = 2)
    (hchain : IsFlagChain S) : aug n (boundary n 0 (genC n 1 S 1)) = 0 := by
  classical
  obtain ⟨A, B, hne, hs⟩ := Finset.card_eq_two.1 hS
  rw [hs] at hchain hS ⊢
  rw [boundary_gen_c n 0 1 ⟨hS, hchain⟩, Finset.sum_pair hne]
  have hAmem : A ∈ ({A, B} : Finset (Finset (Fin (n + 1)))) := Finset.mem_insert_self A {B}
  have hBmem : B ∈ ({A, B} : Finset (Finset (Fin (n + 1)))) :=
    Finset.mem_insert_of_mem (Finset.mem_singleton_self B)
  have hcA : ({A} : Finset (Finset (Fin (n + 1)))).card = 0 + 1 ∧ IsFlagChain {A} :=
    ⟨rfl, singleton_isFlagChain (hchain.1 A hAmem)⟩
  have hcB : ({B} : Finset (Finset (Fin (n + 1)))).card = 0 + 1 ∧ IsFlagChain {B} :=
    ⟨rfl, singleton_isFlagChain (hchain.1 B hBmem)⟩
  rcases hchain.2 A hAmem B hBmem hne with hsub | hsub
  · obtain ⟨hA0, hB1⟩ := pos_two (Finset.ssubset_iff_subset_ne.2 ⟨hsub, hne⟩)
    rw [hA0, hB1, erase_insert_self hne, erase_insert_other hne, map_add,
      aug_gen_c n _ hcB, aug_gen_c n _ hcA]
    norm_num
  · obtain ⟨hA1, hB0⟩ := pos_two_swap (Finset.ssubset_iff_subset_ne.2 ⟨hsub, Ne.symm hne⟩)
    rw [hA1, hB0, erase_insert_self hne, erase_insert_other hne, map_add,
      aug_gen_c n _ hcB, aug_gen_c n _ hcA]
    norm_num

/-- **`ε ∘ ∂₁ = 0`** in the barycentric model. -/
theorem aug_comp_boundary (n : ℕ) : (aug n).comp (boundary n 0) = 0 := by
  refine linearMap_ext_single fun s => ?_
  rw [LinearMap.comp_apply, LinearMap.zero_apply]
  have h1 : (Finsupp.single s (1 : ℤ)) = genC n 1 s.1 1 := by
    rw [gen_c_of_card n 1 1 s.2]
  rw [h1]
  exact aug_boundary_two n s.1 s.2.1 s.2.2

/-- A double sum over the deletions is a sum over the ordered pairs of distinct faces. -/
lemma sum_pairs_erase {α M : Type} [AddCommMonoid M] [DecidableEq α] (s : Finset α)
    (f : α → α → M) :
    ∑ v ∈ s, ∑ w ∈ s.erase v, f v w =
      ∑ p ∈ (s ×ˢ s).filter (fun q : α × α => q.2 ≠ q.1), f p.1 p.2 := by
  rw [Finset.sum_filter, Finset.sum_product]
  have hEF : ∀ v : α, s.erase v = s.filter (fun w => w ≠ v) := fun v =>
    Finset.ext fun u => by simp [Finset.mem_erase, Finset.mem_filter, and_comm]
  simp_rw [hEF, Finset.sum_filter]

/-- **`∂ ∘ ∂ = 0`**, on a flag of cardinality `i + 3`: deleting `F` and then `G` and the
other way round give the same smaller flag with opposite signs, so the sum over the ordered
pairs of distinct faces cancels under the swap. -/
lemma boundary_comp_flag (n i : ℕ) (S : Finset (Finset (Fin (n + 1)))) (c : ℤ)
    (hS : S.card = i + 3 ∧ IsFlagChain S) :
    boundary n i (boundary n (i + 1) (genC n (i + 2) S c)) = 0 := by
  classical
  have hchain := hS.2
  rw [boundary_gen_c n (i + 1) c (by simpa using hS), map_sum]
  have hterm : ∀ F ∈ S, boundary n i (genC n (i + 1) (S.erase F) (c * (-1 : ℤ) ^ posOf S F))
      = ∑ G ∈ S.erase F, genC n i ((S.erase F).erase G)
          ((c * (-1 : ℤ) ^ posOf S F) * (-1 : ℤ) ^ posOf (S.erase F) G) := by
    intro F hF
    exact boundary_gen_c n i _
      ⟨by rw [Finset.card_erase_of_mem hF, hS.1]; omega, hchain.erase F⟩
  rw [Finset.sum_congr rfl hterm, sum_pairs_erase]
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
  have hcard : ((S.erase p.1).erase p.2).card = i + 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_erase_of_ne_of_mem hpne hp2),
      Finset.card_erase_of_mem hp1, hS.1]
    omega
  have hswap : ((S.erase p.2).erase p.1) = (S.erase p.1).erase p.2 := by
    ext u
    simp only [Finset.mem_erase]
    constructor
    · rintro ⟨h1, h2, h3⟩; exact ⟨h2, h1, h3⟩
    · rintro ⟨h1, h2, h3⟩; exact ⟨h2, h1, h3⟩
  have hchain1 : IsFlagChain ((S.erase p.1).erase p.2) := (hchain.erase p.1).erase p.2
  simp only [Prod.fst_swap, Prod.snd_swap]
  rw [gen_c_of_card _ _ _ ⟨hcard, hchain1⟩, hswap,
    gen_c_of_card _ _ _ ⟨hcard, hchain1⟩, ← Finsupp.single_add]
  have hzero : c * (-1 : ℤ) ^ posOf S p.1 * (-1 : ℤ) ^ posOf (S.erase p.1) p.2
      + c * (-1 : ℤ) ^ posOf S p.2 * (-1 : ℤ) ^ posOf (S.erase p.2) p.1 = 0 := by
    rcases hchain.2 p.1 hp1 p.2 hp2 (Ne.symm hpne) with hsub | hsub
    · have hlt : p.1 ⊂ p.2 := Finset.ssubset_iff_subset_ne.2 ⟨hsub, Ne.symm hpne⟩
      have e1 := pos_of_erase_lt hp1 hlt
      have e2 := pos_of_erase_of_notMem (S := S) (F := p.2) (G := p.1) (not_ssubset_of_ssubset hlt)
      have hB : 1 ≤ posOf S p.2 :=
        Finset.card_pos.2 ⟨p.1, Finset.mem_filter.2 ⟨hp1, hlt⟩⟩
      rw [e1, e2, mul_assoc, mul_assoc, ← mul_add, neg_one_pow_pair_cancel _ _ hB, mul_zero]
    · have hlt : p.2 ⊂ p.1 := Finset.ssubset_iff_subset_ne.2 ⟨hsub, hpne⟩
      have e1 := pos_of_erase_lt hp2 hlt
      have e2 := pos_of_erase_of_notMem (S := S) (F := p.1) (G := p.2) (not_ssubset_of_ssubset hlt)
      have hA : 1 ≤ posOf S p.1 :=
        Finset.card_pos.2 ⟨p.2, Finset.mem_filter.2 ⟨hp2, hlt⟩⟩
      rw [e1, e2, mul_assoc, mul_assoc, add_comm, ← mul_add,
        neg_one_pow_pair_cancel _ _ hA, mul_zero]
  rw [hzero, Finsupp.single_zero]

/-- **`∂ ∘ ∂ = 0`** in the barycentric model. -/
theorem boundary_comp_boundary (n i : ℕ) : (boundary n i).comp (boundary n (i + 1)) = 0 := by
  refine linearMap_ext_single fun s => ?_
  rw [LinearMap.comp_apply, LinearMap.zero_apply]
  have h1 : (Finsupp.single s (1 : ℤ)) = genC n (i + 2) s.1 1 := by
    rw [gen_c_of_card n (i + 2) 1 s.2]
  rw [h1]
  exact boundary_comp_flag n i s.1 1 ⟨s.2.1, s.2.2⟩


/-! ## The cone contraction -/

/-- **The cone contraction in positive degrees: `(∂h + h∂)(x) = -x`** for the barycentric
chain complex of `Δ^n`.  On a flag not containing the full face `univ`, `h` appends `univ`
and signs by `(-1)^degree`; the boundary of the appended flag produces the original flag
with the sign `(-1)^{deg+2}`, and the `h`-image of the boundary produces the remaining
terms, which cancel because `(-1)^{j+1} = -(-1)^j`.  On a flag containing `univ`, `h`
vanishes and only the deletion of `univ` survives. -/
theorem homotopy_succ (n j : ℕ) (x : bchains n (j + 1)) :
    boundary n (j + 1) (h n (j + 1) x) + h n j (boundary n j x) = -x := by
  have hL : ((boundary n (j + 1)).comp (h n (j + 1)) + (h n j).comp (boundary n j)
      + LinearMap.id) = 0 := by
    refine linearMap_ext_single fun s => ?_
    rw [LinearMap.add_apply, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.comp_apply,
      LinearMap.id_apply, LinearMap.zero_apply, h_single, boundary_single]
    by_cases hl : (Finset.univ : Finset (Fin (n + 1))) ∈ s.1
    · rw [Finset.insert_eq_of_mem hl,
        gen_c_of_ne_card n (j + 2) _ (fun hh => by
          have := hh.1; rw [s.2.1] at this; omega),
        map_zero, zero_add, map_sum,
        Finset.sum_congr rfl (fun F hF => h_gen_c n j _
          ⟨by rw [Finset.card_erase_of_mem hF, s.2.1]; omega, s.2.2.erase F⟩),
        Finset.sum_eq_single (Finset.univ : Finset (Fin (n + 1)))]
      · rw [Finset.insert_erase hl, pos_of_univ_mem hl]
        have hcoef : (-1 : ℤ) ^ ((j + 1 + 1) - 1) * (-1 : ℤ) ^ j = -1 := by
          rw [show (j + 1 + 1) - 1 = j + 1 by omega, ← pow_add,
            show j + 1 + j = 2 * j + 1 by omega]
          exact neg_one_pow_odd j
        rw [s.2.1, hcoef, gen_c_smul_single, neg_one_smul, neg_add_cancel]
      · intro F hF hne
        rw [Finset.insert_eq_of_mem (Finset.mem_erase_of_ne_of_mem (Ne.symm hne) hl),
          gen_c_of_ne_card n (j + 1) _ (fun hh => by
            have := hh.1; rw [Finset.card_erase_of_mem hF, s.2.1] at this; omega)]
      · intro hcon
        exact absurd hl hcon
    · have hcard : (insert (Finset.univ : Finset (Fin (n + 1))) s.1).card = j + 1 + 2 := by
        rw [Finset.card_insert_of_notMem hl, s.2.1]
      have hpos : ∀ u ∈ s.1, posOf (insert (Finset.univ : Finset (Fin (n + 1))) s.1) u
          = posOf s.1 u := fun u _ => pos_of_univ_notMem_eq
      have hnelast : ∀ u ∈ s.1, (Finset.univ : Finset (Fin (n + 1))) ≠ u :=
        fun u hu heq => hl (heq ▸ hu)
      have hsum1 : (∑ u ∈ s.1, genC n (j + 1)
            ((insert (Finset.univ : Finset (Fin (n + 1))) s.1).erase u)
            ((-1 : ℤ) ^ (j + 1) * (-1 : ℤ) ^
              posOf (insert (Finset.univ : Finset (Fin (n + 1))) s.1) u))
          = (∑ u ∈ s.1, genC n (j + 1)
            (insert (Finset.univ : Finset (Fin (n + 1))) (s.1.erase u))
            ((-1 : ℤ) ^ (j + 1) * (-1 : ℤ) ^ posOf s.1 u)) := by
        refine Finset.sum_congr rfl fun u hu => ?_
        rw [Finset.erase_insert_of_ne (hnelast u hu), hpos u hu]
      have hsum2 : (∑ v ∈ s.1, genC n (j + 1)
            (insert (Finset.univ : Finset (Fin (n + 1))) (s.1.erase v))
            ((-1 : ℤ) ^ posOf s.1 v * (-1 : ℤ) ^ j))
          = -(∑ u ∈ s.1, genC n (j + 1)
            (insert (Finset.univ : Finset (Fin (n + 1))) (s.1.erase u))
            ((-1 : ℤ) ^ (j + 1) * (-1 : ℤ) ^ posOf s.1 u)) := by
        rw [← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun u _ => ?_
        rw [← gen_c_neg]
        congr 1
        rw [neg_one_pow_succ]
        ring
      rw [boundary_gen_c n (j + 1) ((-1 : ℤ) ^ (j + 1)) ⟨hcard, s.2.2.insert_univ⟩,
        Finset.sum_insert hl,
        Finset.erase_insert hl, pos_of_insert_univ s.1 hl, s.2.1, map_sum,
        Finset.sum_congr rfl (fun F hF => h_gen_c n j _
          ⟨by rw [Finset.card_erase_of_mem hF, s.2.1]; omega, s.2.2.erase F⟩),
        hsum1, hsum2]
      have hcancel : genC n (j + 1) s.1 ((-1 : ℤ) ^ (j + 1) * (-1 : ℤ) ^ (j + 1 + 1))
          + (∑ u ∈ s.1, genC n (j + 1)
            (insert (Finset.univ : Finset (Fin (n + 1))) (s.1.erase u))
            ((-1 : ℤ) ^ (j + 1) * (-1 : ℤ) ^ posOf s.1 u))
          + -(∑ u ∈ s.1, genC n (j + 1)
            (insert (Finset.univ : Finset (Fin (n + 1))) (s.1.erase u))
            ((-1 : ℤ) ^ (j + 1) * (-1 : ℤ) ^ posOf s.1 u))
          + Finsupp.single s (1 : ℤ)
          = genC n (j + 1) s.1 ((-1 : ℤ) ^ (j + 1) * (-1 : ℤ) ^ (j + 1 + 1))
            + Finsupp.single s (1 : ℤ) := by
        abel
      rw [hcancel, gen_c_smul_single,
        show (-1 : ℤ) ^ (j + 1) * (-1 : ℤ) ^ (j + 2) = -1 by
          rw [← pow_add, show j + 1 + (j + 2) = 2 * (j + 1) + 1 by omega]
          exact neg_one_pow_odd (j + 1),
        neg_one_smul, neg_add_cancel]
  have hx := congrArg (fun (f : bchains n (j + 1) →ₗ[ℤ] bchains n (j + 1)) => f x) hL
  simp only [LinearMap.zero_apply, LinearMap.add_apply, LinearMap.comp_apply,
    LinearMap.id_apply] at hx
  exact eq_neg_of_add_eq_zero_left hx

/-- **The cone contraction in degree zero, on a single face.** -/
lemma homotopy_zero_flag (n : ℕ) (S : Finset (Finset (Fin (n + 1)))) (hS : S.card = 1)
    (hchain : IsFlagChain S) :
    boundary n 0 (h n 0 (genC n 0 S 1)) + hMinus n (aug n (genC n 0 S 1))
      + genC n 0 S 1 = 0 := by
  classical
  obtain ⟨a, ha⟩ := Finset.card_eq_one.1 hS
  rw [ha] at hchain ⊢
  have hchain' : IsFlagChain ({a} : Finset (Finset (Fin (n + 1)))) := hchain
  by_cases hl : a = (Finset.univ : Finset (Fin (n + 1)))
  · subst hl
    have hne : ¬ (({Finset.univ} : Finset (Finset (Fin (n + 1)))).card = 0 + 1 + 1) := by
      simp
    rw [h_gen_c n 0 1 ⟨by simp, hchain'⟩,
      show (1 : ℤ) * (-1 : ℤ) ^ (0 : ℕ) = 1 by norm_num,
      Finset.insert_eq_of_mem (Finset.mem_singleton_self _),
      gen_c_of_ne_card n 1 _ (fun hh => by
        have := hh.1; rw [Finset.card_singleton] at this; omega),
      map_zero, zero_add, aug_gen_c n 1 ⟨by simp, hchain'⟩,
      hMinus, LinearMap.toSpanSingleton_apply, one_smul,
      show genC n 0 ({Finset.univ} : Finset (Finset (Fin (n + 1)))) (1 : ℤ)
        = genC n 0 ({Finset.univ} : Finset (Finset (Fin (n + 1)))) (1 : ℤ) from rfl]
    abel
  · have hne : a ≠ (Finset.univ : Finset (Fin (n + 1))) := hl
    have halt : a ⊂ (Finset.univ : Finset (Fin (n + 1))) := ssubset_univ_iff.2 hne
    obtain ⟨hpos_a, hpos_u⟩ :=
      pos_two (F := a) (G := Finset.univ) halt
    have hcau : ({a, Finset.univ} : Finset (Finset (Fin (n + 1)))).card = 0 + 1 + 1 := by
      rw [Finset.card_insert_of_notMem, Finset.card_singleton]
      simp [hne]
    have hchain_au : IsFlagChain ({a, Finset.univ} : Finset (Finset (Fin (n + 1)))) := by
      rw [Finset.pair_comm]
      exact hchain'.insert_univ
    have hchain_u : IsFlagChain ({Finset.univ} : Finset (Finset (Fin (n + 1)))) :=
      singleton_isFlagChain Finset.univ_nonempty
    have hchain_a : IsFlagChain ({a} : Finset (Finset (Fin (n + 1)))) := hchain'
    rw [h_gen_c n 0 1 ⟨by simp, hchain'⟩,
      show (1 : ℤ) * (-1 : ℤ) ^ (0 : ℕ) = 1 by norm_num, Finset.pair_comm,
      boundary_gen_c n 0 1 ⟨hcau, hchain_au⟩,
      Finset.sum_pair hne, hpos_a, hpos_u, erase_insert_other hne,
      erase_insert_self hne,
      show (1 : ℤ) * (-1 : ℤ) ^ (0 : ℕ) = 1 by norm_num,
      show (1 : ℤ) * (-1 : ℤ) ^ (1 : ℕ) = -1 by norm_num,
      gen_c_neg, aug_gen_c n 1 ⟨by simp, hchain_a⟩, hMinus,
      LinearMap.toSpanSingleton_apply, one_smul]
    abel

/-- **The cone contraction in degree zero.** -/
theorem homotopy_zero (n : ℕ) (x : bchains n 0) :
    boundary n 0 (h n 0 x) + hMinus n (aug n x) = -x := by
  have hL : ((boundary n 0).comp (h n 0) + (hMinus n).comp (aug n) + LinearMap.id) = 0 := by
    refine linearMap_ext_single fun s => ?_
    rw [LinearMap.add_apply, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.comp_apply,
      LinearMap.id_apply, LinearMap.zero_apply]
    have hgen : (Finsupp.single s (1 : ℤ)) = genC n 0 s.1 1 := by
      rw [gen_c_of_card n 0 1 s.2]
    rw [hgen]
    exact homotopy_zero_flag n s.1 s.2.1 s.2.2
  have hx := congrArg (fun (f : bchains n 0 →ₗ[ℤ] bchains n 0) => f x) hL
  simp only [LinearMap.zero_apply, LinearMap.add_apply, LinearMap.comp_apply,
    LinearMap.id_apply] at hx
  exact eq_neg_of_add_eq_zero_left hx

/-- **The cone contraction in degree `-1`: `ε ∘ h₋₁ = -id`.** -/
theorem aug_h_minus (n : ℕ) (z : ℤ) : aug n (hMinus n z) = -z := by
  rw [hMinus, LinearMap.toSpanSingleton_apply, map_smul, map_neg,
    aug_gen_c n 1 ⟨rfl, singleton_isFlagChain (Finset.univ_nonempty)⟩, smul_eq_mul, mul_neg_one]


/-! ## The augmented complex is exact -/

/-- The group of `i`-boundaries of the barycentric model: the image of `∂ : C_{i+1} → C_i`. -/
noncomputable def boundaries (n i : ℕ) : Submodule ℤ (bchains n i) :=
  LinearMap.range (boundary n i)

/-- The group of `i`-cycles of the augmented barycentric complex: `ker ∂_i` for `i ≥ 1`,
`ker ε` in degree zero. -/
noncomputable def cyclesAug (n : ℕ) : ∀ i, Submodule ℤ (bchains n i)
  | 0 => LinearMap.ker (aug n)
  | i + 1 => LinearMap.ker (boundary n i)

theorem mem_boundaries {n i : ℕ} {x : bchains n i} :
    x ∈ boundaries n i ↔ ∃ y : bchains n (i + 1), boundary n i y = x :=
  LinearMap.mem_range

/-- **Exactness in degree zero of the barycentric model: `ker ε = im ∂₁`.** -/
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

/-- **Exactness in positive degrees of the barycentric model: `ker ∂_i = im ∂_{i+1}`.** -/
theorem exact_succ (n i : ℕ) : LinearMap.ker (boundary n i) = boundaries n (i + 1) := by
  ext x
  constructor
  · intro hx
    rw [LinearMap.mem_ker] at hx
    rw [mem_boundaries]
    refine ⟨-(h n (i + 1) x), ?_⟩
    have hh := homotopy_succ n i x
    rw [hx, map_zero, add_zero] at hh
    rw [map_neg, hh, neg_neg]
  · intro hx
    obtain ⟨y, hy⟩ := hx
    rw [← hy, LinearMap.mem_ker, ← LinearMap.comp_apply, boundary_comp_boundary,
      LinearMap.zero_apply]

/-- **The augmented barycentric chain complex of `Δ^n` is exact**: in every degree the
augmented cycles are the boundaries.  This is the contractibility of the barycentric
subdivision of the standard simplex, read at chain level: the apex is the full face, whose
barycentre is a vertex of every subdivision simplex. -/
theorem cycles_aug_eq_boundaries (n i : ℕ) : cyclesAug n i = boundaries n i := by
  cases i with
  | zero => exact exact_zero n
  | succ i => exact exact_succ n i

/-- The `i`-th reduced homology of the barycentric subdivision of `Δ^n`: the augmented
cycles modulo the augmented boundaries. -/
abbrev baryHomology (n i : ℕ) : Type :=
  (cyclesAug n i) ⧸ ((boundaries n i).comap (cyclesAug n i).subtype)

/-- **The barycentric chain complex of `Δ^n` has trivial reduced homology** — its own
`H̃`, not the card's: the model computes the homology of the contractible simplex, which is
what lets it stand in for the card's chains. -/
theorem subsingleton_baryHomology (n i : ℕ) : Subsingleton (baryHomology n i) := by
  have h : (boundaries n i).comap (cyclesAug n i).subtype = ⊤ := by
    rw [← cycles_aug_eq_boundaries n i]
    exact Submodule.comap_subtype_self _
  exact Submodule.Quotient.subsingleton_iff.mpr h

/-! ## The card's chains are the barycentric ones

The card's `k`-simplices of `Δ^n` are the `(k+1)`-element vertex subsets.  The statements
below identify them with the top-dimensional simplices of the barycentric subdivision: a
flag `f` with `(f i).card = i + 1` is a *maximal* flag of the subdivision of the
`(k+1)`-simplex `f (last k)`, and every `(k+1)`-element subset is such a top face.  This is
the sense in which the card's chains are the barycentric chains, and it is where the
ordering the card leaves implicit comes from: a maximal flag is its top face together with
an ordering of it, and `Finset` supplies one canonically. -/

lemma injective_of_isBarycentricFaceFlag {n r : ℕ} {f : BarycentricFaceFlag n r}
    (hf : IsBarycentricFaceFlag f) : Function.Injective f := by
  intro i j hij
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · exact absurd hij (Finset.ssubset_iff_subset_ne.1 (hf.2 i j h)).2
  · exact absurd hij.symm (Finset.ssubset_iff_subset_ne.1 (hf.2 j i h)).2

/-- A `Fin`-indexed barycentric-subdivision simplex read as a flag of faces: the set of
the barycentres it spans. -/
noncomputable def chainOfFlag (n r : ℕ) (f : BarycentricFaceFlag n r) :
    Finset (Finset (Fin (n + 1))) :=
  Finset.univ.image f

lemma card_chainOfFlag (n r : ℕ) (f : BarycentricFaceFlag n r)
    (hf : IsBarycentricFaceFlag f) : (chainOfFlag n r f).card = r + 1 := by
  rw [chainOfFlag, Finset.card_image_of_injective _ (injective_of_isBarycentricFaceFlag hf),
    Finset.card_univ, Fintype.card_fin]

lemma isFlagChain_chainOfFlag (n r : ℕ) (f : BarycentricFaceFlag n r)
    (hf : IsBarycentricFaceFlag f) : IsFlagChain (chainOfFlag n r f) := by
  constructor
  · intro F hF
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hF
    exact hf.1 i
  · intro F hF G hG hne
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hF
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hG
    rcases lt_trichotomy i j with h | h | h
    · exact Or.inl (Finset.ssubset_iff_subset_ne.1 (hf.2 i j h)).1
    · exact absurd (by rw [h]) hne
    · exact Or.inr (Finset.ssubset_iff_subset_ne.1 (hf.2 j i h)).1

/-- The canonical maximal flag of the barycentric subdivision of a vertex subset `s`: its
`i`-th face is the set of the `i+1` smallest vertices of `s`. -/
noncomputable def prefixFlag (n k : ℕ) (s : Finset (Fin (n + 1))) (hs : s.card = k + 1) :
    BarycentricFaceFlag n k :=
  fun i => (Finset.Iic i).image (s.orderEmbOfFin hs)

lemma prefixFlag_card (n k : ℕ) (s : Finset (Fin (n + 1))) (hs : s.card = k + 1)
    (i : Fin (k + 1)) : (prefixFlag n k s hs i).card = i.val + 1 := by
  rw [prefixFlag, Finset.card_image_of_injective _ (s.orderEmbOfFin hs).injective]
  exact Fin.card_Iic i

lemma prefixFlag_mono {n k : ℕ} (s : Finset (Fin (n + 1))) (hs : s.card = k + 1)
    {i j : Fin (k + 1)} (hij : i < j) : prefixFlag n k s hs i ⊂ prefixFlag n k s hs j := by
  refine Finset.ssubset_iff_subset_ne.2 ⟨?_, ?_⟩
  · exact Finset.image_subset_image (Finset.Iic_subset_Iic.2 hij.le)
  · intro hcon
    have h1 := prefixFlag_card n k s hs i
    have h2 := prefixFlag_card n k s hs j
    rw [hcon] at h1
    omega

lemma prefixFlag_isBarycentricFaceFlag (n k : ℕ) (s : Finset (Fin (n + 1)))
    (hs : s.card = k + 1) : IsBarycentricFaceFlag (prefixFlag n k s hs) := by
  constructor
  · intro i
    rw [← Finset.card_pos, prefixFlag_card n k s hs i]
    omega
  · intro i j hij
    exact prefixFlag_mono s hs hij

lemma prefixFlag_last (n k : ℕ) (s : Finset (Fin (n + 1))) (hs : s.card = k + 1) :
    prefixFlag n k s hs (Fin.last k) = s := by
  have huniv : Finset.Iic (Fin.last k) = (Finset.univ : Finset (Fin (k + 1))) := by
    refine Finset.eq_univ_of_forall fun j => Finset.mem_Iic.2 ?_
    exact Fin.le_last j
  rw [prefixFlag, huniv, Finset.image_orderEmbOfFin_univ s hs]

/-- **The card's chains are the barycentric ones.**  Every `(k+1)`-element vertex subset
`s` of `Δ^n` — a `k`-simplex of the card's Δ-complex model, i.e. a generator of the card's
`k`-th chain group — is the top face of a barycentric `k`-simplex of the subdivision whose
faces have the maximal sizes `1, 2, …, k+1`; the subdivision of a single `k`-simplex is
therefore indexed by exactly these flags. -/
theorem exists_faceFlag_top (n k : ℕ) (s : Finset (Fin (n + 1))) (hs : s.card = k + 1) :
    ∃ f : BarycentricFaceFlag n k, IsBarycentricFaceFlag f ∧ (∀ i, (f i).card = i.val + 1) ∧
      f (Fin.last k) = s :=
  ⟨prefixFlag n k s hs, prefixFlag_isBarycentricFaceFlag n k s hs, prefixFlag_card n k s hs,
    prefixFlag_last n k s hs⟩

/-- The same correspondence read inside the chain model: the barycentric `k`-simplices of
the subdivision of the `(k+1)`-simplex `s` are the flags of `k+1` faces of `s` whose sizes
are `1, 2, …, k+1`, and the card's `k`-chains span exactly their top faces. -/
theorem exists_flag_top (n k : ℕ) (s : Finset (Fin (n + 1))) (hs : s.card = k + 1) :
    ∃ S : Finset (Finset (Fin (n + 1))), S.card = k + 1 ∧ IsFlagChain S ∧
      (∀ F ∈ S, F ⊆ s) ∧ s ∈ S := by
  obtain ⟨f, hf, -, htop⟩ := exists_faceFlag_top n k s hs
  refine ⟨chainOfFlag n k f, card_chainOfFlag n k f hf, isFlagChain_chainOfFlag n k f hf,
    ?_, ?_⟩
  · intro F hF
    obtain ⟨i, -, hiF⟩ := Finset.mem_image.1 hF
    rw [← hiF]
    have hle : f i ⊆ f (Fin.last k) := by
      rcases eq_or_lt_of_le (Fin.le_last i) with h | h
      · rw [← h]
      · exact (Finset.ssubset_iff_subset_ne.1 (hf.2 i (Fin.last k) h)).1
    rwa [htop] at hle
  · rw [chainOfFlag, ← htop]
    exact Finset.mem_image_of_mem f (Finset.mem_univ (Fin.last k))

end LeanCategories.Homological.BarycentricChains
