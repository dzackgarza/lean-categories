# Issue 89 — the normal-form unit: what is left, and what it must prove

**One item of #89 is open**, and it is the only one: the completeness of the presentation
`⟨S, T | S⁴, (TS)³ = S²⟩` of `SL(2, ℤ)`, i.e.

```lean
ModularGroup.Sl2zPresentationComplete : Prop := Function.Injective sl2zToGroup
```

at `LeanCategories/ForMathlib/ModularGroupPresentation.lean:201`. Everything else in that file is
proved: the relators evaluated (`S_pow_four`, `T_mul_S_pow_three_eq_S_sq`), the presentation and its
map (`sl2zRelators`, `sl2zToGroup`), surjectivity (`sl2zToGroup_surjective`), the amalgam change of
generators as a `MulEquiv` (`sl2zAmalgamEquiv`), the factor orders in both `SL(2, ℤ)` and the
presentation (`S_sq_ne_one` … `of_one_mul_of_zero_pow_six`), and for item 2 the whole semidirect
product (`gl2z_isComplement`) and the restriction of the adjoined presentation (`sl2zInGl`).

## It is not a lookup

Probe (`.scratch/wt89-probes/closeattempt.lean`, not shipped): `exact?` and `aesop` cannot close
`Function.Injective sl2zToGroup`, and `exact?` cannot close the reduced-word datum it reduces to. No
Mathlib lemma states it: there is no pushout instance for `SL(2, ℤ)` (`PushoutI` gives normal forms
only for a pushout one maps *into*), no Farey graph and no Bass–Serre theory.

## The two components, with their Lean shape

1. **Euclid descent on the first column.** With `colHeight A := max |A 0 0| |A 1 0|` (ℤ-valued), prove
   for `2 ≤ colHeight A` that there are `ε : Fin 2`, `q : ℤ`, `A'` with
   `A = S ^ (ε : ℕ) * T ^ q * A'` and `colHeight A' < colHeight A`. Inputs: `ModularGroup.coe_T_zpow`
   for the first column of `T ^ q * A`, `Matrix.mul_fin_two` for the entries, `Int.emod_lt_abs` and
   `Int.emod_add_ediv` for `|a % c| < |c|`, and — for the two degenerate cases `c = 0` and
   `|a| = |c|` — `det = 1 ⟹ gcd a c = 1`, which is Bezout from `det_fin_two_of`.
2. **The cusp stratum.** `colHeight A = 1`, i.e. the image fixes the cusp `∞` up to sign: a word there
   must be relation-equivalent to `T ^ b`. This is the vertex-stabilizer statement of the tree action
   and is what the elementary route cannot supply; it is where a formalized amalgam normal form (or
   unique reduced words for `ℤ/4 *_{ℤ/2} ℤ/6`) enters.

## Why no height descent can finish it

The descent landed by the concurrent session (`colHeight_step`, and
`exists_lift_mul_colHeight_le_one` which drives every `A` to `colHeight ≤ 1`) cannot be iterated to a
proof: the cusp stratum contains the identity, so the cusp statement *at `A = 1`* is exactly
`Function.Injective sl2zToGroup`. A second descent — on the row height `colHeight Aᵀ`, via the
transpose, which is word-realizable by `S ↦ S⁻¹`, `T ↦ S T⁻¹ S⁻¹` since `Sᵀ = S⁻¹` and
`(T⁻¹)ᵀ = S T S⁻¹` — shrinks the cusp stratum to finitely many matrices but does not help: for each
of those the obligation is still "every word evaluating here is relation-equivalent to a fixed
word", and the case `A = 1` is the theorem itself. So the missing step is a normal-form/acyclicity
theorem, not more integer arithmetic.

The consumer named in the issue — Todd–Coxeter enumeration of cosets of finite-index subgroups of
`GL(2, ℤ)` — needs (1) and (2): with only the relations already verified, an enumeration returns a
quotient of `SL(2, ℤ)`, not `SL(2, ℤ)`.

## Progress: the tiebreak in the Farey height is now a theorem (not a measurement)

The acyclicity criterion `no_closed_reduced_walk` needs a height on the Farey triangle graph with
(a) adjacent vertices of different height and (b) at most one neighbour below each vertex. (b) was
already `no_two_flips_decrease`. (a) was recorded in the module docstring as *measured* on the finite
truncation (78 triangles, 117 edges, `|entries| ≤ 5`): the only tie is the edge between the two
triangles of height four, `{0, 1, ∞}` and `{0, -1, ∞}`, and lowering `{0, 1, ∞}` to three removes it.

Both halves of that are now proved in `ModularGroupPresentation.lean` (section "The Farey height has
no ties"), for *every* Farey basis and not only the truncation:

* `core_nonneg`: two integer vectors `(P, Q)` and `(R, S)` with equal `ℓ¹`-lengths, determinant `±2`
  and coordinates congruent mod `2` have all four coordinates `±1`. Without the congruence there are
  such pairs of every size; a Farey basis supplies it because `u + v` and `u - v` differ by twice
  `v` and twice `u`.
* `triH_eq_imp_std`, `triH_flip_left`, `triH_flip_right`: an `ℓ¹` tie between the two triangles on a
  Farey side forces that side to be the standard edge `{0, ∞}` — one lemma per side of a triangle,
  the second and third by applying the first to the bases `(u, u + v)` and `(-v, u + v)`. So there is
  no tie anywhere else, and the height `4 ♣ - 2·[{0,1,∞}]` (in the tree's doubled normalization) has
  none at all.
* `stdTri_triH`: the exceptional pair is computed — both triangles have height four and each has
  neighbours of heights four, six and six — so the O(1) tiebreak separates exactly the tied pair and
  changes no other comparison.

Still open, and unchanged by this: the dictionary from a reduced word to a closed reduced walk in the
incidence graph, and the bridge from `PresentedGroup sl2zRelators` (via `amalgamPushoutEquiv`) to the
matrices these heights are read off.

## Progress: the walk's letters, moves and heights

The dictionary the previous section names as still open is a walk on the incidence graph of Farey
edges and triangles. Its first half is now in `ModularGroupPresentation.lean` (section "The letters,
their moves, and the heights of the walk"):

* `Letter` — the six letters `S`, `S³` of the `ℤ/4` factor and `R`, `R²`, `R⁴`, `R⁵` of the `ℤ/6`
  factor, i.e. every element of the two factors outside the amalgamated `⟨S²⟩`;
* `Letter.act` and `Letter.col_mul_val` — the local move of each letter on a matrix's two columns, and
  the dictionary showing it is exactly the column action of the matrix product (six concrete
  computations on the explicit matrices);
* `HT`, `EH`, `EH_mean` — the two kinds of vertex height in the doubled normalization (a triangle is
  twice its `ℓ¹` cusp sum minus the tiebreak; an edge is the mean of its two triangles);
* `HT_ne` — adjacent vertices never have equal height, now *for every Farey basis*: the `2·(B - B')`
  in the comparison can only be offset by the tiebreak when `B = B'`, which by `triH_eq_imp_std` is
  the standard edge, where `eps_add_of_std` says exactly one of the two triangles is `{0, 1, ∞}`;
* `at_most_one_down` with `downA_iff`/`downB_iff`/`downC_iff` — at most one side of a triangle has a
  lower opposite triangle, i.e. `no_two_flips_decrease` in the heights' own vocabulary.

So both hypotheses of the maximum-vertex criterion are now theorems about the walk's own heights.

What the dictionary still needs, and nothing else: the prefix products along a word, the two
comparisons between consecutive vertices (short now, from `HT_ne`, `at_most_one_down` and
`EH_mean`), the maximum-vertex argument, and the parity split — for an odd-length word the cyclic walk
has one degenerate step, and its two seam comparisons are the only finite work left.

## Progress: the three flips of a basis

The walk's comparisons are always between a triangle and the triangle opposite it across one of its
three sides. That vocabulary is now in the module (section "The three flips of a basis"):

* `flA`, `flB`, `flC` — the three flips of a Farey basis `(u, v)`, i.e. the triangles on the sides
  `{u, v}`, `{u, u + v}`, `{v, u + v}`;
* `triH_flipA/B/C` and `downA_flip/B/C` — each flip's `ℓ¹` height and the condition "this flip is
  lower", which is one of the three mutually exclusive alternatives of `no_two_flips_decrease`;
* `HT_congr`, `triF_uv`, `triF_vu`, `triF_negneg` — `HT` depends only on the triangle and its `ℓ¹`
  height, plus the three changes of basis that say so;
* `HT_ne_flipB`, `HT_ne_flipC` — the other two sides have no tie either, both from `HT_ne` by
  re-reading the triangle in the bases `(u, u + v)` and `(-v, u + v)`.

So all three sides of every Farey triangle now have strictly unequal height from their opposite
triangle. What the dictionary still needs: the prefix products along a word, the two comparisons
between consecutive vertices of the walk (now short: `HT_ne`/`HT_ne_flipB`/`HT_ne_flipC` for the step,
`EH_mean` and `at_most_one_down` for the turn), the maximum-vertex argument, and the parity split.

## Progress: the walk's prefix products, vertices and heights

The walk is read off the columns of a word's prefix products, and that data is now in the module
(section "Prefix products, and the walk's vertices and heights"):

* `Y l j` — the product of the first `j` letters of `l : List Letter`, with `Y_zero`, `Y_succ`,
  `Y_length` and the two *cyclic* forms `Y_nxt`/`Y_prv`; stepping forward across the end of the word
  uses that the whole word's product is one, and `Y_prv` is the same statement read backwards;
* `nxt`/`prv` — cyclic successor and predecessor of an index;
* `cols_nxt`/`cols_prv` — the one-step column dictionary: the columns after a step are the letter's
  move `Letter.act` applied to the columns before it, and likewise backwards. This is what turns a
  comparison between two vertices of the walk into a statement about one letter's move, one leg of
  which is a flip `flA`/`flB`/`flC`;
* `vtx`, `hgt` — the vertex at an index (edge over an `⟨S⟩`-letter, triangle over an `⟨R⟩`-letter) and
  its height.

Remaining for the dictionary: the two comparisons at each index (step: `HT_ne`, `HT_ne_flipB`,
`HT_ne_flipC`; turn: `EH_mean`, `at_most_one_down`), the maximum-vertex argument, and the parity
split with its two seam computations.

## Progress: the basis facts and the height-four bound

The walk's turn comparison at a triangle asks whether one of the two neighbouring edges is lower; since
an edge's height is the mean of its two incident triangles, that becomes "is the opposite triangle
lower in `HT`". Off the tied pair this is a strict `triH` decrease (controlled by
`no_two_flips_decrease`); on the tied pair the O(1) tiebreak can make `HT` lower while `triH` is not,
which is the one case that needs care. In the module (section "The columns of a matrix are a basis,
the flipped bases of a triangle, and height four"):

* `fdet_cols` — the columns of a matrix in `SL(2, ℤ)` are a Farey basis (from `det_entries`);
* `triF_comm'`, `triF_u_negv`, `triF_r2`, `triF_r4` — the changes of basis the letters perform on a
  triangle, so `HT` can be read off in whichever basis is convenient;
* `HT_act_r1/2/4/5` — an `⟨R⟩`-letter does not change a triangle vertex's height; `HT_negv` — the two
  bases of the flip across a side give the same height;
* `triH_ge_four` — every Farey triangle has `ℓ¹` height at least four, which rules out the second
  "tiebreak-lowered" side in that turn comparison.

Still open for the dictionary: the two per-index comparisons themselves, the maximum-vertex argument,
and the parity split.

## Progress: at most one side of a triangle is lower in the tiebroken height

The walk's turn comparison at a triangle becomes "are two of the triangle's flips lower?".
`no_two_flips_decrease` answers that for the `ℓ¹` height; the tiebreak can upset it, and this is now
closed in the module (section "At most one side of a triangle is lower in the tiebroken height"):

* `HT_lt_decrease` — `HT` lower implies either a strict `triH` decrease or `triH` equal with the
  tiebreak deciding it (`eps u v = 0`, `eps x y = 1`);
* `triF_of_eps_one`, `triH_of_eps_one` — `eps = 1` means the triangle is `{0,1,∞}`, of `ℓ¹` height 4;
* `fdet_flipA/B/C` and `triF_flA_ne_flB`, `triF_flA_ne_flC` — the flips of a basis are bases, and the
  flips across two sides are distinct triangles;
* `not_both_AB`, `not_both_AC` — at most one of two given flips is lower in `HT`; apart from the `ℓ¹`
  case the only way to fail would be the tiebreak lowering one flip, which pins the triangle's `ℓ¹`
  height at four and `triH_ge_four` then rules out the second.

Still open: `EH`'s invariance under `⟨S⟩`-letters, the two per-letter comparison statements (a
near-compiling draft exists), the maximum-vertex argument, and the parity split.

## Progress: both comparisons of the walk

The two hypotheses of the maximum-vertex criterion are now theorems about the walk's own heights, for
every letter, with the basis `(u, v)` arbitrary (section "The two comparisons of the walk"):

* `EH_act_s1`, `EH_act_s3` — an `⟨S⟩`-letter does not change the height of an *edge* vertex (the mirror
  of `HT_act_r*`, which says an `⟨R⟩`-letter does not change a *triangle's* height);
* `step_ne` — **the step**: consecutive vertices have different heights. Over an `⟨S⟩`-letter the next
  vertex is the flip `A` and `EH` is the mean of the two triangles' `HT`, so equality would be a tie
  (`HT_ne`); over an `⟨R⟩`-letter the same arithmetic gives `HT_ne_flipB`/`HT_ne_flipC`;
* `turn_not_both` — **the turn**: the two neighbours of a vertex are never both lower. At an edge this
  is immediate (the mean), at a triangle it is exactly "at most one flip is lower"
  (`not_both_AB`/`not_both_AC`).

Remaining for the dictionary is only indexing: read these at the walk's own indices (the one-step
dictionary `cols_nxt`/`cols_prv` does the transport), run the maximum-vertex argument, and split by the
parity of the word's length.

## Progress: the walk's height as a function of the index

The maximum-vertex argument needs a height that is a plain function of the index, without index
proofs in the way; that is now in the module (section "The walk's height as a function of the index"):
`U l k`, `V l k` are the two columns of the prefix product, `H l k` the walk's height there (junk off
the word), `H_eq` reads it off, and `H_next` expresses the height one step on in the basis at `k` (the
letter's move applied to that basis, through `cols_nxt`).

Still open: the same statement one step *back* (`H_prev`, which needs the letter case analysis plus
`cols_prv`), the maximum-vertex argument, and the parity split.

## Progress: the walk's height without index proofs

Case analysis on the letter at an index kept tripping over the index proof carried by `l[k]`; the
module now isolates that (section "The walk's height without index proofs"): `L l k` is the letter at
`k` as a total function, `Hk l k` the walk's height built from it, `L_eq`/`L_isS` relate them on the
word. Also here `bool_eq_not` (two unequal booleans are mutual negations — how "the next letter is the
other type" becomes an equation), `fdet_UV`, `HT_ne_EH`, the generic invariance lemmas
`HT_act_of_false`/`EH_act_of_true` (by the letter's type, not six case splits), and `Hk_next` — the
height one step on in the basis at `k`.

Still open: `Hk_prev` (its direct proof exceeds the heartbeat limit because `simp` unfolds `Y` at the
`prv` index; it needs the invariance facts restated in `U`/`V` form), the maximum-vertex argument, and
the parity split.

## Progress: the walk closes

The dictionary is now proved in the form the walk decides it (section "The walk closes"):
`Hk_prev` is the height one step back in the basis at `k`; `step_Hk` and `turn_Hk` are the two
comparisons; `no_cycle` is the maximum-vertex argument (on the highest vertex both neighbours are
lower, which the turn forbids); and `no_reduced_word_dies` states it:

> a nonempty cyclically alternating word of the six letters has product one only if it is empty.

So the "no nonempty reduced word dies" half of the tree unit is done for cyclically alternating
words, i.e. for even length. What remains is the parity split — an odd-length word is only linearly
alternating, `hcyc` fails, and the walk has one degenerate step at the seam — and then the bridge from
`PresentedGroup sl2zRelators` to these letters.

## Progress: the two ends of the walk

For the odd-length parity split the two ends must be pinned: at index `0` the basis is the identity, so
`Hk_zero` reads the height there off `(E1, E2)`, and `EH_std = 15`, `HT_std = 14` are those two
numbers. (The first step of the walk goes strictly up at that end — `16` when `l[0]` is `⟨S⟩`-type,
`19` when it is `⟨R⟩`-type — which is what rules out index `0` being a maximum.)

Still open: the mirror statement at the last index (the columns of the inverse of the last letter), the
odd-length maximum-vertex argument built on the two ends, and then the bridge from
`PresentedGroup sl2zRelators`.

## Progress: one step into the walk

`Hk_one` writes the height at index `1` of the walk in terms of the first letter's matrix, i.e. the
mirror of `Hk_zero` at the near seam the odd-length case needs. The remaining half there is the
six-value arithmetic comparison `Hk l 0 < Hk l 1` (15 against 16 for an `⟨S⟩`-letter, 14 against 19 or
23 for an `⟨R⟩`-letter), and then the far end and the odd-length maximum-vertex argument.

## Progress: the two seam comparisons at the near end

For the odd-length case the walk's ends are now pinned (section "The two seam comparisons at the near
end"):

* `Hk_zero_lt_one` — the first step goes strictly up: `15` against `16` for the two `⟨S⟩`-letters, `14`
  against `19, 19, 19, 23` for the four `⟨R⟩`-letters (six `decide`s);
* `Hk_last` — the last step returns to the *same* height when both ends carry the same type (the
  odd-length seam), because the columns at index `0` are the last letter's move applied to the columns
  at `n - 1` and the invariance lemmas identify the heights.

So neither end can be the highest vertex of an odd-length walk; what remains is the maximum-vertex
argument at an interior index, and then the bridge to the presented group.

## The parity split is closed: no nonempty reduced word dies

`no_die` is now a theorem in the module: **a nonempty word of the six letters `S`, `S³`, `R`, `R²`,
`R⁴`, `R⁵`, whose consecutive letters lie in different factors, has product one only if it is empty.**
That is the statement the module docstring names as the surviving half of the issue.

* `isS_parity` — in a linearly alternating word a letter's type depends only on the parity of its
  index;
* `no_die_odd` — the odd-length case: by the two seam comparisons (`Hk_zero_lt_one`: the first step
  strictly rises; `Hk_last`: the last step returns to the first height) neither end of the walk is its
  highest vertex, so the highest vertex is interior, where both neighbours are lower and `turn_Hk`
  forbids it;
* `no_die` — both parities (even length is also cyclically alternating, so `no_reduced_word_dies`
  applies).

Remaining before `Sl2zPresentationComplete`: the glue from `PresentedGroup sl2zRelators` — every
element of the presented group must be shown to be a base element times such a word.
