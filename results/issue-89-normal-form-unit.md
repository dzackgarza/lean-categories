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
