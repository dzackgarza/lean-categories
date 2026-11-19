# #116 — folding a Lorentzian chamber along a diagram involution

Status at `66600d4e` on `main`, and every `file:line` and declaration name below is re-checked against
that commit. What the issue asks for, item by item, with the declaration that
carries each; then the one theorem the chamber item reduces to, its five hypotheses, and where each
comes from.

Source: Alexeev–Engel–Garza–Schaffler, *Compact moduli of Enriques surfaces of degree 2*, Nagoya Math.
J. 259 (2025), arXiv:2312.03638v2, §3.7–3.8 (printed pp. 11–13). The construction direction is the
source's: invariants, not coinvariants.

## Acceptance, item by item

| # | Item | Status | Declaration (file:line) |
|---|---|---|---|
| 1 | The fixed sublattice `M^σ` | **met** | `involutionFixedSubmodule` `Folding.lean:114` (ker of `σ − 1`); as a lattice object `invariantFixedLattice` `FoldingInvariantChamber.lean:120` |
| 2 | The folded root set (Def. 3.3 → Def. 3.7) | **met** | `foldedVector` `Folding.lean:126`; filtered set `foldedRootSet` `Folding.lean:416` |
| 3 | Its Coxeter diagram | **met** | `foldedDiagramOfRoots` `Folding.lean:480`; family/set agreement `range_foldedDiagramOfRoots_eq` `FoldingDiagramOrbits.lean:78` |
| 4 | The chamber theorem | **met as an implication; its root hypothesis fails in `T_dP`** — proved below, so it does not by itself give Lemma 3.8 for `T_dP` | `isChamberWithWalls_invariant_of_foldedRootSet` `FoldingChamberOfDefinition37.lean` |
| 5 | One worked declaration from a published folded diagram | **met** | the `E₈` block of `T_dP` folds to `E₈(2)`: `tdpFoldedE8Diagram` `FoldingDiagram.lean:385` with `tdpFoldedE8Diagram_adjacent` `:407` |
| 6 | Compiles with no `sorry` | **met** | zero `sorry`/`admit` across the `Folding*.lean` modules; **all 65 of them imported by `LeanCategories/All.lean`** (audited at this commit: 65 modules on disk, 65 `public import` lines, no gap and no stray — a module missing there is never elaborated) |

Supporting statements that are proved rather than assumed:

* `roots_mem` of the predicate is *derived* from Definition 3.7's filter, not hypothesised:
  `foldedRootSet_subset_negativeReflectiveRoots` (`FoldingInvariantChamber.lean`).
* `hstab` is *derived* from a diagram involution: `realFormOrthogonalHom_mem_rootInteriorCone`
  `FoldingChamberStability.lean:62`.
* The source's maximal-dimension hypothesis is *derived*: `exists_mem_fixedPart_interior`
  (`FoldingInvariantChamber.lean`).
* The folded roots are transverse to an interior point of the chamber, with no classification
  hypothesis: `foldedVector_pairing_ne_zero_of_mem_interior` `FoldingInvariantConverse.lean:80`.
* The trace and wall identities are stated on the invariant part `M^σ ⊗ ℝ` (`realFormFixedPart`).

## Item 4 — the chamber theorem, and what changed

**`hcomplete` is false, not merely unproved.** Earlier states of this report treated
"every negative reflective root of `M^σ` is a nonzero integer multiple of a folded wall root" as a
sufficient hypothesis one might discharge. It cannot be discharged: in the source's own instance
`T_En = U ⊕ E₈(2)` the vectors `e + (2l²−1)f + l·r₀` (with `r₀² = −4`) have square `−2`, divisibility
`1` and pairwise distinct lines, while a finite wall set has at most `|R|` folds. The small
machine-checked witness is `e10_root_not_multiple_of_wall` `FoldingE10RootNotWall.lean:148`; the
counting argument is in `FoldingInvariantChamberOfSigns`'s docstring. The sign covering fails with it
(it implies `hcomplete`).

**What replaced it.** A chain of statements, each proved:

1. `exists_smul_eq_add_involution` (`FoldingSignTransfer.lean`) — for each wall root there is a
   nonnegative `ε ∈ {1,2}` with `R + gR = ε • R^g`; `2` at a fixed wall, `1` otherwise.
2. `two_smul_eq_sum_smul_foldedVector` (same file) — a same-sign `ℤ`-combination of wall roots,
   doubled, folds to a same-sign combination of the folded roots, with coefficients `cᵢ εᵢ`. The
   factor `2` is the price of staying over `ℤ` (`cᵢ/2` is not integral).
3. `two_smul_eq_sum_smul_foldedWallFamily` (`FoldingSignTransferLattice.lean`) — the same at `M^σ`'s
   carrier, which is the form the chamber criterion consumes.
4. `isChamberWithWalls_invariant_of_two_smul_folded_signs`
   (`FoldingInvariantChamberOfTwoSmulSigns.lean`) — the chamber from a *doubled* one-sign expansion.
   The doubling costs nothing at an interior point (`⟨z, 2ρ⟩ = 2⟨z, ρ⟩`), and the nonvanishing
   `2 • ρ ≠ 0` is derived from `ρ² < 0` (`two_zsmul_ne_zero_of_pairing_neg`
   `NegativeSquareTwoZsmul.lean`), not assumed.
5. `isChamberWithWalls_invariant_of_ambient_signs` (`FoldingInvariantChamberOfAmbientSigns.lean`) —
   the composition: an ambient same-sign expansion (in the wall family of `L`) plus the class
   restriction gives the folded chamber.
6. `isChamberWithWalls_invariant_of_square_criterion` (`FoldingChamberOfSquareCriterion.lean`) — the
   class restriction in checkable form: every root of `M^σ` has square `−2`, or square `−4` with all
   ambient pairings even.
7. The fold analysis, AEGS Lemma 3.4's forward direction (**printed pp. 11–12**): a non-fixed root
   orthogonal to its image folds to a root (`isReflectiveRoot_foldedVector_of_orthogonal`
   `FoldingFoldOfRoot.lean`), while a `(−4)`-root that is *not* orthogonal to its image folds to a
   vector of non-negative square and is dropped by Definition 3.7's filter
   (`foldedWallFamily_not_mem_negativeReflectiveRoots` `FoldingFoldNonRoot.lean`).
8. `foldedWallFamily_mem_negativeReflectiveRoots` (`FoldingRootHypothesis.lean`) — hence `hroot`
   ("every fold of a wall root is a root"), which the chamber theorems had carried as a hypothesis,
   follows from three per-wall conditions: reflective, negative square, and fixed or orthogonal to
   the image. Its ingredient `isReflectiveRoot_of_mem_of_isReflectiveRoot` is the easy direction of
   Lemma 3.4: reflectivity passes from `L` to `M^σ` for a fixed vector.

**The statement everything reduces to** (`FoldingChamberOfDefinition37.lean`):

  `isChamberWithWalls_invariant_of_foldedRootSet (g) (hg) (R) (w) (hw) (hwamb) (hR) (hneg) (hcase)
  (hsq) (hamb) : IsChamberWithWalls M (toRealForm _ w) (foldedRootSet g (Set.range R))`

Its wall set is Definition 3.7's folded root set `Λ^{J=1}` (**printed p. 12**) — the object AEGS state
Lemma 3.8 for — because `range_foldedWallFamily_eq_foldedRootSet` identifies it with the range of the
indexing family once no fold is dropped, which `foldedWallFamily_mem_negativeReflectiveRoots` supplies.

with

* `hw` — an interior *lattice* vector of the folded cone. It is not derivable from the
  maximal-dimension hypothesis: AEGS's hypothesis is a chamber point in `H = PC` over `ℝ`, which
  `exists_mem_fixedPart_interior` extracts as a statement about `realFormFixedPart g`, and the earlier
  joining theorem `isChamberWithWalls_invariant_of_chamber` likewise carries a lattice `w` separately;
* `hwamb` — that vector's positivity against the *ambient* walls; positivity against the folded walls
  follows by `foldedWallFamily_pairing_pos`;
* `hR`, `hneg` — every wall root is reflective and of negative square: the diagram of `L`
  (Figure 5, **printed p. 11**);
* `hcase` — every wall root is fixed or orthogonal to its image: the arithmetic of `T_dP`, per wall
  (**printed p. 12**);
* `hsq` — every root of `M^σ` is `(−2)`, or `(−4)` with even ambient pairings: Namikawa's
  classification behind Lemma 3.4's converse (**printed p. 12**);
* `hamb` — every root of `L` is a same-sign combination of the walls: Vinberg's one-sign expansion.

The first three are checkable on the diagrams; `hamb` and one root hypothesis (`hsq`, equivalently
`hsub`) are the inputs. What is **not** a hypothesis any more: `hcomplete`, the sign covering, the
carrier identification, `hroot`, and the folded positivity `hwv`.

**The `(−2)`/`(−4)` rule is a theorem (AEGS p. 10).** The source states it on **printed p. 10**:
*"The lattices `L^±_En` and `L^±_dP` are even 2-elementary. For such lattices the roots are the
`(−2)`-vectors and the `(−4)`-vectors with `div(α) = 2`."* The forward direction is three divisibility
steps, not a classification, and it is now formalized: `pairing_eq_neg_two_or_neg_four_of_two_elementary`
(`TwoElementaryRootSquare.lean`) — for an even lattice on which `div` divides `2`, every root of
negative square has square `(−2)`, or `(−4)` with all pairings even; `square_criterion_of_two_elementary`
(same file) is that over `negativeReflectiveRoots L`. The argument: with `q = (α·α)`, reflectivity
gives `q ∣ 2(α·y)` for every `y`, two-elementary puts `2` in the ideal generated by the values, so
`q ∣ 4`; then `q < 0` and `q` even leave `q ∈ {−2, −4}`, and at `q = −4` reflectivity itself reads
`2 ∣ (α·y)`.

**What that does and does not do for `hsq`.** Applied to `M^σ` — which the source asserts is even
2-elementary, **p. 10** — the rule gives every root of `M^σ` square `(−2)` or `(−4)`: the *square*
half of `hsq`, with no classification. It does **not** give `hsq`'s second clause, which pairs the
*ambient image* `ρ^` with vectors `y ∈ L` of the ambient lattice. For such `y` one has
`⟨ρ^, y⟩ = ⟨ρ, y + gy⟩/2`, and evenness of `⟨ρ, ·⟩` on `M^σ` makes `⟨ρ^, y⟩` an integer, not
necessarily an even one; applying the rule to `L` instead would need `ρ^` to be a root of `L`, which
is `hsub` itself. So the ambient clause is not something the rule on `M^σ` supplies.

**But it is not a second input either.** Applied to `L` — which the source also asserts is even
2-elementary, **p. 10** — the rule gives `hsq`'s ambient clause verbatim at `ρ^`, and nothing more is
needed. `FoldingRootTransferEquivalence.lean` records the two implications:

* `hsub_of_hsq` — `hsq` gives `hsub`, with no hypothesis on `L` (the `(−2)`/`(−4)` case split);
* `hsq_of_hsub_of_two_elementary` — `hsub` gives `hsq`, given the p. 10 hypotheses on `L`, by the
  rule applied at `ρ^`;
* `hsub_iff_hsq_of_two_elementary` — so the two guises are one hypothesis.

That is the content of Lemma 3.4's type (3) and nothing besides: the ambient-pairing clause carries
no information beyond the reflectivity transfer. `hsq` and `hsub` may be carried interchangeably, and
the chain carries whichever is convenient — `hsub` is the weaker interface, `hsq` the one the
class-restriction corollaries are stated at.

**`hsq`'s only job in the chain is `hsub`.** `hsq` is consumed in exactly one place: to produce "the
ambient image of a root of `M^σ` is a root of `L`", the `hsub` hypothesis of
`isChamberWithWalls_invariant_of_ambient_signs` (`FoldingInvariantChamberOfAmbientSigns.lean:63`). So
the theorem is also stated at `hsub`, which is strictly weaker — one divisibility check per root
instead of a statement about all root squares:
`isChamberWithWalls_invariant_of_foldedRootSet_of_hsub` (`FoldingChamberOfAmbientRoots.lean`). In the
**white** case, where every root of `M^σ` is a `(−2)`-vector, even that property is not needed:
`isReflectiveRoot_invariantCarrierToAmbient_of_square_neg_two` gives `hsub` root by root
(`isChamberWithWalls_invariant_of_foldedRootSet_of_square_neg_two`, same module).

**Why the class restriction has that form.** A `(−2)`-vector of an integral lattice is always
reflective (`−2 ∣ 2·anything`), so a `(−2)`-root of `M^σ` is a root of `L`
(`isReflectiveRoot_invariantCarrierToAmbient_of_square_neg_two` `FoldingNegativeTwoRoots.lean:59`). A `(−4)`-vector
is reflective exactly when all its pairings are even: `−4 ∣ 2⟨x,y⟩ ⟺ 2 ∣ ⟨x,y⟩`
(`isReflectiveRoot_iff_two_dvd_pairing` `FoldingNegativeFourRoots.lean`). So the roots that can fail to
be roots of `L` are precisely the `(−4)`-ones with an odd pairing — AEGS Lemma 3.4's type (3)
(**printed p. 12**: `div(α^I) ≠ 2` in `T_dP`, `= 2` in `T_En`).

**The one input that remains, outside the folding argument.**

* *The ambient expansion* (`hamb`): Vinberg's same-sign expansion of every root of `L` in its wall
  family. This needs chambers and a Tits cone for a reflection group, which Mathlib does not have.

Alongside it the chain carries **one** root hypothesis, in either guise: `hsub` (the ambient image of
every root of `M^σ` is a root of `L`) or `hsq` (`(−2)`, or `(−4)` with even ambient pairings). They are
equivalent given the p. 10 properties of `L`, and each is what Namikawa's classification of
`O(T_En)`-orbits supplies for the black vertices. The p. 10 rule itself is no longer cited as a
classification: it is proved (`TwoElementaryRootSquare.lean`). So what is cited rather than reproved
is Vinberg's chamber theory and Namikawa's orbit classification, and nothing else.

**That root hypothesis is false in `T_dP`** — AEGS's own `div(α^I) ≠ 2`, **printed p. 12**.
`FoldingTdpE8FoldNotRoot.lean` machine-checks it in the block model. The fold of the `i`-th `E₈`
simple root is `αᵢ + Iαᵢ`, and pairing it with the first-block vector `αⱼ` leaves the `E₈` Gram entry
(`tdpFoldedE8Root_pairing_single`); the `(0,2)` entry is `1` (`tdpFoldedE8Root_pairing_zero_two`, by
`decide` on the published matrix). Hence the fold has an odd ambient pairing
(`tdpFoldedE8Root_not_two_dvd`), so `div ≠ 2`, and since its square is `(−4)`
(`tdpFoldedE8Root_square`) it is **not a reflective root of `T_dP`**
(`tdpFoldedE8Root_not_isReflectiveRoot`) and not a root of `T_dP` at all
(`tdpFoldedE8Root_not_mem_negativeReflectiveRoots`).

Since the folded walls *are* roots of `M^σ` (Lemma 3.4 forward,
`foldedWallFamily_mem_negativeReflectiveRoots`), while their ambient image is the fold itself
(`invariantCarrierToAmbient_foldedWallFamily`), `hsub` fails at these roots — and with it `hsq`. So
the chamber theorem, though true as an implication, is **not** an instance of Lemma 3.8 for `T_dP`;
its hypothesis is met only in the direction where the folds are roots, which is the `T_En` half of the
source's dichotomy. This is not a defect of the formalization and not a defect of the source: it is
why the source separates `div(α^I) ≠ 2` from `= 2` in the first place, and it means an application of
item 4 needs the `T_En` block data, not the `T_dP` one.

Everything the paper argues *by folding* is therefore formalized; what is not is the arithmetic of
`T_En` and Vinberg's chamber theory, both cited rather than reproved.

## Carry: the carrier bridge

An earlier state of this report recorded that `M^σ`'s carrier is `(formedSublattice L.obj P).obj.carrier`,
definitionally but not syntactically the subtype `↥P`, and that no coercion between them exists — so
predicates about roots of `M^σ` could not be stated in `L` at all. That is now resolved:
`invariantFixedLattice_carrier_eq` proves the carrier equality by `rfl` (`FoldingCarrierBridge.lean:51`)
and `invariantCarrierToAmbient` (`FoldingCarrierBridge.lean:65`) supplies the map, with its additive,
`ℤ`-linear and
`foldedWallFamily`-compatible laws, all by `rfl`. The failure mode was an ascription
(`(ρ : L.obj.obj.carrier)`) triggering a *coercion search* where `show ↥P from ρ` triggers a
*definitional check*; the latter elaborates.

## Other open items, outside the acceptance

* `invariantToAmbient_range` `FoldingFixedPartBridge.lean:141` identifies the range of `r ⊗ v ↦ r • v`
  with the fixed locus, and `invariantToAmbient_qf_tmul` (`FoldingFixedPartIsometry.lean`) shows it is
  form-preserving on pure tensors. **Injectivity is not proved**: relating the map to
  `LinearMap.lTensor` fails on an instance path (`Submodule.module` on `↥M^σ` versus
  `AddCommGroup.toIntModule`), recorded with the literal error in that file's docstring. Without it
  there is no linear equivalence `realForm M^σ ≃ M^σ ⊗ ℝ`.
* Consequently the signature of `invariantFixedLattice 1` — needed to drop the `hpos` premise from the
  chamber-equality statement rather than from the predicate — is also unproved. Building it as
  `M^1 ≅ M` hits the same instance path: `Module.Projective.of_equiv (Submodule.topEquiv)` fails with
  `synthesized AddCommGroup.toIntModule ↥⊤ / inferred ⊤.module`. Both residuals have one cause: the
  lattice carrier carries its group and module structure as **data** of the bundled category
  (`isAddCommGroup`, `isModule`), while a submodule carries them as **type-class instances**
  (`AddCommGroup.toIntModule`), and no defeq check identifies those. The fix is to state such
  facts on a carrier built the way the lattice's own is, which is what
  `ofBilinMap_projective` (`FoldingOfBilinMapProjective.lean:43`) records as available.

## LC-09

Each module carries its own record: repository search, Mathlib at the pinned head, and the live
Formalization Corpus (queries and hits listed per file). Nothing in Mathlib, the repository or the
corpus supplies a folding of a Coxeter diagram or of a chamber along an involution; the one statement
that is Mathlib's — symmetry of `Matrix.toBilin'` for a symmetric matrix — is delegated to
`Matrix.isSymm_toBilin'_iff_isSymm` (`toBilin'_symm`, `FoldingEnriques.lean`), and the remaining
`toBilin'_*` block-matrix glue is `private`.
