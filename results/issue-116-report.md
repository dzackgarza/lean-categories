# #116 — folding a Lorentzian chamber along a diagram involution

Status at `36154787` on `main`. What the issue asks for, item by item, with the declaration that
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
| 4 | The chamber theorem | **met modulo two named inputs** — see below | `isChamberWithWalls_invariant_of_wall_data` `FoldingChamberOfWallData.lean` |
| 5 | One worked declaration from a published folded diagram | **met** | the `E₈` block of `T_dP` folds to `E₈(2)`: `tdpFoldedE8Diagram` `FoldingDiagram.lean:385` with `tdpFoldedE8Diagram_adjacent` `:407` |
| 6 | Compiles with no `sorry` | **met** | zero `sorry`/`admit` across the `Folding*.lean` modules; all imported by `LeanCategories/All.lean` |

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

**The statement everything reduces to** (`FoldingChamberOfWallData.lean`):

  `isChamberWithWalls_invariant_of_wall_data (g) (hg) (R) (w) (hw) (hwv) (hR) (hneg) (hcase) (hsq)
  (hamb) : IsChamberWithWalls M (toRealForm _ w) (Set.range (foldedWallFamily g hg R))`

with

* `hw`, `hwv` — an interior vector of the folded cone: Lemma 3.8's maximal-dimension hypothesis
  (**printed p. 12**), realized by `exists_mem_fixedPart_interior` under `hstab`;
* `hR`, `hneg` — every wall root is reflective and of negative square: the diagram of `L`
  (Figure 5, **printed p. 11**);
* `hcase` — every wall root is fixed or orthogonal to its image: the arithmetic of `T_dP`, per wall
  (**printed p. 12**);
* `hsq` — every root of `M^σ` is `(−2)`, or `(−4)` with even ambient pairings: Namikawa's
  classification behind Lemma 3.4's converse (**printed p. 12**);
* `hamb` — every root of `L` is a same-sign combination of the walls: Vinberg's one-sign expansion.

The first three are checkable on the diagrams; the last two are the external inputs. What is **not** a
hypothesis any more: `hcomplete`, the sign covering, the carrier identification, and `hroot`.

**Why the class restriction has that form.** A `(−2)`-vector of an integral lattice is always
reflective (`−2 ∣ 2·anything`), so a `(−2)`-root of `M^σ` is a root of `L`
(`isReflectiveRoot_invariantToAmbient_of_square_neg_two` `FoldingNegativeTwoRoots.lean`). A `(−4)`-vector
is reflective exactly when all its pairings are even: `−4 ∣ 2⟨x,y⟩ ⟺ 2 ∣ ⟨x,y⟩`
(`isReflectiveRoot_iff_two_dvd_pairing` `FoldingNegativeFourRoots.lean`). So the roots that can fail to
be roots of `L` are precisely the `(−4)`-ones with an odd pairing — AEGS Lemma 3.4's type (3)
(**printed p. 12**: `div(α^I) ≠ 2` in `T_dP`, `= 2` in `T_En`).

**The two inputs that remain, both outside the folding argument.**

* *The ambient expansion* (`hamb`): Vinberg's same-sign expansion of every root of `L` in its wall
  family. This needs chambers and a Tits cone for a reflection group, which Mathlib does not have.
* *That the `(−4)`-roots have even ambient pairings* (`hsq`'s second alternative): decided in the
  source by Namikawa's classification of `O(T_En)`-orbits of `(−2)`- and `(−4)`-vectors
  (**printed p. 12**, Lemma 3.4's converse, cited to [Nam85, 2.13 and 2.15]). The classification is
  not in the development.

Everything the paper argues *by folding* is therefore formalized; what is not is the arithmetic of
`T_En` and Vinberg's chamber theory, both cited rather than reproved.

## Carry: the carrier bridge

An earlier state of this report recorded that `M^σ`'s carrier is `(formedSublattice L.obj P).obj.carrier`,
definitionally but not syntactically the subtype `↥P`, and that no coercion between them exists — so
predicates about roots of `M^σ` could not be stated in `L` at all. That is now resolved:
`invariantFixedLattice_carrier_eq` proves the carrier equality by `rfl` and `invariantToAmbient`
(`FoldingCarrierBridge.lean`) supplies the map, with its additive, `ℤ`-linear and
`foldedWallFamily`-compatible laws, all by `rfl`. The failure mode was an ascription
(`(ρ : L.obj.obj.carrier)`) triggering a *coercion search* where `show ↥P from ρ` triggers a
*definitional check*; the latter elaborates.

## Other open items, outside the acceptance

* `invariantToAmbient_range` `FoldingFixedPartBridge.lean:130` identifies the range of `r ⊗ v ↦ r • v`
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
  `FoldingOfBilinMapProjective.ofBilinMap_projective` records as available.

## LC-09

Each module carries its own record: repository search, Mathlib at the pinned head, and the live
Formalization Corpus (queries and hits listed per file). Nothing in Mathlib, the repository or the
corpus supplies a folding of a Coxeter diagram or of a chamber along an involution; the one statement
that is Mathlib's — symmetry of `Matrix.toBilin'` for a symmetric matrix — is delegated to
`Matrix.isSymm_toBilin'_iff_isSymm` (`toBilin'_symm`, `FoldingEnriques.lean`), and the remaining
`toBilin'_*` block-matrix glue is `private`.
