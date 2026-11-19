# #116 — folding a Lorentzian chamber along a diagram involution

Status at `b95afe04` on `main`. What the issue asks for, item by item, with the declaration that
carries each; then what is *not* delivered and why, with the machine-checked obstruction.

Source: Alexeev–Engel–Garza–Schaffler, *Compact moduli of Enriques surfaces of degree 2*, Nagoya Math.
J. 259 (2025), arXiv:2312.03638v2, §3.7–3.8 (printed pp. 11–13). The construction direction is the
source's: invariants, not coinvariants.

## Acceptance, item by item

| # | Item | Status | Declaration (file:line) |
|---|---|---|---|
| 1 | The fixed sublattice `M^σ` | **met** | `involutionFixedSubmodule` `Folding.lean:114` (ker of `σ − 1`); as a lattice object `invariantFixedLattice` `FoldingInvariantChamber.lean:120` |
| 2 | The folded root set (Def. 3.3 → Def. 3.7) | **met** | `foldedVector` `Folding.lean:126`; filtered set `foldedRootSet` `Folding.lean:416` (keeps only folds that are roots of `M^σ`) |
| 3 | Its Coxeter diagram | **met** | `foldedDiagramOfRoots` `Folding.lean:480` (indexed by the surviving folds, no negative-square hypothesis); family/set agreement `range_foldedDiagramOfRoots_eq` `FoldingDiagramOrbits.lean:78` |
| 4 | The chamber theorem | **partly met** — see below | ambient trace/wall identity `chamberOf_folded_trace_walls` `FoldingDiagram.lean:198`; predicate `isChamberWithWalls_invariant` `FoldingInvariantChamber.lean:254`; joining theorem `isChamberWithWalls_invariant_of_chamber` `FoldingInvariantChamber.lean:370`; chamber = folded cone `chamberOf_invariant_folded_of_sign_cover` `FoldingInvariantChamberSignCover.lean:87` |
| 5 | One worked declaration from a published folded diagram | **met** | the `E₈` block of `T_dP` folds to `E₈(2)`: `tdpFoldedE8Diagram` `FoldingDiagram.lean:385` with `tdpFoldedE8Diagram_adjacent` `FoldingDiagram.lean:407` (an `E₈` edge has weight `1/4`) |
| 6 | Compiles with no `sorry` | **met** | zero `sorry`/`admit` across the 25 `Folding*.lean` modules; all imported by `LeanCategories/All.lean:442-466` |

Supporting statements that are proved rather than assumed:

* `roots_mem` of the predicate is *derived* from Definition 3.7's filter, not hypothesised:
  `foldedRootSet_subset_negativeReflectiveRoots` (`FoldingInvariantChamber.lean`).
* `hstab` (the involution preserves the chamber cone) is *derived* from a diagram involution:
  `realFormOrthogonalHom_mem_rootInteriorCone` `FoldingChamberStability.lean:62`.
* The source's maximal-dimension hypothesis is *derived*: `exists_mem_fixedPart_interior`
  (`FoldingInvariantChamber.lean`).
* The folded roots are transverse to an interior point of the chamber, with no classification
  hypothesis: `foldedVector_pairing_ne_zero_of_mem_interior` `FoldingInvariantConverse.lean:80`.
* The trace and wall identities are stated on the invariant part `M^σ ⊗ ℝ`
  (`realFormFixedPart`), not on the image of the fixed lattice.

Closed instances (not conditional):

* `U = ⟨e,f⟩` at the identity involution, via `hcomplete`: `u_witnessed` `FoldingWitness.lean:332`,
  with the chamber itself at `hyperbolicPlane_isChamberWithWalls` `FoldingWitness.lean:193`.
* the same, via the sign covering and with no `hpos`: `u_invariant_isChamberWithWalls_signCover`
  `FoldingSignCoverWitness.lean:64`.

## Item 4: what is not delivered

**The general statement is not proved.** For a *non-trivial* involution on a Lorentzian lattice with
more than one chamber wall, `IsChamberWithWalls (M^σ)` is proved only from an additional hypothesis
— either

* `hcomplete`: every negative reflective root of `M^σ` is a nonzero integer multiple of a folded wall
  root, or
* the sign covering: every such root *is* a folded wall root or its negative
  (`hcomplete_of_sign_cover` `FoldingInvariantConverse.lean:109` proves that this implies
  `hcomplete`; it is **stronger**, not weaker).

Neither is a consequence of the chamber hypothesis, and the reason is now a theorem rather than a
claim: in `E₁₀(2)`'s chamber the reflection in `α₃` carries the simple root `α₁` to `α₁ + α₃`
(`C₁₃ = −1`; the reflection in `α₀` fixes `α₁`, since `C₀₁ = 0`), which is a negative reflective root
of the lattice and no nonzero integer multiple of any simple root —
`e10_root_not_multiple_of_wall` `FoldingE10RootNotWall.lean:148`, with the pieces at
`…_reflective` :108, `…_square` :85 and `…_not_multiple` :132.

What the predicate's `interior_regular` field actually needs is the reflection-group statement that
every root of `M^σ` is a `W(M^σ)`-translate of a wall root, together with stability of the interior
cone under `W(M^σ)`. No action of a reflection group on the chambers of `M^σ` exists in this
development, so that route is not available here.

A *non-trivial* instance would need a Lorentzian lattice with more than one chamber wall and a
chamber-preserving involution. The repository has exactly one such chamber, `E₁₀(2)`, and its diagram
admits none: node `4` is the unique branch point (`e10_no_other_branch` `FoldingE10Rigidity.lean:66`,
degrees at `e10_degree` :81) and its three branches have lengths `1, 2, 6`, so the diagram's
automorphism group is trivial. `T_dP = U ⊕ U(2) ⊕ E₈ ⊕ E₈` with `I = −I_En` is the source's own
setting, but its 19- and 22-vertex diagrams (AEGS Figure 5) are printed as pictures and not
tabulated, and the folded diagrams (Figures 7–8) likewise, so the data for an instance are not in the
text.

## Other open items, outside the acceptance

* `invariantToAmbient_range` `FoldingFixedPartBridge.lean:130` identifies the range of the map
  `r ⊗ v ↦ r • v` with the fixed locus, and `invariantToAmbient_qf_tmul`
  (`FoldingFixedPartIsometry.lean`) shows it is form-preserving on pure tensors. **Injectivity is not
  proved**: relating the map to `LinearMap.lTensor` fails on an instance path —
  `Submodule.module` on `↥M^σ` versus `AddCommGroup.toIntModule` — recorded with the literal error in
  `FoldingFixedPartIsometry.lean`'s docstring. Without injectivity there is no linear equivalence
  `realForm M^σ ≃ M^σ ⊗ ℝ`, which is what lifting the cone statements to the invariant lattice's own
  real form needs.
* Consequently the signature of `invariantFixedLattice 1` (needed to drop the `hpos` premise from the
  chamber-equality statement rather than from the predicate) is also unproved; it follows from
  `⊤ ≅ U` once the transport above exists.

## LC-09

Each module carries its own record: repository search, Mathlib at the pinned head, and the live
Formalization Corpus (queries and hits listed per file). Nothing in Mathlib, the repository or the
corpus supplies a folding of a Coxeter diagram or of a chamber along an involution; the one statement
that is Mathlib's — symmetry of `Matrix.toBilin'` for a symmetric matrix — is now delegated to
`Matrix.isSymm_toBilin'_iff_isSymm` (`toBilin'_symm`, `FoldingEnriques.lean`), and the remaining
`toBilin'_*` block-matrix glue is `private`, i.e. not part of the library's surface.
