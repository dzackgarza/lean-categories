---
type: reference
title: Provenance contract for FC09 C05
description: '# Provenance contract for FC09 C05'
tags:
- project
- reference
timestamp: '2026-09-07T00:00:00Z'
scope: project
source: agent
confidence: high
promotable: false
project_id: github.com__dzackgarza__lean-categories
---
# Provenance contract for FC09 C05

# Provenance contract for FC09 C05

## Provenance contract for FC09 C05

- Canonical source block: FC09 Neukirch Chapter V, `FC09-C05-U001`–`FC09-C05-U056`, in canonical source-ID order from [[foundational-corpus-units-fc09-neukirch]]. The generator retrieves all 56 rows through `agent-memory`, asserts exact order/uniqueness, and assigns exactly one route to every unit.
- Project-first inspection used `A=3b2239e161592472b34e02ad3b7da308f9ce7280` (Lean 4.33.0, Apache-2.0). The material C05 project layer is the quadratic Hilbert-symbol development in `LeanCategories/Lattices/Valued`: the norm criterion, odd-prime unit/mixed formulas, and the closed dyadic formula.  These close U028 exactly, but strict bundle semantics prevents a quadratic specialization from earning the general n-th Hilbert-symbol rows U020–U027 or the wild explicit-reciprocity rows U029–U032.  No project local-reciprocity or Lubin–Tate layer was found.
- Pinned Mathlib is `P=db584cd6d46c92f209a44c0f1c829460d327499d`, Lean 4.33.0, Apache-2.0.  Its source-complete C05 contribution is the one-dimensional formal-group-law core: `FormalGroup` plus `FormalGroup.IsComm` closes U033.  It has no local norm-residue/reciprocity, Hilbert-symbol, Lubin–Tate, or higher-ramification interface closing the remaining local-CFT bundles.
- Current Mathlib was checked at `H=71a80585ee495fc24472fd0eaffc89d94e4fd8d6`.  Targeted current-tree searches found no `Lubin-Tate`, local-reciprocity/norm-residue, `hilbertSymbol`, or Herbrand local-CFT layer, and `Mathlib/RingTheory/Valuation/RamificationGroup.lean` still explicitly states `TODO: Define higher ramification groups in lower numbering`.  This blocks source-complete routes for U053–U056.
- Open Mathlib PR #38213 was inspected at `O=133714768d42ba1a6107b7a84e2d22222c7c69ed`.  Its new `FormalGroupHom` and `FormalGroupIso` APIs close U034 and, together with pinned substitution-inverse and base-change APIs, give direct short derivations for U036–U037.  Because the PR is open/draft and absent from both P and H, these are `reference-port`, not `mathlib`.  It does not provide the endomorphism-ring/formal-module/Lubin–Tate structures needed for U038–U052.
- Open Mathlib PR #42687 was rechecked at `O=a40561e249ebf45d2870f5d9d45bc2eb4d80b242`.  It defines abstract formation/field-formation/class-formation structures but no reciprocity/norm-residue theorem, while its proposed local class formation still contains `sorry`; it therefore does not close U001–U012 or U043–U052.
- External local-CFT discovery was checked rather than inferred.  `kbuzzard/ClassFieldTheory@ccc3323c6750abca25b49b35106f54eb3a398509` contains intended local Herbrand and unramified-cohomology theorems, but the former depends on an explicit `sorry` for local units and the latter is itself sorried, so neither is credited.  `mariainesdff/LocalClassFieldTheory` currently has no completed reciprocity/Lubin–Tate layer.  A targeted Kronecker–Weber search found `xroblot/SKW@3c8b2c9589b5a790f07ee7faf0b5ccfbe4005d10::kronecker_weber`, whose statement exactly matches U013, but its current proof depends on `TwoPower.lean` with unresolved `sorry`s and the repository exposes no recognized license; U013 therefore remains unmatched.
- Strict bundle semantics was enforced throughout.  Ordinary cyclotomic Galois APIs do not earn the Kronecker–Weber or local-cyclotomic maximal-abelian statements; Hilbert 90 does not earn local reciprocity; basic formal-group laws/homomorphisms do not earn endomorphism rings, formal O-modules, or Lubin–Tate modules; and ideal-theoretic ramification does not earn upper-numbering reciprocity or Hasse–Arf without the missing higher-ramification layer.
- Short derivations are credited only from checked interfaces.  U028 is a notational translation of the project’s closed quadratic p-adic formulas.  U036 uses the pinned two-sided substitution inverse of a zero-constant power series with unit linear coefficient and cancellation in the formal-group homomorphism identity to obtain the inverse homomorphism; the converse compares linear coefficients.  U037 is formal-group base change followed by the PR’s homomorphism object.
- All `mathlib` targets were path/token validated against P, U028 project targets against A, open-PR targets against `O=133714768d42ba1a6107b7a84e2d22222c7c69ed` with `sorry` excluded in the cited file, and negative/current/open/external checks against H/#42687/the inspected external revisions.
- Route totals for C05: `mathlib` 1, `project-existing` 1, `package-import` 0, `reference-port` 3, `unmatched` 51.

