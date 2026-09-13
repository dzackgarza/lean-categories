---
type: reference
title: Provenance contract for FC09 C06
description: '# Provenance contract for FC09 C06'
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
# Provenance contract for FC09 C06

# Provenance contract for FC09 C06

## Provenance contract for FC09 C06

- Canonical source block: FC09 Neukirch Chapter VI, `FC09-C06-U001`–`FC09-C06-U090`, in canonical source-ID order from [[foundational-corpus-units-fc09-neukirch]]. The generator retrieves all 90 rows through `agent-memory`, asserts exact order/uniqueness, and assigns exactly one route to every unit.
- Project-first inspection used `A=3b2239e161592472b34e02ad3b7da308f9ce7280` (Lean 4.33.0, Apache-2.0). `LeanCategories/Algebra/IdeleGroup.lean` provides the restricted-product idèle group, principal idèles, local compactness/Haar measure, and the quotient `IdeleClassGroup`; only U005 is source-complete because Neukirch U002 additionally bundles the finite-`S` idèle subgroups and their exhaustion of all idèles. No project S-idèle, ray-class, global idèle-norm, Artin-symbol, or global reciprocity layer was found.
- Pinned Mathlib is `P=db584cd6d46c92f209a44c0f1c829460d327499d`, Lean 4.33.0, Apache-2.0. Its adèle stack (`AdeleRing`, finite restricted products, infinite completions) closes U001. The native Jacobi implementation closes U090 and, via its signed-numerator, quadratic-reciprocity, and supplementary-character theorems, closes the full signed Gauss reciprocity package U089. Ordinary class groups, S-integers, local norms, transfer, and Frobenius infrastructure do not close any further global-CFT bundle; notably `SInteger.lean` still lists finite generation/Dirichlet's S-unit theorem as TODO.
- Current Mathlib was checked at `H=71a80585ee495fc24472fd0eaffc89d94e4fd8d6`. There is still no first-class idèle, ray-class, global reciprocity, or Hilbert-class-field module. Targeted open-PR searches found no idèle/ray/Artin-symbol work. Open PR #42687 at `O=a40561e249ebf45d2870f5d9d45bc2eb4d80b242` provides abstract class-formation infrastructure but no global reciprocity theorem or global instance. Open PR #40661 at `O=184a5900ddc04998dd9d5976cb9c242f265dd56b` is explicitly a file of `*_wanted` Hilbert-class-field statements and contains an unfinished `sorry`, so it is not a `reference-port` owner.
- External global-CFT discovery was checked rather than inferred. `kbuzzard/ClassFieldTheory` has no global adèle/idèle/Artin/ray-class layer. `acmepjz/lean-iwasawa@7fffeb8c80fbe13f989f318c23cbb0dcf2230092` (Apache-2.0) contains experimental Hilbert-class-field and Artin-map files, but `artinMap`, surjectivity, Artin equivalence, and related maximal-unramified results explicitly depend on `sorry`s. TauCeti at `R=2c1e8865b4b9bf705ce1e43a8e50d27145f24f6a` (Apache-2.0) has substantial Frobenius/Artin-prime and Chebotarev setup, but not the Chebotarev density theorem itself, so it does not close U035–U036; its Artin-prime layer also lacks the local-reciprocity/idèle compatibility bundled in U074–U076.
- Strict bundle semantics was enforced. The headline `IdeleGroup` object does not earn U002 without its `S`-idèle subgroups/exhaustion; a principal-idèle map does not earn U003 without the S-unit identification; generic coinduction/Tate cohomology does not earn U026–U034 without the actual global idèle/S-unit G-modules; Frobenius definitions do not earn Artin reciprocity; generic transfer does not earn Furtwängler's U082 triviality theorem; and the project's quadratic local Hilbert symbols do not earn the general n-th Hilbert product/power-residue laws U085–U088.
- Short derivations are credited only where all ingredients are checked. U089 applies native Jacobi reciprocity to absolute values, uses `jacobiSym.neg` to account for signed generators, and uses `at_neg_one`, `at_two`, and the explicit quadratic characters for the two supplementary laws. No global class-field theorem is smuggled into that route.
- All `mathlib` targets were path/token validated against P, U005 project targets against A, and the negative current/open/external checks against H/#42687/#40661 and the inspected external revisions.
- Route totals for C06: `mathlib` 3, `project-existing` 1, `package-import` 0, `reference-port` 0, `unmatched` 86.

