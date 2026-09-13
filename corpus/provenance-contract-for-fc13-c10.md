---
type: reference
title: Provenance contract for FC13 C10
description: '# Provenance contract for FC13 C10'
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
# Provenance contract for FC13 C10

# Provenance contract for FC13 C10

## Provenance contract for FC13 C10

- Canonical source block: FC13 Matsumura Chapter 10, `FC13-C10-U001`–`FC13-C10-U065`, §§28–30, in canonical source-ID order from [[foundational-corpus-units-fc13-matsumura]]. All 65 IDs are retrieved through `agent-memory`, asserted once/in-order, and assigned exactly one route.
- Project-first inspection used `A=3b2239e161592472b34e02ad3b7da308f9ce7280`. No project-owned adic smoothness, coefficient/Cohen-ring, p-basis, regular-locus, or weak-Jacobian interface closes a C10 unit, so C10 has no `project-existing` route.
- Pinned Mathlib is `P=db584cd6d46c92f209a44c0f1c829460d327499d`, Lean 4.33.0, Apache-2.0. Native C10 coverage is narrow but exact: the full Eisenstein criterion U037, formal-smoothness local-to-global U042, local-to-global solvability of linear systems U043, and the fraction-field module-rank definition U050.
- Current Mathlib was refreshed 2026-09-07 to `H=e281a66114fe17935e6ea7917a01b714d0c1e493`. Targeted P/H/open searches found no source-level I-smooth/I-unramified/I-étale interface, geometrically regular local algebra predicate, coefficient/quasi-coefficient ring package, ramified regular-local predicate, regular locus, weak Jacobian condition, or p-basis/cofinite-field differential package.
- Open PR #39289 (`7c2cce3eff4d42f292ba86215e7e3fa10735e925`, Cohen structure theorem) and #35560 (`1e4c8c2848f36bd73aea213044612c247b1ea91f`, corollaries) were inspected at fixed revisions. They contain substantial Cohen-ring, residue-field lifting, flat-extension, and regular-presentation partials, but do not close Matsumura’s whole coefficient-ring bundles; the flat-extension branch also contains an unresolved `sorry`. They are therefore evidence recorded inside unmatched rows, not `reference-port` routes.
- Strict bundle semantics were enforced. Ordinary formal smoothness into adically complete targets is not Matsumura’s I-smoothness; the pinned smooth locus does not close rows that also require regular-locus openness; and presentation-level Jacobian criteria are not substitutes for the rows bundling m-smoothness, regularity, p-bases, arbitrary derivations, or cofinite coefficient fields.
- Three nontrivial P assemblies were compile-checked in isolated Lean files before promotion: U037 descends prime divisibility from the fraction field after Eisenstein/Gauss; U042 uses the open smooth locus and maximal ideals; U043 applies `Submodule.mem_of_localization_maximal` to the range of the coefficient map.
- Route totals for C10: `mathlib` 4, `project-existing` 0, `package-import` 0, `reference-port` 0, `unmatched` 61.
