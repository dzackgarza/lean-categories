---
type: reference
title: Foundational corpus mapping FC10 Serre Local Fields
description: "# FC10 \u2014 Serre, *Local Fields* mapping"
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
# Foundational corpus mapping FC10 Serre Local Fields

# FC10 — Serre, *Local Fields* mapping

Status: **Sweep II complete.** C01–C15 complete.

Canonical catalogue: [[foundational-corpus-units-fc10-serre-local-fields|FC10 — Serre, Local Fields]].

Pinned project baseline: Mathlib `db584cd6d46c92f209a44c0f1c829460d327499d`, Lean 4.33.0. Current Mathlib was checked at `71a80585ee495fc24472fd0eaffc89d94e4fd8d6`. Declarations first appearing after the project pin are revision-specific `reference-port` routes unless independently importable.

Every canonical unit receives exactly one Sweep-II route: `mathlib`, `project-existing`, `package-import`, `reference-port`, or `unmatched`. Project source is searched first, followed by pinned/current Mathlib, open/current work, and targeted external Lean discovery. Strict bundle semantics apply throughout.

## Structured definitional residue pass 2 — 2026-09-17

The seven provisional FC10 definitional residues were re-run against project history, pinned/current Mathlib, the live Formalization Corpus, the repository's importable packages, and targeted current Lean searches. The pass covered truncated Witt ring schemes; ℓ-adic curve homology/Jacobian representations; nonabelian group `H¹`, its functoriality and the two low-degree connecting maps; and the tensor/group/base-change structure on the classical Brauer quotient.

One first-pass false negative is now an exact importable route. The pinned `Whysoserioushah/BrauerGroup@54a54e35abf4c69fdef952100df57a8ec2bc1ea9` package defines Brauer multiplication from tensor products of central simple algebras, proves the quotient is a commutative group, defines scalar extension as `BrauerGroupHom.BaseChange`, and packages field-extension functoriality as `BrauerGroupHom.Br`; its relevant files are proof-complete. Hence `FC10-C10-U027` is remapped to `package-import`.

The other six rows remain provisional unmatched residue. No checked source was found assembling truncated Witt vectors into Serre's affine finite-type ring scheme, or supplying general ℓ-adic homology of smooth projective curves together with `H₁=T_ℓ(J)`. Mathlib's `CategoryTheory/Sites/NonabelianCohomology/H1.lean` constructs Čech-style `H¹` for a presheaf of groups rather than Serre's group-action cohomology, while `RepresentationTheory/Homological/GroupCohomology/LowDegree.lean` explicitly leaves nonabelian group cohomology TODO and its multiplicative interface assumes commutative coefficients. Current external hits either remain in the abelian setting or are roadmap declarations with `sorry`, so they do not supply `FC10-C07-U039/U040/U044/U045`. No definition authoring occurred.

## Open-ended prior-art recovery — 2026-09-17

The unconstrained search then found open Mathlib PR #31613 at `xyzw12345/mathlib4@9dc1e337689fa7ba4fefa52b4874660bdd3a3619`, whose new `GroupCohomology/NonAbelian.lean` explicitly follows Serre's *Local Fields*. Its active head code has no `sorry`/`admit` and the head `main` check succeeds. It defines the arbitrary-noncommutative crossed-cocycle setoid and quotient, proves quotient functoriality, and constructs the degree-zero connecting map together with the factor-through proof giving lift independence. Hence `FC10-C07-U039`, `U040`, and `U044` are recovered as `reference-port` routes.

The same PR does not close `FC10-C07-U045`: the proposed `connectHom₁`/`δ₁ : H1 G C → H2 A` development is wholly commented out at the inspected head, and the generated declaration summary contains no `δ₁`. It is therefore design-level partial evidence only. Together with the still-unmatched truncated-Witt ring scheme and general ℓ-adic curve/Jacobian representation, FC10 now has three surviving definitional residue rows. No definition authoring occurred.

[Provenance contract for FC10 C01](provenance-contract-for-fc10-c01)

[Chapter 1. Discrete Valuation Rings and Dedekind Domains FC10](chapter-1-discrete-valuation-rings-and-dedekind-domains-fc10)

[Provenance contract for FC10 C02](provenance-contract-for-fc10-c02)

[Chapter 2. Completion FC10](chapter-2-completion-fc10)

[Provenance contract for FC10 C03](provenance-contract-for-fc10-c03)

[Chapter 3. Discriminant and Different FC10](chapter-3-discriminant-and-different-fc10)

[Provenance contract for FC10 C04](provenance-contract-for-fc10-c04)

[Chapter 4. Ramification Groups FC10](chapter-4-ramification-groups-fc10)

[Provenance contract for FC10 C05](provenance-contract-for-fc10-c05)

[Chapter 5. The Norm FC10](chapter-5-the-norm-fc10)

[Provenance contract for FC10 C06](provenance-contract-for-fc10-c06)

[Chapter 6. Artin Representation FC10](chapter-6-artin-representation-fc10)

[Provenance contract for FC10 C07](provenance-contract-for-fc10-c07)

[Chapter 7. Basic Facts FC10](chapter-7-basic-facts-fc10)

[Provenance contract for FC10 C08](provenance-contract-for-fc10-c08)

[Chapter 8. Cohomology of Finite Groups FC10](chapter-8-cohomology-of-finite-groups-fc10)

[Provenance contract for FC10 C09](provenance-contract-for-fc10-c09)

[Chapter 9. Theorems of Tate and Nakayama FC10](chapter-9-theorems-of-tate-and-nakayama-fc10)

[Provenance contract for FC10 C10](provenance-contract-for-fc10-c10)

[Chapter 10. Galois Cohomology FC10](chapter-10-galois-cohomology-fc10)

[Provenance contract for FC10 C11](provenance-contract-for-fc10-c11)

[Chapter 11. Class Formations FC10](chapter-11-class-formations-fc10)

[Provenance contract for FC10 C12](provenance-contract-for-fc10-c12)

[Chapter 12. Brauer Group of a Local Field FC10](chapter-12-brauer-group-of-a-local-field-fc10)

[Provenance contract for FC10 C13](provenance-contract-for-fc10-c13)

[Chapter 13. Local Class Field Theory FC10](chapter-13-local-class-field-theory-fc10)

[Provenance contract for FC10 C14](provenance-contract-for-fc10-c14)

[Chapter 14. Local Symbols and Existence Theorem FC10](chapter-14-local-symbols-and-existence-theorem-fc10)

[Provenance contract for FC10 C15](provenance-contract-for-fc10-c15)

[Chapter 15. Ramification FC10](chapter-15-ramification-fc10)
