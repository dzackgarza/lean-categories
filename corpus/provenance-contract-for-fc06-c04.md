---
type: reference
title: Provenance contract for FC06 C04
description: '# Provenance contract for FC06 C04'
tags:
- project
- reference
timestamp: '2026-09-06T00:00:00Z'
scope: project
source: agent
confidence: high
promotable: false
project_id: github.com__dzackgarza__lean-categories
---
# Provenance contract for FC06 C04

# Provenance contract for FC06 C04

## Provenance contract for FC06 C04

- Canonical source block: FC06 Hartshorne, Chapter IV, `FC06-C04-U001`–`FC06-C04-U148`, in canonical source-ID order. The live master mapping was checked first: C01–C03 were already complete, C04 was active, and concurrently owned C02 work was not touched.
- Project-first inspection is recorded against repository `A=3b2239e161592472b34e02ad3b7da308f9ce7280`. Pinned Mathlib is `P=db584cd6d46c92f209a44c0f1c829460d327499d`, Lean 4.33.0, Apache-2.0. Current Mathlib was refreshed at `H=5aedf732b6987e8c26ab3c9ebc855314f82b045f`; the two pinned positive routes were also checked at H and remain present there.
- The C03 generator/audit pattern was reused: canonical rows are parsed and contiguity-checked, every positive Mathlib path/declaration is verified at P, and exactly one route is emitted per source ID.
- Strict bundle semantics govern every row. A route must own the complete source statement. Partial clauses, a theorem only for a special model without the required comparison bridge, a nearby algebraic primitive, a statement using `sorry`, or an open/conditional work item does not count as a route.
- Project source searches covered the Hartshorne/curve/elliptic/Riemann–Roch/Hurwitz/Jacobian/canonical-curve vocabulary. The only nearby project implementation is `LeanCategories/Lattices/Valued/ComplexTorus.lean`; it does not prove the Hartshorne analytic/algebraic comparison rows and is therefore not promoted.
- Pinned Mathlib was searched for algebraic curves, divisors/Picard, Riemann–Roch, finite morphisms/ramification/differentials, Frobenius, ample/very ample divisors, Weierstrass elliptic curves, group schemes, modular forms, CM/Hasse/supersingularity, rational points, hyperelliptic/canonical curves, gonality, Severi and Castelnuovo theory. Generic Kähler/different/ramification and Weierstrass-model infrastructure is retained only as near-miss evidence where it does not own the complete row.
- U086 has a direct pinned owner: `CategoryTheory.GrpObj` is the internal-group structure in a Cartesian monoidal category, and `Over S` has its Cartesian structure from pullbacks. This is exactly the group-scheme datum over S. Mathlib’s algebraic-geometry group files use `GrpObj (Over.mk f)`/`GrpObj ((Spec A).asOver (Spec R))`, confirming the intended scheme specialization.
- U094 has a direct pinned owner in `Mathlib/Analysis/SpecialFunctions/Elliptic/Weierstrass.lean`: the standard ℘ lattice sum and derivative, lattice periodicity, meromorphicity, and order-two poles are all proved. The same file proves the differential equation, but the field-generation half of U095 is absent, so U095 remains unmatched.
- Pinned `RatFunc.Luroth.algEquiv` proves the field-theoretic part of U037 but not Hartshorne’s geometric consequence; pinned `fermatLastTheoremThree` supports the Diophantine obstruction behind U125 but not the exact projective rational-point set/group law. Both are rejected as proper subsets of bundled rows.
- Current/open Mathlib searches found no landed algebraic-curve Riemann–Roch or Jacobian bridge. Relevant open work includes conditional Riemann–Roch (#41621), divisor/class-group groundwork (#41729/#41732), Jacobian blueprint statements (#40616), division-polynomial scalar-multiplication work (#41197), and universal Weierstrass-model work (#41300); none realizes a complete additional C04 row under this contract.
- External checks included `mrdouglasny/jacobian-challenge` at `JAC=8ce1ec28aed1c78b3b39d0bae26e2858c82f5143` (analytic complex-curve/Jacobian development; torus uniformization is assumed axiomatically) and `MichaelStollBayreuth/EllipticCurves` at `EC=449c7b936813254c8718db5c204aa71e9c3c44f6` (Apache-2.0; proved Mordell–Weil for Weierstrass models over number fields). The latter supplies a strong implementation of Mordell–Weil in a model representation, but no checked abstract-curve-to-Weierstrass bridge closes Hartshorne U124; its explicit rank-one `E(Q)≅Z` example is a different curve from U126.
- No checked P/H/open/external route was found for the algebraic-curve Riemann–Roch/Hurwitz programme, ample/canonical embeddings, relative Picard/Jacobian theory, complex elliptic uniformization/classification, CM and supersingularity theory, or the canonical-curve/moduli/space-curve bounds in U127–U148.
- `N=2026-09-06` marks a dated unmatched decision after project-first, pinned/current Mathlib, recorded open/current work, indexed search services, and relevant external Lean checks.

