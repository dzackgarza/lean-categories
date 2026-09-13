---
type: reference
title: Provenance contract for FC06 C02
description: '# Provenance contract for FC06 C02'
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
# Provenance contract for FC06 C02

# Provenance contract for FC06 C02

## Provenance contract for FC06 C02

- Canonical source block: FC06 Hartshorne, Chapter II, `FC06-C02-U001`–`FC06-C02-U325`, in canonical source-ID order. C01 was already promoted and was not modified or regenerated.
- Project-first evidence is recorded against `A=cd74b69e97f743cd7318a9fe130ed2a749860b3f`. Repository HEAD is `3b2239e161592472b34e02ad3b7da308f9ce7280`; that later commit changes only `TODO.md`, so no project mathematical declaration changed relative to A.
- Pinned Mathlib is `P=db584cd6d46c92f209a44c0f1c829460d327499d`, Lean 4.33.0, Apache-2.0 and directly project-compatible. Every Mathlib route promoted in this table was checked at that exact revision.
- Current Mathlib evidence was refreshed on 2026-09-06 at `H=5aedf732b6987e8c26ab3c9ebc855314f82b045f`, Lean 4.34.0-rc2, Apache-2.0. H/current evidence is used only to close negative gaps; no post-pin declaration is silently treated as project-compatible Mathlib.
- The broad C02 project/P/H/open/external/indexed searches already recorded by the concurrent lean-categories audit were reused rather than rerun. This pass only resolved exact declaration boundaries and strict-bundle ambiguities left by those recordings, including sheaf stalk/exactness APIs, affine/Proj ownership, scheme morphism properties, module sheaves, Kähler differentials, and inverse-limit/adic-completion interfaces.
- Strict bundle semantics govern every row. A route owns the entire stable-ID statement. One clause, one example, a specialization, an unbridged classical/scheme analogue, or a theorem with stronger hypotheses than the source is evidence but not a route.
- The basic sheaf, affine `Spec`, `Proj`, scheme-property, separated/proper, module-sheaf, ring-level Kähler, inverse-limit and adic-completion layers have direct pinned owners. The pinned valuative-criterion API exactly owns U083 and U089 after discharging its quasi-separated/quasi-compact side conditions from Hartshorne’s noetherian/finite-type hypotheses. Classical Chapter-I variety bridges, relative projective morphisms, graded-module sheaves on `Proj`, scheme-level differential sheaves, and the formal-scheme layer remain absent where the complete source row is not otherwise realized.
- Mathlib’s `IdealSheafData` is credited for rows whose mathematics is exactly the closed-subscheme/ideal correspondence (notably U060, U061, U125 and U127). It is not used to claim Hartshorne’s literal `O_X`-subsheaf definition U104; Mathlib’s own ideal-sheaf documentation explicitly distinguishes the implementation-level data from an actual subsheaf.
- TauCeti at `T=f95596f4ee8cc6cd3e6644aaf04e7fe947364697` (Apache-2.0, Lean 4.34.0-rc2; Mathlib `5fcc6656691ed31965746c369f41fa75e567ac9d`) was checked for U153–U157. It implements Weil divisors via `CodimensionOnePoint`, `orderAt`, principal divisors, linear equivalence and a class group, but no checked formal bridge identifies its codimension-one-point divisor group with Hartshorne prime divisors as closed integral codimension-one subschemes. The plan explicitly rejects unbridged equivalent representations, so U155–U157 remain `unmatched`, not `reference-port`.
- Ring-level Kähler rows U253–U260 are credited only where the complete algebraic interface exists at P. The stronger differential-dimension/cotangent statements U261–U263 and all scheme-sheaf differential rows from U265 onward remain unmatched absent exact declarations; the existence of ring-level analogues is not sufficient.
- `Functor.IsMittagLeffler`, its stable-image construction, surjective-system criterion, sheaf limits and generic categorical limits give exact routes for U297, U299, U300, U302, U304 and U305. U301 remains unmatched because no checked theorem supplies Hartshorne’s full ML exactness criterion. U307–U308 use the generic module-level `AdicCompletion`; the large algebraic bundle U309 and the formal-scheme layer U310–U325 are not inferred from it.
- `N=2026-09-06` marks a dated unmatched decision after the recorded project-first, P, H/current, open/current work, indexed search services and relevant external Lean checks. Every unmatched row records exact A/P/H revisions and `none` as its target because no complete route was verified.
- Reconciliation against the concurrent promoted C02 artifact changed only nine route rows: U015, U074, U083, U089, U111 and U142 are pinned `mathlib`; U155–U157 are `unmatched`. The retained live decisions for all other 316 rows were not regenerated. Final route counts are `mathlib` 82, `project-existing` 0, `package-import` 0, `reference-port` 0, `unmatched` 243.
