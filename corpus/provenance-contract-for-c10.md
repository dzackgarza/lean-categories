---
type: reference
title: Provenance contract for C10
description: '# Provenance contract for C10'
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
# Provenance contract for C10

# Provenance contract for C10

- Project search: `LeanCategories/**` outside `.lake/.agents/.git` was searched first at repo HEAD `351cba0287077eadfcd7c71a78ec4a509ce8c966`. `LeanCategories/ForMathlib/AdicCompletionTopology.lean` is the sole general whole-row project owner in this chapter: it supplies the topology and topological-ring structure on ring adic completion used for `FC04-C10-U018`. The file was compiled at this HEAD. Project code has no topology on general module adic completions, no associated-graded construction, and no general Rees grading structure.
- Pinned Mathlib: project pin `db584cd6d46c92f209a44c0f1c829460d327499d` (Apache-2.0, Lean v4.33.0), denoted `P`, contains the topological-group completion APIs, adic completion/functoriality/exactness/tensor/flatness/local/Krull infrastructure, filtrations/Artin-Rees/Rees algebra, and general graded-ring/module infrastructure cited in the chapter. Source-shaped assemblies for U035, U037, U041, U046, and U047 were compile-checked against P; the first-half declaration-name probe and the project U018 bridge also compiled in the P environment.
- Current Mathlib: upstream `5aedf732b6987e8c26ab3c9ebc855314f82b045f` (Apache-2.0), denoted `H`, was rechecked on 2026-09-06 and retains the pinned positive owners. H still has no topology on `AdicCompletion I M`, no stable-filtration topology theorem, no graded-Noetherian biconditional of U029, no exported grading on the Rees ring/module objects of U030, and no pinned associated-graded/noetherian-completion owners for U053/U054/U059.
- Open Mathlib work was rechecked immediately before assembly. PR #33218 remains open at head `3c12745297b7236616f6a23d7c11a8addd85e839` (Apache-2.0) and supplies the associated graded ring in `Mathlib/RingTheory/FilteredAlgebra/AssociatedGraded.lean`; U053 is therefore `reference-port`, not `mathlib`. PR #33220 remains open at head `70572cd62395e933e8f6476bcedcee366a5b5e82` and supplies the associated graded module; U054 is `reference-port`. PR #38331 remains open at head `700711ddc105006709aa5e9bb98684001a93859a` and supplies Noetherianity of general adic completion; U059 is `reference-port`. Negative evidence for U056 also rechecked PR heads #33225=`77d1835b8c0fcd797e8ba34f3513d3bcd4e6ce20` and #33227=`41854bad257ddac64fd172e8d3d571b633ee0c0e`: their filtered/associated-graded map results still do not imply injectivity/surjectivity after completion.
- External exact route U012: `LiranShaul/lean-faithfully-flat-descent@f5967aab9067290aed1b7113569c1b9024a9fca4` (Apache-2.0), `lib/mlSystem.lean::InverseSystem.surjective_limit_of_mittagLeffler_exact` plus `surjective_is_mittag_leffler`. The repository currently pins Lean `v4.26.0-rc2` and Mathlib `d5c9558e75342a10d6321e6a8c798a14f68ae23c`; the source file compiled unchanged against this project's newer P, so U012 is a revision-specific `reference-port` with verified compatibility.
- External/current inverse-limit search also rechecked `ImperialCollegeLondon/FLT@8ec873aab84b21c4faaef849d5afd56ef79f684d`, `DE0CH/flt-lean@a5ec7082457bab42553702cdb183b3e034021ab3`, and `acmepjz/lean-iwasawa@7fffeb8c80fbe13f989f318c23cbb0dcf2230092`. They contain inverse-limit infrastructure but no stronger whole-row owner replacing the U012 route or filling U013–U015.
- The bundled p-adic example U021 was searched through P/H and indexed external Lean code. Current heads of the most relevant surfaced repositories were rechecked: `rwst/lean-code@ce1619b6418dc263efb911b11ad09409c2083d80`, `YijunYuan/FormalizedSparse@be9fb43dded873bc7567b486e17e924823e10e41`, and `CBirkbeck/AINTLIB@160e446617a2168c34c95bbe7a76c4105b392434`. None supplied the complete source bundle identifying `ℤ_p` with the adic completion together with a canonical base-`p` digit expansion and convergence statement.
- Graded/Rees negatives U023/U029/U030 were searched in P/H, open Mathlib work, and indexed external Lean code. `tom111/BEI-lean@5b3ddff1ffac4a12d16da43df6fc443501f4d680` surfaced for graded Noetherian developments but assumes both Noetherianity and finite type rather than proving U029. No external `reesAlgebra` grading owner or stable-filtration topology theorem was found.
- `N` denotes dated 2026-09-06 strict negative evidence after project-first search, P/H, open/current Mathlib, installed packages, and targeted external Lean search. A partial theorem, informal docstring identification, editorially related fact, or one clause of a bundled proposition does not satisfy a canonical unit under strict bundle semantics. This is why U023, U029, U030, U044, and U055 remain unmatched despite substantial nearby formalization.
