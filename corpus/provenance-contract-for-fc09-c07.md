---
type: reference
title: Provenance contract for FC09 C07
description: '## Provenance contract for FC09 C07'
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
# Provenance contract for FC09 C07


## Provenance contract for FC09 C07

- Canonical source block: FC09 Neukirch Chapter VII, “Zeta Functions and L-series”, `FC09-C07-U001`–`FC09-C07-U175`, in canonical source-ID order from [[foundational-corpus-units-fc09-neukirch]]. The generator retrieves all 175 rows through `agent-memory`, asserts exact order/uniqueness, and assigns exactly one route to every unit. C07 is the final FC09 chapter in the canonical catalogue.
- Project-first inspection used `A=3b2239e161592472b34e02ad3b7da308f9ce7280` (Lean 4.33.0, Apache-2.0). The project has lattice theta/formal-series material but no additional analytic number theory interface that closes a C07 row; therefore C07 has no `project-existing` route.
- Pinned Mathlib is `P=db584cd6d46c92f209a44c0f1c829460d327499d`, Lean 4.33.0, Apache-2.0. Native coverage is concentrated in the classical analytic substrate: Riemann zeta and its completion, complex Gamma, theta/Hurwitz kernels and abstract Mellin functional equations, Bernoulli/zeta special values, Dirichlet characters and L-series/Euler products, Schwartz Fourier theory, Dedekind zeta, Dirichlet nonvanishing/primes in progressions, representation characters, and Dirichlet density. Uniform convergence in U001/U008/U018 is credited only after the checked summable majorants are combined with Mathlib’s uniform M-test.
- Current Mathlib was checked at `H=71a80585ee495fc24472fd0eaffc89d94e4fd8d6`. It adds no source-complete general Artin-L, Chebotarev, or global Hecke analytic layer closing the unmatched C07 blocks. Open PR #40736 was inspected at `O=945b7b641bcfd4b2b787a8abf241fdb65ad70dc1`: it defines a number-field `HeckeCharacter` as an algebraic `MulChar` of the idèle class group and defines local Euler factors/L-functions, but it does not impose Neukirch’s required continuity into `S¹` or prove the Hecke analytic theory, so it earns no row here.
- External analytic discovery found `CBirkbeck/AINTLIB@160e446617a2168c34c95bbe7a76c4105b392434` (Apache-2.0; Mathlib pin `e4b72ca0d01c5f45c485814ec129debbc4f64634`). Its `DedekindResidue` Poisson development is sorry-free in the cited files and proves the full `GL` Fourier change-of-variables formula, the n-dimensional Gaussian transform, dual lattices and lattice Poisson summation. These are conservatively `reference-port` routes for U039–U040 because the package is on a distinct Mathlib revision; for U040 the external Poisson theorem’s summability hypotheses are discharged for Schwartz maps by pinned rapid-decay seminorms and `ZLattice.summable_norm_rpow`.
- External discovery also found `Vilin97/lean-pool@c8ddda0a64f21cb019720cdda48c94354d4091e7` (Apache-2.0; Mathlib pin `de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11`), whose sorry-free Dedekind-zeta files prove the literal ideal series, prime-ideal Euler product and locally uniform product control. Combined with the pinned uniform M-test this closes U053 as a `reference-port`. AINTLIB additionally has a general completed-Dedekind-zeta functional equation, but Neukirch U064–U065 bundle exact residue/normalization assertions not exported as one checked theorem, so strict bundle semantics leaves them unmatched. AINTLIB’s cyclotomic zeta factorization currently treats prime conductor `p`, not Neukirch’s arbitrary `m`, so U066 also remains unmatched.
- Chebotarev-specific discovery checked `CBirkbeck/chebotarev-density@c64095e6cc6483b401849c7fd9182d983d3bf261` (Apache-2.0; Mathlib pin `e568743e9c24da15c8f8347a47931d2a6c33ff85`), but its named `chebotarev_density` theorem still contains `sorry`; TauCeti supplies substantial Frobenius-prime/counting infrastructure but not the density theorem itself. No Chebotarev row is credited.
- Strict bundle semantics was enforced across all 13 sections. A functional equation without the source’s root-number modulus, residue normalization or special-value formula does not earn the row; generic finite-group induction does not earn Brauer/character-basis assertions; the algebraic Hecke-character PR does not earn continuous Größencharacters; and Frobenius or density definitions do not earn prime-density theorems.
- Short derivations are credited only where the checked APIs close the whole source unit: Gamma residues at `-n` follow from the residue at zero plus recurrence; negative-half-plane zeta zero classification follows from the functional equation, Gamma nonvanishing and right-half-plane nonvanishing; and the uniform half-plane convergence rows use explicit summable majorants plus the library M-test.
- All `mathlib` targets were path/token validated against P, every external positive target was checked at its exact repository revision with `sorry`/`*_wanted` excluded in the cited files, and current/open/external negative boundaries were rechecked against H, PR #40736 and the Chebotarev/cyclotomic candidates.
- Route totals for C07: `mathlib` 25, `project-existing` 0, `package-import` 0, `reference-port` 3, `unmatched` 147.
