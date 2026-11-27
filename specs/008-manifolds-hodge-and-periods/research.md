# Research: decisions of manifolds, Hodge theory and period constructions

Each decision settles a choice that #40 lists as unresolved, or a point of #9 and #109, and names
its source.

## D1. The requirement is definitional; position in the work order

**Decision**: Every object has its objects, morphisms and at least one proved theorem. Torelli
theorems, surjectivity and extension of period maps, the finite generation of the ring of
modular forms, Cartan's theorem that $\Gamma\backslash\Omega_T$ is a normal complex space and the
semitoroidal comparison of arXiv:2312.03638 Thm. 1.1 are not requirements, are not stated, and
no axiom stands for them. The feature is a consumer intake of the research programme (stages 1
and 3) under constitution M9 and runs in the repository-wide definition-first Spec Kit order; a declaration that a task needs and that a task of another feature owns (a pending corpus unit of 002, an owner row of 003) is done first, at once, by that owning task, which keeps its place and ID.

**Source**: #1, north star (decision record 2, R1); #40, rules; constitution M9, M11; 002 research
D9. **Supersedes**: the comment of 2026-09-04 on #40 that made a corpus-version amendment a
prerequisite.

## D2. Manifolds and the truncation of the period domain

**Decision**: Complex manifolds are Mathlib `IsManifold 𝓘(ℂ, E) ⊤ M` in the categories of 002
T124. $\Omega_T$ is the set-level domain of 003 T037 with its complex-manifold structure as an
open subset of the smooth quadric; the space of oriented positive-definite real 2-planes in
$T_{\mathbb R}$ is a comparison theorem.

**Source**: [FOUNDATIONS.md](../../FOUNDATIONS.md) Def. 61.3; #40, Mathlib reuse comment; #1,
coordinator default 5 of the touchstone audit (set-level core, analytic layer here).

## D3. The quotient object

**Decision**: The quotient of $\Omega_T$ by an arithmetic $\Gamma \subseteq O^+(T)$ is the quotient
stack $[\Omega_T/\Gamma]$ on the site of complex analytic spaces of 002 T125. The coarse quotient
is the locally ringed space of $\Gamma$-invariant holomorphic functions on the orbit space.

**Source**: [FOUNDATIONS.md](../../FOUNDATIONS.md) Def. 34.4, 61.4; #1, foundations-compliance
record (the quotient stack is primary); #40, unresolved choices.

## D4. Hodge data and polarization

**Decision**: A polarized variation of Hodge structure of weight $n$ on a complex manifold $B$ is a
local system $\mathbb V_{\mathbb Z}$ of finitely generated free abelian groups, a holomorphic
decreasing filtration $\mathcal F^\bullet$ of $\mathbb V \otimes \mathcal O_B$ satisfying Griffiths
transversality $\nabla \mathcal F^p \subseteq \mathcal F^{p-1} \otimes \Omega^1_B$, fibrewise a pure
Hodge structure, and a flat polarization. Type-IV period domains use positive isotropic lines for
the intersection form (003 D22). Task T001 records the source locator in Carlson–Müller-Stach–Peters,
*Period Mappings and Period Domains*.

**Source**: [FOUNDATIONS.md](../../FOUNDATIONS.md) Def. 61.1, 61.2; 003 research D22; #40, Hodge
branch; constitution M2.

## D5. The period construction and markings

**Decision**: The period construction is a morphism of analytic stacks from the moduli stack of
the family to $[\Omega_T/\Gamma]$, induced by the Hodge filtration; $\Gamma$ is the image of the
monodromy representation in $O^+(T)$. For a marked family (a trivialization of the local system by
$T$) the target is $\Omega_T$. The worked example is the morphism from a base into a quotient
period stack of arXiv:1607.05984, read by task T001.

**Source**: [FOUNDATIONS.md](../../FOUNDATIONS.md) Def. 61.5; #40, unresolved choices (marked or
unmarked, quotient level, categorical level) and its cited example.

## D6. The Coble target

**Decision**: $T_{\mathrm{Co}}$ and $\Gamma_{\mathrm{Co}}$ are read from the source of the Coble
moduli that task T001 records; Dolgachev–Kondō, arXiv:1201.6093, is the first source to open. Its
Prop. 3.2 is not proved by its cited argument and is not used.

**Source**: #40, issue question (stage 1); #1, ambiguity ledger (the Dolgachev–Kondō precedent);
constitution M2.

## D7. The Baily–Borel compactification

**Decision**: The rational boundary components of a Type-IV quotient are the $\Gamma$-orbits of
primitive isotropic lines ($0$-dimensional cusps) and planes ($1$-dimensional cusps), ordered by
inclusion. The Baily–Borel compactification is the Proj of the graded ring of $\Gamma$-modular forms
on $\Omega_T$; its projectivity is the theorem of Baily–Borel and is not a requirement.

**Source**: [FOUNDATIONS.md](../../FOUNDATIONS.md) Def. 62.1 ([@LZ16, §3.1]); #40, scavenged targets.

## D8. Semifans and semitoroidal compactifications

**Decision**: The axiom list of a semifan and the semitoroidal compactification are those of
Looijenga, *Compactifications defined by arrangements II* (arXiv:math/0201218v2), which feature 002
T117 (#162) already formalizes for the semifan arrangement; this feature consumes T117's owner and
states the compactification.

**Source**: [FOUNDATIONS.md](../../FOUNDATIONS.md) Def. 58.5, Rem. 62.7, Rem. 65.6; #9, settled
semitoroidal rulings; 002 T117.

## D9. Lattices from surfaces and their examples

**Decision**: $H^2(X, \mathbb Z)/\mathrm{torsion}$ carries the cup product; $\operatorname{NS}(X)$ is
the image of $\operatorname{Pic}(X)$ under the first Chern class, with the intersection form of
002 T049; the transcendental lattice is $\operatorname{NS}(X)^\perp$. The examples are
$\mathbb P^1 \times \mathbb P^1$ ($U$, with the factor swap acting by exchanging the two isotropic
generators) and the blowup of $\mathbb P^2$ at $k$ points ($I_{1,k}$, odd). The Mordell–Weil
lattice uses Shioda's height pairing (Shioda, *On the Mordell–Weil lattices*, 1990), with the
rational elliptic surface whose fibres are irreducible: $\operatorname{NS}(X) = I_{1,9}$, the trivial
lattice spanned by the zero section $O$ and a fibre $F$ has Gram matrix
$\begin{pmatrix} -1 & 1 \\ 1 & 0 \end{pmatrix}$, its orthogonal complement is $E_8$ (negative
definite, Conv. 64.9), and the Mordell–Weil lattice is $E_8(-1)$.

**Source**: #109, targets and the geometry-to-lattice contract; FOUNDATIONS Conv. 64.9; constitution
M2 (task T001 reads Shioda).
