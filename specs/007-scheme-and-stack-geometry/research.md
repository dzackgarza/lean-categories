# Research: decisions of scheme and stack geometry

Each decision settles a choice that #9, #38 or #39 lists as unresolved, and names its source.

## D1. Position in the work order

**Decision**: The feature is a consumer intake of the research programme (stage 3) under
constitution M9. It runs in the repository-wide definition-first Spec Kit order. It works from its cited sources with the
search of constitution M8; corpus membership of a source is not a prerequisite. A declaration that a task needs and that a task of another feature owns (a pending corpus unit of 002, an owner row of 003) is done first, at once, by that owning task, which keeps its place and ID.

**Source**: constitution M9, M11; 002 research D9. **Supersedes**: the comments of 2026-09-04 on
#9, #38 and #39 that made a corpus-version amendment a prerequisite (constitution, Governance).

## D2. The requirement is definitional

**Decision**: Every object of the feature has its objects, morphisms and at least one proved
theorem. The theorems that are requirements are the universal properties of FR-004, the stack
conditions of FR-007, FR-012 and FR-014 and the comparison functors of FR-006. Algebraicity,
properness and separatedness of moduli stacks, the Deligne–Mumford property of
$\overline{\mathcal M}_{g,n}$, existence of log resolutions and the minimal model programme are
not requirements and are not stated. No axiom stands for any of them.

**Source**: #1, north star (decision record 2, R1); #9, superseding note of 2026-07-23;
[FOUNDATIONS.md](../../FOUNDATIONS.md) Def. 35.4, 62.4; constitution M3.

## D3. Varieties, curves, surfaces

**Decision**: A variety over a field $k$ is an integral scheme whose structure morphism to
$\operatorname{Spec} k$ is separated and of finite type (Stacks Project, chapter Varieties, the
definition of a variety; task T001 records its tag). Its dimension is the Krull dimension of its
underlying space. Curves and surfaces are the dimension-1 and dimension-2 values of the family of
proper varieties. The existing `Schemes/Varieties.lean` predicates are compared with this
definition by task T003.

**Source**: #38, unresolved choices 2–3 and its touchstone amendment (one dimension-parameterized
family); Stacks Project.

## D4. Divisor and dualizing formalism

**Decision**: Weil divisors on Noetherian integral separated schemes regular in codimension one;
Cartier divisors and the Picard group by invertible sheaves; $\mathbb Q$-divisors as
$\operatorname{Div} \otimes \mathbb Q$; on a normal variety the canonical divisor class of
$\omega_X$ and reflexive powers $\omega_X^{[m]} = (\omega_X^{\otimes m})^{\vee\vee}$; on a
demi-normal scheme the same through its $S_2$ condition and the conductor. The Hartshorne units
(II.6 divisors and the class group, III.7 dualizing sheaves) are used at their corpus owners.

**Source**: Hartshorne, *Algebraic Geometry*, II.6, III.7 (FC06); Kollár, *Singularities of the
Minimal Model Program*, §5.1 (demi-normal schemes); #38, unresolved choice 4.

## D5. Base site, topology and truncation

**Decision**: The base is $\mathbf{Sch}_{/S}$ with the fppf topology. Stacks are stacks in
groupoids (a 2-category of stacks). Higher geometric stacks are not used.

**Source**: [FOUNDATIONS.md](../../FOUNDATIONS.md) Rem. 30.7, Def. 31.4, 31.6, Def. 33.5, Rem. 65.5;
#39, unresolved choices 1–2; the fppf correction recorded on #1 (foundations-compliance record).

## D6. Artin and Deligne–Mumford stacks

**Decision**: Algebraic stacks in the sense of the Stacks Project (smooth surjective atlas,
diagonal representable by algebraic spaces) are the ambient category; Deligne–Mumford stacks are
the full subcategory with an étale surjective atlas.

**Source**: [FOUNDATIONS.md](../../FOUNDATIONS.md) Def. 33.3, 33.4; #39, unresolved choice 3.

## D7. Pairs, singularities and stable families

**Decision**: A log pair has $K_X + \Delta$ $\mathbb Q$-Cartier. Discrepancies and the classes klt,
plt, lc and dlt are those of Kollár–Mori, *Birational Geometry of Algebraic Varieties*, §2.3
(dlt by Def. 2.37); slc and demi-normal are those of Kollár, *Singularities of the Minimal Model
Program*, §5; a stable family is a flat proper morphism whose fibres are stable pairs and whose
reflexive powers $\omega^{[m]}_{X/T}(m\Delta)$ commute with base change (Kollár's condition), from
Kollár, *Families of Varieties of General Type* (2023). The boundary coefficient set, the dimension
and the volume are parameters of the moduli problem. Task T001 records the item keys and locators.

**Source**: [FOUNDATIONS.md](../../FOUNDATIONS.md) Def. 62.3 (parameters of the moduli category),
62.4; #39, unresolved choices 4–8; #9, settled KSBA rulings; constitution M2.

## D8. The KSBA moduli problem and the Coble instance

**Decision**: The KSBA moduli fibred category over $(\mathbf{Sch}_{/k})_{\mathrm{fppf}}$ sends $T$
to the groupoid of stable families over $T$ with the fixed dimension, coefficient set and volume;
its stack condition is proved from fppf descent of the relatively ample polarization
$\omega^{[m]}_{X/T}(m\Delta)$. The general stable pair is the definitional object; the Coble
instance is a predicate: the singular quotient with its $\tfrac14(1,1)$ point, $2K_S + C \sim 0$,
$C^2 = -4$, with the coefficients and volume read from arXiv:2312.03638 §§5, 7.

**Source**: #39, issue question (stage 3) and step 11; #9, settled rulings; #1, coordinator default
4 of the touchstone audit (general stable pair, Coble family as instance predicate).

## D9. The two deformation problems

**Decision**: For lifting a point through a square-zero extension by $M$, automorphisms,
lifts and obstructions are governed by $\operatorname{Ext}^{-1}$, $\operatorname{Ext}^{0}$ and
$\operatorname{Ext}^{1}$ of $x^*L_X$ against $M$ ([FOUNDATIONS.md](../../FOUNDATIONS.md) Def. 37.4).
For deforming an object $X$, infinitesimal automorphisms, deformations and obstructions are
$\operatorname{Ext}^0$, $\operatorname{Ext}^1$ and $\operatorname{Ext}^2$ of $L_X$ against
$\mathcal O_X$ (Illusie, *Complexe cotangent*, III.1.2). Both are stated through the transitivity
triangle. `H1Cotangent` of Mathlib is a homology module of the ring-level model, not an Ext group.

**Source**: [FOUNDATIONS.md](../../FOUNDATIONS.md) Def. 37.3, 37.4, Rem. 37.5; #39, correction of
2026-10-28.

## D10. The name without a referent

**Decision**: No declaration is named `AnticanonicalQuotient`; the name has no standard referent.

**Source**: #1, referent audit (2026-07-23); #38.
