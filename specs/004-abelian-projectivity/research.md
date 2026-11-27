# Research: decisions of the abelian projectivity feature

Each decision settles an open point of PLAN-ABELIAN-PROJECTIVITY and its feature card
FEATURE-normalized-category-catalogue, and names its source.

## D1. Scope and starting objects

**Decision**: The feature proves the projective-embedding theorem for the repository's complex
tori with a Riemann form, from `ComplexTorus` and `IsAbelianVariety` (`Lattices/Valued/ComplexTorus.lean`)
and `IsProjectiveVariety` (`Schemes/Varieties.lean`). Stacks, KSBA moduli, quotient stacks, period maps
and stable families are not inputs of any task.

**Source**: PLAN-ABELIAN-PROJECTIVITY (starting boundary; "only capabilities actually consumed by
that chain are prerequisites"); FEATURE-normalized-category-catalogue ("Do not block this consumer
on completion of the stacks/KSBA or period-map programmes").

## D2. Position in the work order

**Decision**: The owning tasks execute in the repository-wide definition-first Spec Kit order. Feature 002 T111
checks aggregate acceptance, after T110 (002 D11), without delaying its definition tasks.
The actual inputs are 003 T036 and T037 (Hodge categories and complex tori), 002 T125
(complex analytic spaces), and the required corpus units of FR-008 at their 002 owners
(the corresponding Sweep-IV results of T101 and T102 where needed).

**Source**: 002 research D11, D22; constitution M11; the plan ("If Sweep IV has already delivered an
exact theorem or construction needed here, consume it at that owner").

## D3. The corpus sources of the chain

**Decision**: The plan's "Peters–Steenbrink theta material" is the theta material of FC11,
Peters–Sterk, *Symmetric and Quadratic Forms* (source manifest), Chapter 16: units FC11-C16-U026
(the Jacobian as an abelian variety), U027 (quasi-periodic functions on tori), U028 (properties of
Riemann's theta function), U030–U032 (canonical class, theta characteristics). The Beauville clause is
FC12-C05-U009 (complex tori; a projective complex torus is an abelian variety), U010 and U011.

**Source**: `corpus/foundational-source-corpus.md` (FC11 row); the FC11 and FC12 catalogues.

**Supersedes**: the plan's attribution of the theta material to Peters–Steenbrink.

## D4. The proof sources

**Decision**: Appell–Humbert, the canonical theta functions, $h^0 = \operatorname{Pf}(E)$ and the
Lefschetz theorem are read from Birkenhake–Lange, *Complex Abelian Varieties*, Chapters 1–4, with
Mumford, *Abelian Varieties*, Chapter I, as the second source; Chow's theorem from Griffiths–Harris,
*Principles of Algebraic Geometry*, Chapter 1. Task T001 records the item keys and the page locators
of each statement before any statement is written (002 research D16). A source that the library
does not hold is added to it first, by the same rule.

**Source**: constitution M2, M8; docs/agents/citation-sources.md; the plan ("Appell–Humbert
classification ... theta sections ... very-ampleness ... Chow/GAGA comparison").

## D5. Owner of holomorphic line bundles

**Decision**: A holomorphic line bundle is a rank-one vector bundle over a complex manifold whose
trivializations change by holomorphic maps, in Mathlib's vector-bundle framework over the complex
model with analytic smoothness, after the search of constitution M8 confirms that framework; its
sections form a $\mathbb C$-vector space; $\operatorname{Pic}(X)$ is $\pi_0$ of the core of the
category of line bundles with tensor product. The description of a line bundle on $V/\Gamma$ by a
factor of automorphy is a comparison theorem, not the definition.

**Source**: the plan ("principled categorical definitions"); FOUNDATIONS Def. 2.3 (classes as $\pi_0$
of the core) and Conv. 64.11; docs/agents/mathematical-simplicity.md, "Hold the mathematical object
fixed".

## D6. Chow rather than GAGA

**Decision**: The algebraic conclusion uses Chow's theorem for closed analytic subsets of
$\mathbb P^N(\mathbb C)$: the image of the embedding is a closed complex submanifold, hence a closed
analytic subset, hence the zero set of homogeneous polynomials. GAGA (an equivalence of coherent
sheaf categories) is not needed for the stated conclusion. The analytic subsets come from the complex
analytic spaces of 002 T125.

**Source**: the plan ("Any algebraic-variety conclusion names and proves the required Chow or GAGA
comparison"); COMPLAINTS.md, "Missing definitions: complex analytic spaces".
