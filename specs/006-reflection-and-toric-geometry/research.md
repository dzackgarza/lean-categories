# Research: decisions of reflection, fan and toric geometry

Each decision settles a point that #8, #24 or #116 leaves open, and names its source.

## D1. Folding gives the invariant sublattice

**Decision**: The fixed sublattice $M^\sigma$ is the limit of the $BC_2$-action of $\sigma$ on
$M$, the invariant sublattice, not the coinvariant lattice. The folded root set and the chamber
theorem are those of the source that task T001 reads; a difference between that statement and
the question of #116 is recorded under LC-05 and the source's statement is formalized.

**Source**: #116 ("the fixed sublattice $M^\sigma$"); #1, touchstone-compliance record
(folding as the limit of the $BC_2 \to \mathbf{Lat}$ action); [FOUNDATIONS.md](../../FOUNDATIONS.md)
§28 (actions); constitution M2.

## D2. Vinberg's algorithm is a bounded computation

**Decision**: The algorithm is a total function of a Lorentzian reflection datum and a bound into
`Option` of a walled fundamental chamber; a returned chamber carries its proof; termination and
completeness are not claimed.

**Source**: #8, ambiguity resolutions (2026-07-22); #1, decision record 3, §10;
[FOUNDATIONS.md](../../FOUNDATIONS.md) Def. 60.5.

## D3. The referent of the Wythoff coarsening

**Decision**: The Wythoff coarsening is the coarsened fan of Alexeev–Engel–Thompson,
arXiv:1903.09742v3, Def. 4.16, built by Maxwell's Wythoff construction (*Wythoff's Construction
for Coxeter Groups*, Props. 5.1–5.5), as feature 002 task T121 compares it. It is a functor from
the category of folded chamber data to the category of fans of
[FOUNDATIONS.md](../../FOUNDATIONS.md) Def. 58.4.

**Source**: #24, referent-audit amendment; 002 T121; #180, #181.

## D4. The direction of the toric functor

**Decision**: $\Sigma \mapsto X_\Sigma$ is covariant: a morphism of fans $(N, \Sigma) \to (N', \Sigma')$
induces the toric morphism $X_\Sigma \to X_{\Sigma'}$. On affine pieces a face inclusion
$\tau \preceq \sigma$ induces $k[\sigma^\vee \cap M] \to k[\tau^\vee \cap M]$ and the open
immersion $U_\tau \hookrightarrow U_\sigma$. $X_\Sigma$ is the colimit over the face diagram in
schemes.

**Source**: [FOUNDATIONS.md](../../FOUNDATIONS.md) Def. 59.1, 59.2 ([@Tel22, §§2.6–2.7, 4.2]);
#24, foundations-compliance amendment (the direction is recorded data).

## D5. Cone types

**Decision**: Rational polyhedral cones and fans are Mathlib `PointedCone`s over $\mathbb Q \otimes L$;
closed round cones (nef, Mori) are `PointedCone`s over $\mathbb R \otimes L$; the ample cone is the
interior of the nef cone, an open convex cone stable under positive scaling, and is not a pointed
cone.

**Source**: #1, decision record 1, item 3, and the correction of 2026-10-28; #37 (closed);
[FOUNDATIONS.md](../../FOUNDATIONS.md) Def. 58.2.

## D6. Looijenga pairs

**Decision**: A Looijenga pair is a smooth projective rational surface $Y$ with an anticanonical
cycle $D = D_1 + \cdots + D_n$ of rational curves; its charge is $Q(Y, D) = 12 - D^2 - n$; a toric
(corner) blowup preserves $Q$, an interior blowup raises it by one, and the strict transform of
$D$ is the new anticanonical cycle. Task T011 reads these statements from Gross–Hacking–Keel,
*Mirror symmetry for log Calabi–Yau surfaces I* (Publ. Math. IHÉS 122, 2015), §1, through the
live library.

**Source**: #8, ambiguity resolutions (toric conventions); constitution M2.

## D7. Position in the work order

**Decision**: This feature is a consumer intake of the research programme (stages 3 and 5) under
constitution M9. It runs in its own document order and does not wait for a corpus milestone. A declaration that a task needs and that a task of another feature owns (a pending corpus unit of 002, an owner row of 003) is done first, at once, by that owning task, which keeps its place and ID.

**Source**: constitution M9, M11; 002 research D9; #24, #116 (stage questions).

## D8. Semifans

**Decision**: Semifans and semitoroidal compactifications are owned by feature 008 (research D5
there). This feature builds no declaration under those names.

**Source**: [FOUNDATIONS.md](../../FOUNDATIONS.md) Def. 58.5, Rem. 62.7; #24, foundations-compliance
amendment.
