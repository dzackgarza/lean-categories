# Outstanding work

Measured against the audit in `Repo-Organization-for-Category-Theory.md` (its final
ten-item list and the Tier 0–3 delta), checked against HEAD `433f811`: working tree
clean, no `sorry`, no project axioms.

## Closed since that audit

Tier 0 documentation corrections; `I`-duality over fractional ideals
(`IdealDual.lean`); the equivariant and isotypic layer (`Equivariant.lean`); Dedekind
projective arithmetic (`DeterminantLine.lean`, `FittingIdeal.lean`); the arithmetic
base and one unified place type (`ArithmeticBase.lean`, `ArithmeticPlace.lean`); ring
adeles; adelic genus, where `SameGenus` is now `SameAdeleGenus ℚ` (`LocalGlobal.lean:133`)
with the classical real and `p`-adic condition as a theorem rather than a second
definition; canonical Hasse and spinor theory; ideles; Jordan existence and uniqueness;
topological adelic orthogonal groups with Haar measure.

## 1. Mass formula

`mass` (`Mass.lean:61`) sums the reciprocal orthogonal group orders over an explicit
`List` of lattices. Its module docstring still states that finiteness of a genus is not
available in this development. `genus_finite` (`ReducedBasis.lean:458`) makes that
statement false, so the mass of a genus is definable now as a finite sum over the class
set. This is the immediate next step, and it retires the stale docstring with it.

The Smith–Minkowski–Siegel formula itself then needs three further pieces:

- the local integral orthogonal subgroup proved to be the stabilizer of the completed
  integral lattice — the subgroup is currently cut out by matrix integrality, and the
  identification is recorded as unproved at `LocalDensity.lean:19`;
- an archimedean factor: `DensityProduct.lean` factorizes the volume over the *finite*
  adelic orthogonal group only;
- a fundamental domain for the diagonally embedded rational orthogonal group, which is
  what compares the adelic Haar measure with a global counting measure. Recorded as
  absent at `DensityProduct.lean:26`.

## 2. Theta series are not modular

`Theta.lean` counts representation numbers and assembles their generating power series.
No file in the repository mentions `ModularForm`, `UpperHalfPlane` or
`SlashInvariantForm`, so the series is formal only. The analytic mass route and
Siegel–Weil both consume the modularity statement.

## 3. ADE realization direction

`adeClassification` (`DiagramShape.lean:440`) constrains the graph of a base of simple
roots to a path or to a three-arm star with an admissible triple. The converse is
missing: no theorem sends an admissible diagram back to a named lattice, and no
uniqueness statement says an irreducible root lattice is isometric to the named lattice
of its diagram.

The named objects are also incomplete. `A_n` and `D_n` are objects of `RootLatticeCat`
(`DefiniteNondegenerate.lean:122`, `DRootLattice.lean:42`), `E₈` is an object
(`DefiniteNondegenerate.lean:141`), `E₆` exists only as a Gram presentation in
`Standard.lean:582`, and `E₇` does not exist in any form.

## 4. Indefinite branch untouched

`DefiniteIndefinite.lean` separates the definite and indefinite loci. Nothing follows on
the indefinite side: no strong approximation and no Eichler theorem — neither term
occurs anywhere in the repository. The definite side now carries reduction theory, class
finiteness, theta series and masses, so the imbalance is now the largest one in the
Tier 3 list.

## 5. Projectivity of abelian varieties

`IsAbelianVariety` (`ComplexTorusManifold.lean`) asks for a Riemann form integral on the
period lattice, and `isAbelianVariety_gaussianTorus` proves `ℂ/(ℤ+ℤi)` satisfies it, so
the predicate has an inhabitant. The embedding theorem needs four upstream layers, in
dependency order:

1. **Holomorphic line bundles on a complex manifold.** Mathlib has smooth vector bundles,
   but no holomorphic structure on them, no analytic Picard group and no holomorphic
   section. Everything below rests on this.
2. **Appell–Humbert.** Line bundles on `V/Λ` classified by a hermitian form `H` with
   `Im H` integral on `Λ`, plus a semicharacter. This is where `IsRiemannForm` earns its
   keep: the Riemann form is `Im H`. Mathlib has sesquilinear forms; the correspondence
   is absent.
3. **Theta functions and cohomology.** Global sections of `L(H, α)`, their dimension, and
   the Lefschetz theorem that `L^{⊗3}` is very ample. Needs sheaf cohomology on complex
   manifolds.
4. **A target.** `ℙ^N(ℂ)` as a charted complex manifold with a closed-embedding notion.
   Mathlib has projective space as a scheme and as a topological space, not as a complex
   manifold.

Add Chow/GAGA if the intended conclusion is "projective algebraic variety" rather than
"closed complex submanifold of `ℙ^N`". Layers 1 and 4 are the real cost; both are builds
of the same kind as the quotient manifold in `ForMathlib/QuotientManifold.lean`.

## 6. Name collision

`structure ComplexTorus` (`ComplexTorusManifold.lean:266`) shares its name with the
module `LeanCategories.Lattices.Valued.ComplexTorus`. It resolves and builds. Rename one
of the two if the collision is unwanted.
