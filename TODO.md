# Outstanding work

Measured against the audit in `Repo-Organization-for-Category-Theory.md` (its final
ten-item list and the Tier 0–3 delta).

## Closed since that audit

Tier 0 documentation corrections; `I`-duality over fractional ideals
(`IdealDual.lean`); the equivariant and isotypic layer (`Equivariant.lean`); Dedekind
projective arithmetic (`DeterminantLine.lean`, `FittingIdeal.lean`); the arithmetic
base and one unified place type (`ArithmeticBase.lean`, `ArithmeticPlace.lean`); ring
adeles; adelic genus, where `SameGenus` is now `SameAdeleGenus ℚ` (`LocalGlobal.lean:133`)
with the classical real and `p`-adic condition as a theorem rather than a second
definition; canonical Hasse and spinor theory; ideles; Jordan existence and uniqueness;
topological adelic orthogonal groups with Haar measure; the mass of a genus
(`Mass.lean`); the local integral subgroup as the stabilizer of `L ⊗ O_v`
(`LocalDensity.lean`); `E₆` and `E₇` as objects of `RootLatticeCat`.

## 1. The Siegel mass formula

`genusMass` (`Mass.lean`) sums the reciprocal orthogonal-group orders over the class set
of a genus, which `genus_finite` (`ReducedBasis.lean:458`) makes a finite sum. The
Smith–Minkowski–Siegel formula equates that sum with a product of local densities. Two
pieces of that equation are missing:

- **The archimedean factor.** `DensityProduct.lean` factorizes the Haar volume over the
  *finite* adelic orthogonal group. The real place contributes no factor yet, so the
  product cannot be compared with a global volume.
- **A fundamental domain for the rational orthogonal group.** The global volume
  comparison needs the diagonally embedded `O(V)(K)` to have a fundamental domain in the
  adelic group, which is what turns the adelic Haar measure into a lattice count.
  Recorded as absent at `DensityProduct.lean:26`.

The third piece, the identification of the local integral subgroup with the stabilizer
of the completed integral lattice, is now proved: `localLatticeBasis` is a basis of
`L ⊗ O_v` extended to the local field, and `mem_localIntegralOrthogonalSubgroup_iff`
reads integrality of the matrix and its inverse as preservation of that lattice.

## 2. Theta series are not modular

`Theta.lean` counts representation numbers and assembles their generating power series.
No file in the repository mentions `ModularForm`, `UpperHalfPlane` or
`SlashInvariantForm`, so the series is formal only. The analytic mass route and
Siegel–Weil both consume the modularity statement, which needs Poisson summation for a
`ZLattice` and the transformation law it yields.

## 3. ADE realization direction

`adeClassification` (`DiagramShape.lean:440`) constrains the graph of a base of simple
roots to a path or to a three-arm star with an admissible triple. Every simply-laced
type now has an object of `RootLatticeCat` — `A_n`, `D_n` (`DRootLattice.lean:42`), `E₆`,
`E₇` and `E₈` (`DefiniteNondegenerate.lean`) — but the converse of the classification is
missing: no theorem sends an admissible diagram back to the named lattice, and no
uniqueness statement says an irreducible root lattice is isometric to the named lattice
of its diagram.

The step that carries the cost is the enumeration of a path: the Gram matrix of a base
is determined by its graph, since the diagonal is `-2` and the off-diagonal entries are
adjacency, so what remains is to order the vertices of a path or star so that the matrix
becomes the standard one. `isoFiniteLatticeOfGramMatrix` then supplies the isometry.

## 4. Indefinite branch untouched

`DefiniteIndefinite.lean` separates the definite and indefinite loci. Nothing follows on
the indefinite side: no strong approximation and no Eichler theorem — neither term
occurs anywhere in the repository. The definite side now carries reduction theory, class
finiteness, theta series and masses, so the imbalance is the largest one left in the
Tier 3 list.

## 5. Projectivity of abelian varieties

`IsAbelianVariety` (`ComplexTorus.lean`) asks for a Riemann form integral on the period
lattice, and `isAbelianVariety_gaussianTorus` proves `ℂ/(ℤ+ℤi)` satisfies it, so the
predicate has an inhabitant. The embedding theorem needs four upstream layers, in
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
