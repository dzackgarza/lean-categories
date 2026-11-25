# Data model: the owner table

Each row is one public notion of this feature. "Owner" is the declaration that defines it, at
its generality. "Specializations" are the familiar forms that must be theorems about the owner.
"State" is the source at `533e9259` (plan.md, "Current source state"). A task closes a row when
the owner exists and every specialization has its comparison theorem (plan.md Contract O).

| Row | Notion | Owner (module) | Generality | Specializations to compare | State |
| --- | --- | --- | --- | --- | --- |
| N01 | correlation maps, radicals, separation | `Modules/Bilinear/Valued/{Fixed,Total}.lean` | $W$-valued forms over a commutative ring | symmetric one-radical form; adjoint $x \mapsto b(x,-)$ of FOUNDATIONS Def. 18.1 | partial |
| N02 | perfection; fraction-field nondegeneracy and perfection | same; `Lattices/Valued/MetricDual.lean` (`IsFractionFieldPerfect`) | forms over a domain | equivalence for finite projective symmetric scalar-valued forms | partial |
| N03 | lattice category and its presentations | `Lattices/Valued/{Basic,Arithmetic}.lean` | finite projective, integral, symmetric, fraction-field nondegenerate | fixed/variable value, framed, coordinate, arbitrary index, $\mathbf{SymMat}_n$, Gram | partial ($\mathbf{SymMat}_n$, Gram absent) |
| N04 | metric $I$-dual, $I$-modularity | `IdealDual.lean` (`fractionalIdealDual`, `IsFractionalIModular`) | fractional ideals of a Dedekind domain | `metricDual` ($I = R$), `idealDual` (integral $I$), unimodularity | present; comparisons partial |
| N05 | relative discriminant $A_L^I$, $K/I$ form, $K/2I$ refinement | `Discriminant.lean`, `IdealDual.lean` | $L \subseteq L^{\# I}$ | $K/R$, $K/2R$; adjoint defect (Riesz) | partial ($K/2I$ absent) |
| N06 | determinant line, Steinitz class | `DeterminantLine.lean` | finite projective of constant rank | Gram determinant ideal after a basis; $\operatorname{Cl}(R) \cong \operatorname{Pic}(R)$ | partial |
| N07 | discriminant ideal, Fitting ideal | `FittingIdeal.lean` | discriminant module | localization; orthogonal sum | partial |
| N08 | PID and Dedekind structure interfaces | Mathlib owners; `SmithNormalForm.lean` | finite modules | rank, elementary divisors, discriminant modules | partial |
| N09 | primitive embedding, complement, overlattice, gluing | `Gluing.lean`, `Overlattice*.lean`, `Cusps.lean` | formed lattices | construction and recovery; isometry extension criterion | partial |
| N10 | $G$-lattice and derived constructions | `Equivariant.lean`, `Involution.lean`, `FamilyStabilizer.lean` | functors $BG \to \mathbf{Lat}_R^{\simeq}$ | $G \to O(L)$; $C_2$ involutions | present; comparisons partial |
| N11 | rational isotypic constituents and integral glue | `Equivariant.lean` | semisimple $K[G]$ | finite defect through N09 | partial |
| N12 | places and local realizations | `ArithmeticPlace.lean`, `Localization.lean`, `Completion.lean`, `Residue.lean` | arithmetic base | $\mathbb Z_p$, $\mathbb Q_p$ | partial |
| N13 | elementary modules, dyadic places | `Elementary.lean`, `Dyadic.lean` | annihilator ideals; height-one places | prime and $\mathbb Z_2$ cases | present |
| N14 | integral finite and full ring adeles | `IntegralAdeleRing.lean`, `Adele.lean` | number rings (present); arithmetic base (target) | $\mathbb A_{\mathbb Z} \cong \mathbb R \times \prod_p \mathbb Z_p$; field adeles | partial |
| N15 | ring-adelic genus | `Adele.lean`, `LocalGlobal.lean` | finite projective lattices | placewise; $\mathbb R$ and $\mathbb Z_p$ (`sameGenus_iff_sameAdeleGenus`); double coset | partial |
| N16 | Hasse invariant | `Hasse.lean`, `HasseInvariance.lean` | nondegenerate quadratic spaces over a field with Hilbert symbol | diagonal formula | partial (diagonal value only) |
| N17 | spinor norm, spinor kernel, spinor genus | `CanonicalSpinorNorm.lean`, `SpinorGenusAdelic.lean`, `AdelicSpinorNorm.lean` | quadratic spaces over fields | reflection formula; `Spinor.lean` characterization | partial |
| N18 | Jordan, Witt and dyadic classification | `Jordan*.lean`, `Witt.lean`, `Dyadic*.lean` | DVR lattices | $\mathbb Z_2$ | partial (dyadic absent) |
| N19 | signatures and loci | `Signature.lean`, `DefiniteIndefinite.lean` | real places of an arithmetic base | integer signature | partial |
| N20 | reflections, roots, Weyl chambers | `Reflection*.lean`, `Root*.lean`, `WeylChambers.lean` | general lattices; definite locus for roots | root pairing realization | partial |
| N21 | named lattices | `Standard.lean`, `RootLattice.lean`, `ADERealization.lean`, `U2Lattice.lean` | generic constructions | $E_8$ comparison (done), $U^{\perp n}$, $\Lambda_{K3}$ | partial |
| N22 | analytic realization | `Topological.lean`, `RealTorus.lean` | finite rank $\mathbb Z$-lattices | Mathlib `ZLattice`, covolume | partial |
| N23 | Hodge structures, complex tori, period domains | `ComplexStructure.lean`, `ComplexTorus.lean`, `PeriodDomainData.lean` | filtered objects; HS and MHS | Riemann forms; Type IV domains | partial (Hodge categories absent) |
| N24 | class set, class number, mass | `Mass.lean`, `ClassFiniteness.lean` | definite genus | explicit-family mass; double coset | partial (finiteness absent) |
| N25 | theta series and modularity | `Theta.lean` | positive definite lattices | Mathlib analytic theta | partial |
| N26 | local densities and Siegel formula | `LocalDensity.lean`, `DensityProduct.lean` | finite adelic groups | real factor; volume comparison | partial (formula absent) |
| N27 | indefinite theory | `IsotropicReduction*.lean`, `PositiveCone*.lean` | indefinite loci | strong approximation; Eichler | partial (absent: strong approximation, Eichler) |

"Present" means the owner exists at `533e9259`; "partial" means the owner or some comparisons
are missing; the task of the row starts from the source at its own revision (Contract O).
