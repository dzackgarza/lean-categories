# Arithmetic lattice foundations after upstream reuse

## Purpose

This file records the mathematical ownership and dependency order for arithmetic
formed modules and lattices.

It is not the live execution tracker. GitHub issues own current work state.
The central plan vault owns private plan state before public promotion.

Pinned Mathlib owns the general algebra, representation theory, local fields,
and adele rings. This project must connect those foundations to formed modules
and lattices.

Do not use this file as a general algebra syllabus. Do not create a parallel
definition for an existing construction.

For each item, first inspect current project declarations and pinned Mathlib.
The remaining delta can be a definition, theorem, functor, or comparison.

## Present project foundation

The project already has a substantial local algebra core.

| Area | Present project surface | Remaining boundary |
| --- | --- | --- |
| Fixed-value formed modules | `BilinModuleCat R W` and quadratic analogues | Select one public hierarchy and complete all comparisons |
| Variable-value forms | Total categories and change-of-value functors | Relate every public fiber to the total category |
| Scalar extension | Form and lattice scalar extension, exactness, and composition comparisons | Reuse it in all later local and adelic constructions |
| Duality | Algebraic duals, metric duals, and ideal-valued metric duals | Add determinant-line and Dedekind ideal packaging |
| Discriminant data | \(K/R\)-valued bilinear forms and \(K/2R\)-valued quadratic forms | Add more local classification and projective determinant comparisons |
| Orthogonal groups | \(O(L)\), submodule stabilizers, discriminant actions, and stable kernels | Add systematic equivariant centralizers and normalizers |
| Finite torsion forms | Height-one primary components, orthogonality, and projections | Add named elementary-lattice and local classification interfaces |
| Localization and residue | Generic localization and residue functors | Add generic completion and place-indexed realization |
| Framed realization | `GenFrame`, `BasisFrame`, `Coord`, and intrinsic comparison | Complete the general descent and matrix-realization comparisons |

This inventory does not certify every theorem named by a file. A file can contain
definitions or witness structures without the associated existence or
classification theorem.

## Upstream reuse boundary

Use these upstream owners directly.

| Area | Upstream owner |
| --- | --- |
| Rings, ideals, quotients, localization, and Dedekind domains | Mathlib `RingTheory` |
| Modules, tensor products, exactness, rank, bases, and exterior powers | Mathlib module and linear-algebra libraries |
| Torsion and primary decomposition | `Algebra.Module.Torsion` and `Algebra.Module.DedekindDomain` |
| Smith normal form | `LinearAlgebra.FreeModule.PID` |
| Scalar restriction, extension, and adjunction | `ModuleCat.ChangeOfRings` |
| Module-valued bilinear maps | `LinearMap.BilinMap R M W` |
| Module-valued quadratic maps | `QuadraticMap R M W` |
| Orthogonality, radicals, isometries, and signatures | Mathlib form libraries |
| Metric dual submodules | `BilinForm.dualSubmodule` |
| Representations and monoid-algebra modules | `RepresentationTheory.Basic` |
| Semisimple isotypic components | `RingTheory.SimpleModule.Isotypic` |
| Maschke semisimplicity | `RepresentationTheory.Maschke` |
| Fractional ideals and ideal classes | Mathlib Dedekind-domain libraries |
| Height-one completions | `adicCompletion` and `adicCompletionIntegers` |
| Finite adeles | `RingTheory.DedekindDomain.FiniteAdeleRing` |
| Number-field adeles and infinite places | Mathlib number-field libraries |
| Clifford, Lipschitz, Pin, and Spin groups | Mathlib Clifford-algebra libraries |
| Generic centralizers and normalizers | Mathlib group theory |
| Root systems and Weyl groups | `LinearAlgebra.RootSystem` |
| Analytic lattices and covolumes | `Algebra.Module.Lattice` |
| Concrete integral E8 data | Sphere-Packing-Lean `SpherePacking.Basic.E8` |
| Total-category reference constructions | Mathlib Grothendieck machinery and LeanFibredCategories |

The project must integrate these owners. It must not rebuild their general theory.

## Governing dependency spine

The foundation has this order.

\[
\begin{aligned}
&\text{Dedekind and global arithmetic} \\
&\qquad\downarrow \\
&\text{finite-projective and equivariant module arithmetic} \\
&\qquad\downarrow \\
&\text{formed modules, value change, scalar change, and duality} \\
&\qquad\downarrow \\
&\text{lattices, discriminant data, orthogonal actions, and completions} \\
&\qquad\downarrow \\
&\text{local, adelic, Clifford, spinor, and genus theory} \\
&\qquad\downarrow \\
&\text{definite, indefinite, reflection, and geometric branches.}
\end{aligned}
\]

A later layer must not supply a missing definition to an earlier layer.

## 1. Dedekind finite-projective arithmetic

`LatticeCat` permits finite projective carriers. Therefore, a basis-dependent
Gram determinant cannot be the global invariant.

The project needs a coherent finite-projective layer over a Dedekind domain:

- Local rank at each height-one prime.
- Constant rank under the exact required hypotheses.
- The determinant line
  \[
  \det_R P=\bigwedge^{\operatorname{rk}P}P.
  \]
- The Steinitz or ideal class of a finite projective module.
- The relation between the determinant line and a decomposition
  \[
  P\simeq R^{n-1}\oplus I.
  \]
- The determinant map of a pairing
  \[
  \det(b):\det P\longrightarrow (\det P)^*.
  \]
- The intrinsic discriminant ideal
  \[
  \operatorname{disc}(P,b)
  =
  \operatorname{Fitt}_0\!\left(\operatorname{coker}(\operatorname{ad}_b)\right).
  \]
- The comparison between this Fitting ideal and the determinant map.
- The comparison with a Gram determinant after a basis is chosen.
- Base-change and localization formulas for these objects.

If Mathlib lacks the full Steinitz classification theorem, record that exact gap.
Do not replace it with a free-module specialization.

## 2. Canonical formed categories

Use one canonical category for module-valued bilinear forms. Its objects have the
form

\[
(M,W,b),\qquad b:M\otimes_R M\to W.
\]

A morphism contains maps \(f:M\to N\) and \(\alpha:W\to V\). It satisfies

\[
\alpha\circ b=c\circ(f\otimes f).
\]

The remaining obligations are:

- Compare all current project presentations.
- Select one public presentation.
- Relate the fixed-value fibers to the total category.
- Supply change-of-value and scalar-change functors.
- Prove identity and composition comparisons.
- State the cokernel through its universal property.
- Prove that the cokernel kills the required mixed pairings.
- Add a quadratic analogue only when a current consumer requires it.

Do not replace `BilinMap` or `QuadraticMap` with new form types.

## 3. Arithmetic formed modules and lattices

Retain one coherent interface for the arithmetic properties which Mathlib does
not package as formed-lattice theory:

- Perfect and unimodular forms.
- Integral and \(I\)-integral forms.
- Even and \(I\)-even forms.
- Scale ideals.
- Value ideals generated by diagonal values.
- Finite projective formed modules.
- Finite free formed modules over a PID.
- Formed submodules and inclusion isometries.
- Finite-index and saturated formed submodules.
- Primitive inclusions and primitive closure.

Build orthogonal sums and finite orthogonal powers from existing form operations.
Do not create another tensor-product or base-change operation.

Keep these dual objects distinct:

\[
M^*=\operatorname{Hom}_R(M,R),
\]

\[
M^\#=\{x\in M_K\mid b_K(x,M)\subseteq R\},
\]

and the kernel, image, or cokernel of the adjoint map.

Reuse `BilinForm.dualSubmodule` for the metric dual foundation. Extend the
existing discriminant theory by proving

\[
A_L\simeq\operatorname{coker}(\operatorname{ad}_b)
\]

under the exact integral and nondegeneracy hypotheses. Then prove

\[
\operatorname{Fitt}_0(A_L)=\operatorname{disc}(L,b).
\]

## 4. Equivariant formed modules and lattices

Do not start with a bespoke module-over-group-ring lattice structure.

When \(G\) acts trivially on the value module \(W\), a \(G\)-equivariant
\(W\)-valued lattice has two standard presentations:

\[
BG\longrightarrow \operatorname{Lat}_R(W)
\]

and

\[
\rho:G\longrightarrow O(L).
\]

State and prove their comparison. The underlying module then has its standard
\(R[G]\)-module structure.

The equivariant layer must supply:

- Equivariant formed-module and lattice categories.
- Invariant and coinvariant formed submodules.
- Fixed and quotient constructions with their exact hypotheses.
- Centralizers and normalizers attached to \(\rho(G)\subseteq O(L)\).
- Equivariant actions on metric duals and discriminant forms.
- Equivariant localization, completion, and scalar extension.
- The existing involution theory as the \(G=C_2\) specialization.

Do not assert an integral isotypic direct sum without a semisimplicity theorem.
For \(K=\operatorname{Frac}(R)\), finite \(G\), and \(|G|\in K^\times\), first
use Maschke over \(K\):

\[
L_K\simeq\bigoplus_\chi (L_K)_\chi.
\]

Then define the integral intersections

\[
L_\chi=L\cap(L_K)_\chi.
\]

The finite defect between \(\bigoplus_\chi L_\chi\) and \(L\) is arithmetic
gluing data. It is not a missing canonical decomposition.

## 5. Place-indexed localization and completion

Replace the \(\mathbb Z_p\)-only completion surface with a general construction.

For a Dedekind domain \(R\), fraction field \(K\), and height-one point
\(v\), use Mathlib's

\[
R_v=\operatorname{adicCompletionIntegers}(v),\qquad
K_v=\operatorname{adicCompletion}(v).
\]

The project needs:

- Integral completion \(L\mapsto L_{R_v}\).
- Fraction-field completion \(L_K\mapsto (L_K)_{K_v}\).
- Compatibility with scalar extension, duals, orthogonal sums, and discriminants.
- Comparison with the existing localization and residue functors.
- The \(\mathbb Z_p\) and \(\mathbb Q_p\) constructions as specializations.
- A place-indexed interface for number fields.
- A clear separation between height-one points and archimedean places.

Do not model an archimedean place as a point of `Spec R`.

## 6. Finite and full adelic realization

Reuse Mathlib's finite adele ring. Do not implement a new restricted product.

The lattice layer needs:

\[
L_{\mathbb A_f}=L\otimes_R\mathbb A_{K,f},
\qquad
\widehat L=\prod_v L_v,
\]

and the integral finite adeles

\[
\widehat R=\prod_v R_v\subseteq\mathbb A_{K,f}.
\]

The required interfaces and theorems are:

- Diagonal realization of \(K\), \(R\), and \(L\).
- The integral lattice inside its finite adelization.
- Restricted-product descriptions of adelic formed modules.
- Adelic orthogonal groups \(O(V)(\mathbb A_f)\).
- The compact-open stabilizer \(K_L=\prod_v O(L_v)\).
- The arithmetic intersection or pullback statement
  \[
  R=K\cap\widehat R\quad\text{inside }\mathbb A_{K,f}.
  \]
- The corresponding lattice intersection statement.

Use the full adele ring only for number fields until a separate function-field
definition is present. Do not generalize Mathlib's number-field product by name.

## 7. Elementary discriminant modules and local classification

The existing discriminant and primary-decomposition layers support a small
foundational addition.

For a height-one prime \(\mathfrak p\), define

\[
\operatorname{IsPElementary}(L,\mathfrak p)
\iff
\mathfrak p A_L=0.
\]

Then package \(A_L\) as an \(R/\mathfrak p\)-vector space and define

\[
a_\mathfrak p(L)
=
\dim_{R/\mathfrak p}A_L.
\]

The later local layer needs:

- Lattices over DVRs and completed local rings.
- Residue forms and unit square-class filtrations.
- Norm and scale ideals.
- Jordan constituents and decomposition theorems.
- Hasse invariants in the required local contexts.
- Witt comparisons needed by classification.
- A separate dyadic classification layer.
- Finite quadratic modules at \(2\).

The \(K/R\) bilinear and \(K/2R\) quadratic value objects already exist.
Do not list them as missing definitions.

## 8. Canonical Clifford and spinor theory

The current spinor files provide a prototype vocabulary. A chosen homomorphism
with prescribed reflection values is not yet the canonical spinor norm.

Reuse Mathlib's Clifford algebra, Lipschitz group, Pin group, Spin group, and
Clifford action. Integrate them with the project form and orthogonal-group
categories.

The missing foundation is:

\[
\operatorname{Cl}(V,q),\quad
\Gamma(V,q),\quad
\operatorname{Pin}(V,q),\quad
\operatorname{Spin}(V,q),\quad
\theta:O(V)\to K^\times/(K^\times)^2.
\]

It must include:

- The canonical spinor-norm construction.
- The exact hypotheses for its domain and codomain.
- Its value on reflections.
- Comparison with products of reflections.
- The relevant kernels and exact sequences.
- Local and adelic spinor maps.

Define the canonical spinor kernel and spinor genus only after this layer exists.

## 9. Genus and local-to-global comparison

Keep genus as a local isometry relation. Generalize the current
\(\mathbb Z\)-specific definition to the correct place-indexed context.

For number fields, the local presentation includes all finite places and the
required archimedean data.

After the adelic layer exists, prove the comparison with the double-coset
presentation

\[
O(V)(K)\backslash O(V)(\mathbb A_f)/K_L.
\]

The local and adelic definitions are two presentations of one theory. Do not keep
them as unrelated notions.

Only after this comparison should later work develop:

- Spinor genera.
- Class sets and class numbers.
- Strong approximation statements.
- Masses and local density products.

## 10. Embeddings, complements, and gluing

Preserve the existing formed-module work on:

- Orthogonal complements.
- Primitive orthogonal embeddings.
- Saturation and primitive closure.
- Discriminant data for a submodule and its complement.
- Isotropic subgroups of discriminant forms.
- Overlattices constructed from isotropic subgroups.
- Recovery of gluing data from an overlattice.
- Extension criteria for isometries across a gluing construction.

State each result at the formed-module level when possible. Specialize to
integral lattices only when arithmetic hypotheses require it.

The equivariant isotypic defect must use this same gluing theory. It must not
create a second gluing mechanism.

## 11. Algebraic and analytic lattice comparison

Mathlib's analytic lattice is a discrete, cocompact submodule of a normed real
vector space. The project needs a comparison from an algebraic lattice:

\[
(L,b)\longmapsto L\hookrightarrow L_{\mathbb R}.
\]

This comparison must state the required embedding, finite-rank, and positivity
hypotheses. It must connect the algebraic determinant data with covolume data.

After suitable complex or Hodge data exists, extend the bridge to

\[
L\hookrightarrow V_{\mathbb C},\qquad V_{\mathbb C}/L.
\]

Do not identify \(L_K/L\) with a complex torus. For \(R=\mathbb Z\), the first
object is a torsion module such as \((\mathbb Q/\mathbb Z)^n\).

## 12. Definite, indefinite, reflection, and geometric branches

After the shared foundation, organize the later theory by mathematical owner.

### General formed lattices

This branch owns duality, discriminant data, orthogonal sums, embeddings,
gluing, scalar change, and equivariant structures.

### Local arithmetic

This branch owns completions, residue forms, Jordan theory, Hasse invariants,
Witt theory, dyadic classification, and local spinor theory.

### Definite arithmetic

This branch owns finite automorphism groups, minima, short vectors,
enumeration, theta series, class numbers, and mass formulas.

A basic theta series belongs early in this branch. A mass formula belongs late.
It requires finite class sets, finite automorphism groups, adelic quotients, and
local measure theory.

### Indefinite arithmetic

This branch owns isotropic theory, hyperbolic planes, Witt index, arithmetic
orthogonal groups, spinor kernels, strong approximation, and symmetric domains.

### Reflection and root theory

General reflections and root pairings can apply to indefinite lattices. Keep
them in a general reflection branch. Place positive-definite root-lattice and
ADE classification in the definite branch.

### Geometric realization

This branch owns period, Hodge, complex-torus, and moduli constructions. It
depends on the algebraic-to-analytic lattice comparison.

## 13. Standard lattices

Define named lattices through the generic formed-lattice constructions.

- Compare the project E8 object with Sphere-Packing-Lean `E8Lattice`.
- Record and prove each sign change.
- Define the hyperbolic plane from its form.
- Build \(U^n\) through finite orthogonal powers.
- Build \(E_8(-1)^n\) through scaling and orthogonal powers.
- Define \(L_{K3}=U^3\perp E_8(-1)^2\).
- Derive rank, signature, parity, and discriminant from generic theorems.

Do not create a matrix-first parallel hierarchy for these objects.

## Dependency order

Use this order for new work:

1. Reconfirm the pinned Mathlib reuse map and current project comparisons.
2. Complete Dedekind finite-projective determinant and ideal-class arithmetic.
3. Consolidate the canonical formed-module and lattice categories.
4. Extend existing dual and discriminant results to projective determinant ideals.
5. Develop equivariant formed lattices and rational isotypic intersections.
6. Generalize completion to all height-one places.
7. Build finite adelic lattice and orthogonal-group realization.
8. Integrate Clifford theory and construct the canonical spinor norm.
9. Generalize genus and prove its adelic comparison.
10. Split later work into local, definite, indefinite, reflection, and geometric branches.

Steps 5 and 6 can proceed in parallel after steps 2 through 4. Step 8 can proceed
in parallel with step 7. Genus comparison needs both completion and adelic layers.

Existing gluing and named-lattice work remains valid. It must consume these common
foundations when they apply.

## Current framed-category realization

The fixed-rank frame and intrinsic comparison layer exists under issue #33.

- `GenFrame R n` and `BasisFrame R n` use structured-arrow loci.
- `Coord R n` has arbitrary module maps as morphisms.
- `CoordLatticeCat R n` is a categorical pullback over the module carrier.
- `coordLatticeToIntegral` compares a coordinatized lattice with its intrinsic lattice.
- `EvenLatticeCat` is the full subcategory defined by `IsEven`.

This does not complete the arbitrary-index `FramedModules` catalogue entry. It also
does not define `SymMat_n` or the full Gram comparison functor.

## Items that are not present foundation work

Do not move these items before their stated prerequisites:

- Mass formulas before class-set finiteness and adelic measure theory.
- Full dyadic classification before generic local completion and Jordan theory.
- Spinor genus before a canonical spinor norm.
- Integral isotypic direct sums without semisimplicity and gluing analysis.
- Full adeles over function fields through the number-field definition.
- A new `Spec(\mathbb Z)` construction.
- Complex tori before the algebraic-to-analytic lattice comparison and complex data.

## Evidence boundary

This revision organizes a supplied arithmetic-foundation audit against current
repository plan surfaces. It does not independently certify all upstream claims.

The earlier reuse audit used pinned Mathlib commit
`81a5d257c8e410db227a6665ed08f64fea08e997`.

The supplied audit cites these upstream families:

- `Mathlib.RepresentationTheory.Basic` and `Maschke`.
- `Mathlib.RingTheory.SimpleModule.Isotypic`.
- `Mathlib.Algebra.Module.DedekindDomain`.
- `Mathlib.RingTheory.DedekindDomain.AdicValuation`.
- `Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing`.
- `Mathlib.NumberTheory.NumberField.AdeleRing` and infinite places.
- `Mathlib.LinearAlgebra.CliffordAlgebra.Basic` and `SpinGroup`.
- `Mathlib.Algebra.Module.Lattice`.

At implementation time, verify every exact declaration and source path against the
pinned Mathlib revision. Search prior Lean formalizations before new authorship.

“Not found” means “not found in the inspected sources and revisions.” It does not
assert global nonexistence.

## Completion standard

Each new declaration must identify its relationship to existing mathematics. Use
an instance, comparison map, functor, or equivalence as appropriate.

Each theorem must state the exact ring, projectivity, finiteness, nondegeneracy,
semisimplicity, and place hypotheses it uses.

The root module must expose one coherent hierarchy. Passing compilation does not
prove that two parallel presentations agree.
