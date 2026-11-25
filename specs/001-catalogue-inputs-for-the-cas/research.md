# Research: Catalogue inputs for the computer-algebra roadmap

Each entry gives the decision, the reason from the mathematics and the sources, and the
alternative that the reason excludes. Evidence of the present state is in the issues #182 to #200
(read at `main` `443fba9`), #201 to #211 (read at `f009120`) and #212 to #225 (read at `fc549ba`).

## D1 (#193): owners of the arithmetic operations

- **Decision**: `·` at `cat.magmas`; `+` at `cat.additive_magmas`; `1` and $x^k$ at
  `cat.monoids`; `0` at `cat.additive_monoids`; inverse at `cat.groups`; negation and
  subtraction at `cat.additive_groups`. Every other row is a `refines` restriction.
  $\mathbf{AddGrp} \to \mathbf{Grp}$ is not structural.
- **Reason**: a magma is $\operatorname{Op}_2(\mathbf{Set})$ and each later stage adds structure
  (`FOUNDATIONS.md` Def. 12.1-12.3). The unit first exists in the registered tower at monoids;
  Mathlib has no bundled category of unital magmas. A structural functor sends an object to its
  underlying object (`Reg/Entry.lean`, `FunctorEntry.structural`); $\mathbf{AddGrp} \to
  \mathbf{Grp}$ renames the operation, so on it `·` would denote `+`.
- **Excluded**: separate unrestricted rows at monoids, semirings and rings (three owners of `·`).

## D2 (#200): the cycle through subobjects

- **Decision**: one invertible cell $\mathrm{dom} \circ \mathrm{whole} \cong 1$ with identity
  components; a validator rule that every structural cycle has a cell to the identity.
- **Reason**: every route from a set to `Sets` through `Subobjects(Sets)` is $(\mathrm{dom} \circ
  \mathrm{whole})^n$, which the one cell identifies with $1$. The reverse composite is not the
  identity: $\emptyset \subseteq \{0\}$ goes to $\emptyset \subseteq \emptyset$.

## D3 (#185, #190): references to existing rows

- **Decision**: `ComputationRef.application (object)` and `ComputationRef.binder (binder)`, each
  resolving to the field of the existing row.
- **Reason**: constitution M7 keeps one field per meaning. A second morphism row would copy the
  declaration that `ObjectEntry.application` and `BinderEntry.operation` hold.

## D4 (#183): which numerals carry evidence

- **Decision**: only an explicit proposition parameter of the numeral declaration carries
  evidence. `num.sets.fin` ($k < n$) does; ring numerals do not.
- **Reason**: the numeral $k$ of $\mathbb{Z}/n$ is the image of $k$ under $\mathbb{Z} \to
  \mathbb{Z}/n$, total (Mathlib `ZMod.natCast_self`); `finPoint (n k) (h : k < n)` has the
  parameter (`Sem/Foundation/Morphisms.lean:30`). Audit LC-183-F01.
- **Procedures**: decision procedures of this library (`meta` procedures, LC-18): $<$ on
  $\mathbb{N}$ by `Nat.decLt`; totality and distinct arguments of a graph literal by decidable
  quantification over a `Fintype` domain; closing of a literal statement by `DecidableEq` of the
  literal type. A procedure that fails leaves the instance unsettled.

## D5 (#191): power-object maps

- **Decision**: morphism rows for membership, extent, image and inverse image; the transpose at
  every stage $Y$; the fields of `PowerObjectEntry` point to the rows.
- **Reason**: Mac Lane and Moerdijk IV.1 define the power object by the natural bijection at every
  stage; the global form is its case $Y = 1$. `main` already has `fun.sets.power_set`.

## D6 (#186, #194): the generating levels of numerals

- **Decision**: `0` at additive monoids; $k \in \mathbb{N}$ at the coslice
  $\mathbb{N}/\mathbf{AddMon}$; semiring and ring numerals are restrictions.
- **Reason**: LC-15 makes a numeral the image under a universal map. The zero monoid is initial
  in $\mathbf{AddMon}$ and gives only $0$. An object of $\mathbb{N}/\mathbf{AddMon}$ is an additive
  monoid with a chosen element (the image of $1$), and $\mathbb{N}$ is initial there; Mathlib
  `AddMonoidWithOne` with `Nat.cast` is the same structure. The coslice uses the registered
  constructor `ctor.coslice`, so no new kind of category is needed.
- **Excluded**: numerals at semirings as the owner (the structure that generates them is smaller).

## D7 (#184): one authority for written names

- **Decision**: `name` stays the function-call form; an optional structured `notation` carries
  only the other forms; the index is projected from the rows.
- **Reason**: audit LC-184-F01 shows that `name` already holds `abs`, `sqrt`, `derivative`.

## D8 (#198): Spec needs the opposite category

- **Decision**: register `ctor.opposite`; Spec is a functor on `opposite(cat.commutative_rings)`.
- **Reason**: `Catalogue/Syntax.lean` has no opposite expression (its constructors are atom,
  construct, familyApp, familyTotal, classifierTotal, refine, opaque); Spec is contravariant
  (Hartshorne II.2; Mathlib `Scheme.Spec : CommRingCatᵒᵖ ⥤ Scheme`). A constructor fits the
  existing `construct` expression.

## D9 (#188): reading rules carry their data

- **Decision**: a reading rule has typed source, typed target, the selected map, and an
  identification theorem. The whole-subset reading requires a declared inclusion.
- **Reason**: audit LC-188-F01: the images of $i_0, i_1 : 1 \to \{0, 1\}$ differ, so $X$ and $Y$
  alone do not fix the subset.

## D10 (#192): the parameter is a morphism of `ModuleCat R`

- **Decision**: `f : W ⟶ W'` in `ModuleCat R`, through $\mathbf{CRing} \to \mathbf{Ring}$.
- **Reason**: `FOUNDATIONS.md` Def. 15.5 states change of values on module morphisms; the
  admission `admitLinear` exists for these homs (`Sem/Modules/LinearMaps.lean`).

## D11 (#187): names of shape objects

- **Decision**: Mathlib's constructor names; $0, \dots, n-1$ for `Fin n`.
- **Reason**: the shapes are Mathlib inductive types; their constructor names are their
  mathematical labels, and a declared name removes the dependence on constructor order.

## D12 (#197): property and structure classifiers

- **Decision**: a refinement declaration only for property classifiers; a validator refuses one
  for a structure classifier.
- **Reason**: for a property the fibre is a subsingleton and $\tilde{X} = \langle X, h \rangle$ is
  unique up to unique isomorphism (`ObjectProperty.FullSubcategory`); for a structure the fibre
  has many points and an existence proof selects none (`FOUNDATIONS.md` Def. 46.3).

## D13 (#196): constructor roles

- **Decision**: a `ConstructorRole` per constructor with its universal data; the core inclusion,
  the slice forget and the coslice forget are structural; $\mathrm{dom}$, $\mathrm{cod}$, the
  projection of elements and evaluation are not.
- **Reason**: a structural functor sends an object to its underlying object. A core object and a
  slice or coslice object have an underlying object of $C$; an arrow has two ends and no
  underlying object; the projection of a category of elements is a fibration projection, which
  `FunctorEntry.structural` excludes.

## D14 (#182): result kinds

- **Decision**: every operation row states `fixed` or `choice`. The `fixed` example with
  `Classical.choice` is `fun.modules.rank`.
- **Reason**: `Module.rank` is a supremum of cardinals of linearly independent families, a
  prescribed value whose definition depends on `Classical.choice`. The task confirms the axiom
  dependence with `#print axioms` in its test module. Generators and bases are fibres
  (`FOUNDATIONS.md` Def. 73.2-73.6, Def. 46.3).

## D15 (#199): subtraction of ℕ

- **Decision**: $a - b$ on $\mathbb{N}$ is declared on the domain $b \le a$ with an admission.
- **Reason**: LC-14 forbids the truncated subtraction (`Nat.sub` is total by truncation).

## D16 (#195): unbounded semilattices and names

- **Decision**: categories of join- and meet-semilattices without bounds in `ForMathlib`, after
  the search; ids `cat.preorders`, `cat.join_semilattices`, `cat.meet_semilattices`,
  `cat.order_lattices`, `cat.bounded_order_lattices`; keep `cat.partial_orders` and
  `cat.linear_orders`; delete `cat.partially_ordered_sets` and `cat.totally_ordered_sets`.
- **Reason**: $(\mathbb{Z}, \max)$ has no bottom, so Mathlib `SemilatSupCat` (with $\bot$) does
  not contain it. Mathlib `Lat` is already unbounded. The prefix `order_` keeps "lattice" for the
  form lattices of this library. The pair `cat.partial_orders`, `cat.linear_orders` has the
  structural functors, the relations and the named orders (#195).

## D17 (#204): the inclusion of a refinement is derived

- **Decision**: `SemanticState.structuralEdges` derives the edge $\mathrm{refine}(B, c) \to B$ from
  each category row with a `refine` expression, as it derives the forget of a classifier total;
  a functor row equal to it is refused.
- **Reason**: a refinement is a full subcategory of its base (objects of $B$ with evidence for
  $c$), so its inclusion is determined by the expression. One rule covers the seven refinements
  and every later one.
- **Excluded**: one functor row for each refinement, which states again what the expression says.

## D18 (#202): schemes reach sets through topological spaces

- **Decision**: register the category of topological spaces (Mathlib `TopCat`) with its structural
  forget, and $\mathbf{Sch} \to \mathbf{Top}$ as a structural row.
- **Reason**: the underlying set of a scheme is the set of points of its underlying space; a
  structural row is immediate, so the composite is not one row.
- **Excluded**: one row $\mathbf{Sch} \to \mathbf{Set}$, which hides the topological space that a
  later operation on schemes reads.

## D19 (#207): modules over commutative rings as modules over rings

- **Decision**: one structural row from `cat.modules_over_rings_ext` to `cat.modules_total` over
  $\mathbf{CRing} \to \mathbf{Ring}$, acting on maps by the transpose of the
  extension-restriction adjunction.
- **Reason**: the two Grothendieck constructions have the same objects over a commutative ring,
  and the adjunction $S \otimes_R - \dashv f^{*}$ identifies their maps; the functor keeps the
  underlying module.
- **Excluded**: a second registration of modules over commutative rings with restriction of
  scalars, which would give one object two categories with no comparison.

## D20 (#201, #208, #209, #210): forgetful functors that Lean already declares

- **Decision**: register the existing declarations `crystalsToSets`, `CuspObject.lattice`,
  `definiteForget`, `indefiniteForget` and the three full-subcategory inclusions as structural rows;
  `cat.crystals` becomes a category that is not opaque.
- **Reason**: each declaration sends an object to its underlying object; only the registry row is
  missing.
- **Excluded**: new declarations for these functors.

## D21 (#215): the square root on ℂ is the principal value

- **Decision**: $\sqrt{z} = z^{1/2} = \exp(\tfrac{1}{2} \log z)$ with $\arg z \in (-\pi, \pi]$, a
  `fixed` operation declared by `Complex.cpow`.
- **Reason**: the computation that consumes the row states $\sqrt{-4} = 2i$; $\log(-4) = \log 4 +
  i\pi$ gives $(-4)^{1/2} = 2 e^{i\pi/2} = 2i$, so the principal value is the stated convention.
  Mathlib defines the principal logarithm and `Complex.cpow` with this branch; a written $\sqrt{z}$
  with a fixed value is a function, not a choice.
- **Excluded**: a `choice` operation over the two roots (FR-017), which gives the written $\sqrt{-4}$
  no value.

## D22 (#213): the factorization uses the normalized factors

- **Decision**: the factorization of $a \neq 0$ in a unique factorization domain with a
  normalization is the unit $u$ and the multiset `normalizedFactors a`, with $a = u \cdot \prod$.
- **Reason**: irreducible factors are unique only up to units; the normalization chooses one
  representative of each class (on $\mathbb{Z}$, $|x|$), so the multiset is a function of $a$ and
  the unit is determined. This is the form of the polynomial factorization row
  `mor.sets.polynomial_factorization` (a unit and a multiset of factors).
- **Excluded**: a multiset of irreducible factors with no normalization, which is defined only up to
  units and so is no function of $a$.

## D23 (#217): a linear map from a formula is a function with its linearity proof

- **Decision**: the row takes a function $R^n \to R^m$ given by the formula and a proof of
  `IsLinearMap`, and gives the `LinearMap`; a procedure proves linearity for a formula linear in its
  binders, and refutes it otherwise or leaves it unsettled.
- **Reason**: linearity is a property of the function, not of its written form; M5 asks for domain
  evidence, and `IsLinearMap` is that evidence. The matrix rows (`mor.modules.matrix_linear_map`)
  stay the owners of a map given by a matrix; `LinearMap.toMatrix'` relates the two.
- **Excluded**: reading a formula into a matrix by its syntax, which is a second source of meaning
  for the same map (M7).
