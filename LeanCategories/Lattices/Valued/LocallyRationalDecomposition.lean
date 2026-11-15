/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.ForMathlib.PointedConeFiniteGeneration
public import LeanCategories.ForMathlib.PointedConeMinkowskiWeyl
public import LeanCategories.ForMathlib.PointedConeAlternative
public import LeanCategories.Lattices.Valued.RationalPolyhedralCone
public import LeanCategories.Lattices.Valued.PositiveCone
public import LeanCategories.Analysis.Convex.SignCell
public import Mathlib.Analysis.Convex.Cone.Basic
public import Mathlib.Analysis.Convex.Cone.Dual
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.Topology.Algebra.Module.ModuleTopology
public import Mathlib.Topology.Connected.Clopen
public import Mathlib.Topology.LocallyFinite
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import Mathlib.LinearAlgebra.BilinearForm.Properties
public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.Algebra.Module.Torsion.Free
public import Mathlib.Algebra.Module.ZLattice.Basic
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.RingTheory.TensorProduct.Finite
public import Mathlib.Analysis.Normed.Affine.AddTorsorBases
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Order.Filter.AtTopBot.Tendsto

/-!
# Locally rational decompositions of the rational closure of a cone

Definitions 4.1 and 4.2 of E. Looijenga, *Compactifications defined by arrangements II:
locally symmetric varieties of type IV*, arXiv math/0201218v2 (2002), pp. 16-19, the support
spaces of his Lemma-Definition 4.5, p. 19, and the arrangement decomposition of Example 4.3,
over a finite-dimensional `ℚ`-vector space `L`, on the rational cones of #37
(`RationalPolyhedralCone.lean`).

The carrier is the real form `L(ℝ) = L ⊗_ℚ ℝ`. It is carried as `ℝ ⊗[ℚ] L`, canonically
the same tensor product, because that is the order in which the scalar action of `ℝ` is
available: Mathlib's `TensorProduct.leftHasSMul` acts on the left factor, so `ℝ ⊗[ℚ] L` is
an `ℝ`-vector space with no extra structure.

## What is stated

* Definition 4.1 (p. 16): rational cones, and rational cone systems.
* Definition 4.2 (p. 17): the rational closure `C₊` as the **convex hull** of
  `L(ℚ) ∩ closure C` (`rationalClosure`), with the proof that it is a cone
  (`convexHull_coneComb`) and that it is the cone that set generates
  (`rationalClosure_eq_hull`); locally rational cones; locally rational decompositions, with the
  restriction to a rational subcone a rational cone system (`restrictionTo`,
  `IsLocallyRationalDecomposition.restriction`); and the facial decomposition `Σ(bb)`.
  Of the relation of `C` to its rational closure: `C ⊆ closure C₊` for an open `C`, from the
  density of the rational points of `L(ℝ)` (`dense_range_rationalPoint`,
  `subset_closure_rationalClosure`), and `C ⊆ C₊` itself for a finite-dimensional `L`
  (`subset_rationalClosure`), which discharges the cover hypothesis `hcover` of the
  support-space theorems (`exists_mem_of_mem_of_cover_rationalClosure`).
* **The reading of "the restriction"** (the point on which this file takes a position): the
  restriction of `Σ` to a rational subcone `P` is the collection of *faces* of the traces
  `σ ⊓ P`, `σ ∈ Σ` (`faceClosure (restrictionTo Σ P)`), not the traces themselves. The two
  readings are settled by proof: with the faces of the traces `Σ(bb)` is a locally rational
  decomposition of `C₊` (`facialDecomposition_isLocallyRational`), which is what the source
  asserts of it (p. 17); with the traces themselves it is not, in the setting of Example 4.3
  (`not_isLocallyRationalDecompositionTraces_facialDecomposition`, and the section "Example 4.3"
  below for the argument), so the literal reading cannot be the one the source's uses need.
  `IsLocallyRationalDecompositionTraces` keeps the literal reading, so that the counterexample
  is a statement about a named predicate and not a remark about a discarded definition.
* **The setting of Example 4.3** (pp. 17-18), the hyperbolic one: the closed sheet
  `closedSheet` of a nondegenerate form of signature `(1, dim − 1)` at a positive vector `t`,
  which is a cone, is salient (`closedSheet_salient`), and a face of `C₊` containing a rational
  point of the open sheet is `C₊` (`eq_of_isFaceOf_of_mem_pos_closedSheet`); so `C₊` is
  nondegenerate in this setting (`salient_rationalClosure`) and `Σ(bb)` is a locally rational
  decomposition there (`hyperbolicFacialDecomposition_isLocallyRational`). The one topological
  input is carried as the hypothesis `hcl`: `Q` and `x ↦ x · t` are continuous on the
  finite-dimensional real form, so they are nonnegative at the rational points of the closure of
  the sheet, which is where the proofs use it. Mathlib at this revision has no `Continuous`
  statement for a quadratic form, and the module topology of `realified V` here carries no
  `IsTopologicalAddGroup` instance from which `FiniteDimensional` could supply `T2Space`.
* **The action of `Γ`** (Example 4.3, p. 17): a real linear equivalence of `L(ℝ)` defined over
  `ℚ` (`IsRationalEquiv`, the form an element of the arithmetic subgroup of `O(L(ℚ))` takes)
  carries rational cones to rational cones, rational cone systems to rational cone systems,
  faces to faces, and salient cones to salient cones; hence it carries a locally rational
  decomposition of `C₊` to one (`isLocallyRationalDecomposition_coneMap`), and `Σ(bb)` is fixed
  by every such element (`isGammaInvariant_facialDecomposition`, `IsGammaInvariant`).
* Lemma-Definition 4.5 (p. 19): the forms nonnegative on `τ` and zero on `σ`, their common zero
  set, the two inclusions `span σ ≤ L_σ ≤ span τ` that pin the support space between the span
  of `σ` and the span of the cone above it, and `L_σ = span σ` for the cones that meet `C`.
* **The isotropic case of Lemma-Definition 4.5** (the proof at p. 19): `σ` spanning an isotropic
  half line (`IsIsotropicHalfLine`), the functional `β` induced on `L(ℝ)/I` by an isotropic
  generator (`isotropicHalfspaceForm`), and the source's first observation there — that `π_I`
  carries the open cone `C` *onto* the open half-space `{u | 0 < β u}` bounded by
  `(I^⊥/I)(ℝ)` (`image_mkQ_upper_eq`), together with the inclusion of `π_I(C₊)` in the closed
  half-space (`image_mkQ_rationalClosure_subset`). The step it rests on is that a timelike point
  of the open sheet pairs positively with every nonzero point of the closed sheet
  (`associated_pos_of_mem_upper_of_mem_closedSheet`). What the source then does with the
  half-space — the cones of `Σ` above `σ` projecting to polyhedra, their minimal members, and
  the translation space `U` with `L_σ` its preimage — is carried in algebraic form in the section
  "Lemma-Definition 4.5, the general case" below, whose docstring says which of its steps are
  carried and which are not; of the description of `L_σ` itself the upper bound `L_σ ⊆ I^⊥` is
  carried in the section "The two descriptions of `L_σ`"
  (`sigmaSupportSpace_le_ker_associated_of_isotropic`), and the reverse inclusion, which is what
  the affine model over `A_I(ℝ)` supplies, is not.
* **Lemma-Definition 4.5 for every locally rational `Σ`** (p. 19, the proof at line 521): the
  support space of `σ` is the same for every member `τ ≥ σ` meeting `C`. Proved in three steps:
  the face step (`supportSpace_eq_of_face`), which turns the source's "translation space of the
  adjacent members" into an algebraic domination hypothesis on the forms and is unconditional for
  finitely generated cones (`supportSpace_eq_of_common_face_of_fg`); **the connectivity of `Σ`
  through common faces**, which is the step from adjacent members to all members and is what
  `reflTransGen_inf_nonempty_of_convex` supplies — the members meeting `C` are joined by a chain
  in which consecutive members meet in a point of `C`, from the local finiteness of `Σ` and the
  convexity of `C`; and with those, `supportSpace_eq_of_locallyFinite` and
  `sigmaSupportSpace_eq_supportSpace_of_locallyFinite`. What that leaves as a hypothesis is the
  cutting form at each pair of members meeting `C` — the incidence datum `Dominates`, free on the
  domination side for polyhedral members (`dominates_of_fg`).

## Example 4.3 (b): the cells of `Σ(H)` are rational cones, and `Σ(H)` is a locally rational
decomposition

* The one step of Fourier–Motzkin elimination that the cells need, in the form the repository
  already has it: cutting a cone by a linear halfspace keeps the generators explicit
  (`Finset.halfspaceGenerators`, `Finset.hull_halfspaceGenerators`, ported from TauCeti in
  `ForMathlib/PointedConeFiniteGeneration.lean` and *used* here, not re-derived). What is added
  is the rationality: when the cutting form is the extension of a `ℚ`-linear form, the generators
  of the cut are the images of finitely many points of `L(ℚ)`
  (`image_sliceGens_eq_halfspaceGenerators`), so the cut of a rational cone is a rational cone
  (`isRationalCone_inf_halfspace`).
* With that, a cell of `Σ(H)` — a rational cone cut by finitely many rational sign conditions —
  is a rational cone (`isRationalCone_arrangementCone_inf`); a cell is a face of a cell whose
  sign pattern refines it (`isFaceOf_arrangementCone_commonSignPattern`); and `Σ(H)` is a locally
  rational decomposition of `C₊` (`arrangementDecomposition_isLocallyRational`), from the
  hypothesis `CutsFinitelyOnRational` below. That is item (b) of Example 4.3, pp. 17-18.
* **The hypothesis, restated: `CutsFinitelyOnRational`.** A `ℚ`-hyperplane *meets* a cone, in the
  sense of Example 4.3 (b) (p. 18; text version `.tmp-sources/looijenga-math0201218v2.md:487`),
  when it cuts it: the form defining it takes both signs on the cone (`CutsOn`). The hypothesis is
  that only finitely many of the forms cut any given rational **subcone of `C₊`** — the quantifier
  of Definition 4.2, p. 17 ("the restriction to every rational subcone of `C₊` is a rational cone
  system"), which is where a locally rational decomposition is used. It is not a quantifier over the
  rational cones outside `C₊`: those are cut by every normal of a given negative value, so the
  statement is false there even for the arithmetic `H` of Example 4.3 (b) (the definition's own
  docstring carries an integral isometry of infinite order whose orbit witnesses it), and `Σ(H)`
  decomposes none of them. The reading this replaces said
  instead that all but finitely many of the forms **vanish** on every rational cone, which no
  infinite `H` has in the setting of Example 4.3 — an open piece of `C` lies in a rational cone,
  and a form that meets `C` vanishes on no open set — so that version of the theorem was vacuous
  there. The two readings differ exactly on the forms that are one-signed on the cone, and for
  those the sign condition of a cell is a face condition of the cone
  (`isFaceOf_inf_reducePattern`): that is what makes the corrected statement provable, and it is
  why the finiteness of the traces now runs through the faces of the cells of the *finitely many*
  forms that cut (`range_reducePattern_finite`, `finite_faces_of_isRationalCone`) instead of
  through a finite set of nonvanishing forms.
* **The hypothesis for the `H` of Example 4.3 (b) (#161), carried.** Definition 4.2's restriction
  clause asks for a *finite* family — a rational cone system, Definition 4.1, p. 16 — on every
  rational subcone, and `arrangementDecomposition_isLocallyRational` proves it only from
  `CutsFinitelyOnRational`. The source asserts it of the arithmetic `H`;
  `cutsFinitelyOnRational_orbitFamily` (the last section of this file) derives it, from the two
  steps below and the two cone-side hypotheses of the hyperbolic setting. What is *not* formalized
  is the arithmeticity of `Γ` itself — the finite-index subgroup of `O(L(ℚ))` preserving a lattice
  on which the form is integral: the lattice `Λ`, the integrality of the form on it and the
  `Γ`-stability of `Λ` are hypotheses of the theorem, and `Λ` is taken as the `ℤ`-span of a
  `ℚ`-basis (every lattice that spans `L` over `ℚ` has such a basis, and its `ℤ`-basis is one; the
  normal form avoids a local `Fintype` instance inside a proposition, which the repository's
  `haveILetI` linter refuses).

  (i) *Finitely many norms.* `Γ` arithmetic means that a finite-index subgroup preserves a lattice
  `Λ ⊆ L(ℚ)` on which the form is integral. A `ℚ`-hyperplane that meets `C` has a spacelike normal:
  its hyperplane contains a timelike vector `x`, and `0 > ℓ²` then follows from `sigPos Q = 1` and
  nondegeneracy alone — `neg_quadratic_of_associated_eq_zero` below, general in `ℓ` and `x` rather
  than stated for a cone (`ℓ² > 0` is excluded because `(ℓ, x)` would be a positive definite plane,
  `ℓ² = 0` because `eq_zero_of_perp_of_quadratic_eq_zero` then makes `ℓ` vanish). The primitive
  normal of a `ℚ`-line in `Λ` is unique up to sign, so its value `ℓ²` is constant on a `Γ`-orbit;
  a finite union of orbits therefore has its primitive normals taking finitely many *negative*
  values. This is `finite_form_values_of_orbitFamily` below.

  (ii) *The counting lemma.* For a rational cone `P ≤ C₊` and a negative integer `-m`, only finitely
  many primitive `ℓ ∈ Λ` with `ℓ² = -m` cut `P`. This is linear algebra over `ℚ` with integrality —
  no reduction theory and no proper discontinuity — and the section "The counting lemma over `ℚ`" at
  the end of this file carries its two foundations. `cutsOn_iff_generators`: for
  `P = hull (rationalPoint '' s)` and a form that is the extension of a `ℚ`-linear `q`, the form
  cuts `P` exactly when `q` takes both signs on `s`, so `L(ℝ)` leaves the statement.
  `finite_span_int_of_pairings_bounded`: on the `ℤ`-span of a `ℚ`-basis a vector's coordinate
  against `b j` is its pairing with the dual vector `B.dualBasis hB b j` (Mathlib's
  `LinearMap.BilinForm.dualBasis`), so bounded pairings leave finitely many lattice points —
  finiteness from integrality, where `ZSpan.setFinite_inter` would
  need a `ProperSpace` instance that `realified V` has not.

  What bounds the pairings is not analysis on `L(ℝ)` either, and it is now carried: with
  `sigPos Q = 1`, `pairing_quadratic_bound` gives the quadratic relation among the two pairings
  `x = ℓ · a` and `y = ℓ · b` of a pair of generators of `C₊`,
  `Q b · x² - 2 (a · b) x y + Q a · y² ≤ m (a · b² - Q a · Q b)`, from `Q u ≥ -m` at the component
  `u` of `ℓ` in the plane of the pair — that plane is hyperbolic, its orthogonal complement is
  negative semidefinite by `mul_self_le_associated_sq` alone
  (`quadratic_nonpos_of_associated_eq_zero`) — and the three cases of the case analysis are
  `abs_associated_le_of_both_timelike` (both timelike: both pairings bounded by the Gram data of the
  pair), `abs_associated_le_of_isotropic` (one isotropic: the pairing with the isotropic generator
  bounded by `a · b · sqrt (m / Q a)`, and the *product* of the two pairings bounded — the hyperbola
  that over `ℝ` is no box, `ℓ = (N, N + 1/N, 0)` keeping the norm and cutting for every `N`), and
  `abs_associated_mul_le_of_both_isotropic` (both isotropic: the product only). Integrality supplies
  what the product cannot: the pairing of `ℓ` with a generator is a nonzero rational of bounded
  denominator, hence bounded away from `0`, and `abs_le_of_abs_mul_le_of_one_div_le` turns the
  product bound into a bound on the other pairing.

  The assembly is carried too, in the section "The counting lemma over `ℚ`": from the pair bound,
  `abs_associated_le_of_pairing_bound` bounds *every* pairing of `ℓ` — projecting off the line
  `ℝ (a + b)`, whose pairing with `ℓ` is the sum of the two, and applying the reverse
  Cauchy–Schwarz inequality on its orthogonal complement (`associated_spatialPart_sq_le`) — and
  `finite_cutting_of_pairing_bounds` turns bounds on the pairings with Mathlib's dual basis into
  finiteness by `finite_span_int_of_pairings_bounded`. The denominators that the isotropic case
  needs are `one_div_le_abs_of_integral`, and `finite_cutters_of_pair_bounds` unions over the
  finitely many ordered pairs of generators, which is the cutting condition
  (`cutsOn_iff_generators`). Discharged as corollaries: the pair of timelike generators
  (`finite_cutting_normals_of_both_timelike`), the timelike-isotropic one
  (`finite_cutting_normals_of_isotropic`) and the both-isotropic one
  (`finite_cutting_normals_of_both_isotropic`: the product bound of
  `abs_associated_mul_le_of_both_isotropic`, with *both* denominators). The transport of the cut of
  a hyperplane to the cut of the form of its normal is a section of its own
  (`hyperplaneCuts_iff_cutsOn`, `hyperplaneCuts_iff_generators`).

  The assembly for the corrected `H` (the orbit family of the last section, not a finite family) is
  carried there over these pieces, and it is where the two steps meet: the pair of generators on
  which a normal of value `-m` takes both signs has positive pairing on the sheet, and a pair with
  vanishing pairing is proportional (`exists_smul_of_associated_eq_zero_of_mem_closedSheet`) and
  contributes no normal at all (`finite_pairSet_of_smul`) — which is what makes the disjunction over
  the ordered pairs of generators a cover of the cutters. `CutsFinitelyOnRational` is therefore no
  longer a hypothesis for the `H` of Example 4.3 (b); it remains the hypothesis of the general
  arrangement section, whose `H` the caller supplies. The source's own ground for it
  ("this collection is locally finite on `C`", p. 18) does not supply it either: local finiteness on
  `C` is a statement about compact pieces of the open cone, while cutting is a statement about the
  sign pattern of a form on a whole rational cone, and a locally finite family can have infinitely
  many members cutting one rational cone. The family `(x, y) ↦ x - (n+1)y`, `n ∈ ℕ`, on the
  quadrant of the plane with the form `x·y` of signature `(1,1)` is such a family: every one of
  its hyperplanes meets the open cone, all of them cut the quadrant, and the cells of the pattern
  "`pos` up to `n`, `neg` above `n`" are the distinct wedges
  `{(x, y) | 0 ≤ y, (n+1)y ≤ x ≤ (n+2)y}` (the point `(2n+3, 2)` lies in the `n`-th and in no
  earlier one), so the restriction of `Σ(H)` to that rational cone is infinite. That is a check by
  hand: this file states and proves nothing about that family. It is not a finite union of
  `Γ`-orbits for an arithmetic `Γ`, and the point of (i)-(ii) is that arithmeticity excludes it — by
  bounding the *norm*, which is what the family's `x - (n+1)y` vary. Setting 4.4 (p. 18; text
  version line 495) supplies the properness of the `Γ`-action on `C` and says nothing about sign
  patterns on
  rational cones; the classical statement behind it — that an arithmetic subgroup of `O(L)(ℚ)` acts
  properly discontinuously on the hyperbolic space `C`, hence with locally finite orbits of
  hyperplanes — is A. Borel and Harish-Chandra, *Arithmetic subgroups of algebraic groups*, Ann. of
  Math. 75 (1962), 485-535, and Looijenga states the instance he uses at Setting 4.4 (p. 18) and,
  for the Baily-Borel domain, at §1 (text version line 183: "Γ′ acts properly discretely on `D`").

## Lemma-Definition 4.5: the independence of `L_σ` from `τ`

* The source says the assertion is clear unless `σ` spans an isotropic half line, and for the
  facial decomposition `Σ(bb)` that is the whole of it: a member `τ` of `Σ(bb)` meeting `C` is
  `C₊` itself, for an *arbitrary* point of `C` (`eq_of_isFaceOf_of_meets_open_sheet`), so the
  space does not depend on `τ` (`supportSpace_eq_of_meets_openSheet`).
* The step the rational case (`eq_of_isFaceOf_of_mem_pos_closedSheet`) does not cover: a
  nonnegative combination of rational points of the closed sheet that is timelike has a
  sub-combination that is timelike (`exists_pos_pair_sum`), cut off one term at a time with the
  two-term quadratic expansion. A face containing that sub-combination contains a rational point
  of the open sheet, and the rational case applies.
* Carried of the isotropic case: its first step, in the section "Lemma-Definition 4.5, the
  isotropic case" — the projection `π_I : L → L/I` of an isotropic line, and the theorem that it
  carries the open cone onto the open half-space `{u | 0 < β u}` of the quotient
  (`image_mkQ_upper_eq`). The half-space is the affine space `A_I(ℝ)` of the source's proof
  ("we prefer to think of this image as a cone over a real affine space", p. 19).
* Carried of the rest of that proof, in the section "Lemma-Definition 4.5, the general case": the
  independence from `τ` itself, as the face step `supportSpace_eq_of_face` plus the independence
  `supportSpace_eq_of_common_face`, for a general `Σ` and a general `σ`; the domination hypothesis
  of the face step is named, and discharged for finitely generated cones
  (`exists_add_smul_of_fg`, `supportSpace_eq_of_face_of_fg`,
  `supportSpace_eq_of_common_face_of_fg`). With it, `sigmaSupportSpace_eq_supportSpace` states
  the `Σ`-support space of Lemma-Definition 4.5 as the value at any one member.
* **The step from adjacent members to all members is carried**, in the section "The connectivity of
  a locally finite decomposition through common faces": any two members of a locally finite
  decomposition that meet a convex cone `C` are joined by a chain of members in which consecutive
  members meet in a point of `C` (`reflTransGen_inf_nonempty_of_convex`), and along such a chain
  the support space over `σ` does not change (`supportSpace_eq_of_reflTransGen`,
  `supportSpace_eq_of_locallyFinite`). That is what the source's proof summarises as its
  induction over the affine decomposition (`{z | (1, z) ∈ π_I τ}`, the polyhedra of `A_I(ℝ)`, a
  minimal member and its translation space `U`), and what it means by "these assertions are
  clear" for `σ` not an isotropic half line; the argument carried is the one in the form and in
  the cone, with neither the projection `π_I` nor the affine model.
* Carried, as a hypothesis and not as a theorem: that the common face `τ ⊓ τ'` of two members
  meeting `C` is cut out of each by a form nonnegative on it and zero on `σ`, with domination
  (`Dominates`). For a polyhedral member the domination half is free (`dominates_of_fg`); the
  exposure half is the part of the source's affine argument that this section does not reconstruct,
  and for the cells of `Σ(H)` of Example 4.3 (b) it is the form of the sign condition that
  separates the two cells. Also a hypothesis: that the members cover `C`, not only `C₊`.
* **Two descriptions of `L_σ` are carried instead, in the section "The two descriptions of `L_σ`"**,
  and neither of them goes through the cutting forms: for `σ` whose span is the kernel of a form
  nonnegative on the member (`supportSpace_eq_span_of_ker_eq`) the support space is `⟨σ⟩`, and
  with that hypothesis at every member above `σ` the `Σ`-support space is `⟨σ⟩`
  (`sigmaSupportSpace_eq_span_of_forall_ker_eq`) — the independence from `τ` with no `hexp` at
  all, which is the source's "clear" case for `σ` not an isotropic half line. In the isotropic
  case the first projection of the source's proof is carried as `L_σ ⊆ I^⊥`
  (`supportSpace_le_ker_associated_of_isotropic`,
  `sigmaSupportSpace_le_ker_associated_of_isotropic`), which together with
  `supportSpace_le_span` is the source's description as an upper bound, and for the facial
  decomposition both inclusions are carried (`supportSpace_closedSheet_hull_eq_ker`, the section
  "The support space of an isotropic half line in the facial decomposition"). What the affine
  model adds for a general `Σ` — the reverse inclusion `I^⊥ ∩ ⋂_{τ > σ} ⟨τ⟩ ⊆ L_σ` — is not
  carried; see "What is not carried".
* A check by hand of the shape, in a basis `e, f, w₁, w₂` of signature `(1, 3)` with `e · f = 1`
  and `w_i · w_i = -1`: for the single `ℚ`-hyperplane `{z₁ = 0}` through `σ = ℝ≥0 e`, the members
  above `σ` meeting `C` are the two cells and `C₊ ∩ H`, their polyhedra are the two half-spaces
  `±z₁ ≥ 0` and the hyperplane between them, all three have translation space `{z₁ = 0}`, and all
  three support spaces are `span(e, w₂) = I^⊥ ∩ H`, which is the value the source's description
  gives. The minimal members of the whole decomposition, the isotropic rays, do not meet `C`. The
  chain of the two cells runs through `C₊ ∩ H`, which is the connectivity the section above
  proves in general; the three support spaces are not proved to agree in Lean from that chain
  alone, since the forms cutting `C₊ ∩ H` out of the round cone are not supplied.
* Also not carried: the identification of the support spaces of `Σ(bb)` as `V`, `{0}` and the
  hyperplanes orthogonal to the `ℚ`-isotropic lines (p. 19). What is proved here is the
  independence, not that description.

## The arrangement cells are a port

The cells of `Σ(H)` are the weak sign cells of the family of linear forms, and that machine is
not written out here: it is the port of TauCeti's `Analysis/Convex/Polyhedron/SignCell/Basic.lean`
and `Interior.lean` (from Mei at `a79c5717`, Apache 2.0) in
`LeanCategories/Analysis/Convex/SignCell.lean`, with its provenance and the two files' own
statement of what was left out. The last section of this file is the glue.

## LC-09 search record (2026-11-15, extended for the port and the Example 4.3 argument)

Formalization-corpus queries, with the hits that decided the shape of the file and of the port.
`content:PointedCone convexHull rational`: no file. `content:locally finite hyperplane
arrangement`: TauCeti `Analysis/Convex/SimplicialComplex/Arrangement.lean` and
`Analysis/Convex/Polyhedron/SignCell/{Basic,Interior,Rational}.lean` (the sign-cell machine of an
affine arrangement, adapted there from Mei `Geometry/Convex/Polyhedron/SignCell.lean`, commit
`a79c57178cc83666fc244ca6e6eeaa722e9b8bc7`, Apache 2.0): ported, see above.
`content:weakSignCellCone`: TauCeti `Polyhedron/SignCell/Basic.lean` — `weakSignCell`,
`weakSignCellCone`, `closure_signCell`, `weakSignCell_inter`, `commonSignPattern`,
`realizedSignCellClosures`, `mem_weakSignCell_iff_specializes` (latest `main`; the files named in
the earlier record at `SignCell/` are at `TauCeti/Analysis/Convex/Polyhedron/SignCell/`).
`content:signCell intrinsicInterior closure`: TauCeti `SignCell/Interior.lean` and
`Analysis/Convex/Intrinsic.lean` (`eq_zero_of_nonneg_of_mem_intrinsicInterior`): ported.
`content:sign cell hyperplane`: LeanPool `NandakumarRamanaRao/NRR/PowerDiagram/CellOverlap.lean`,
unrelated (power diagrams). `content:rational closure cone` and `content:IsFaceOf`: TauCeti
`Geometry/Toric/Algebraic/Cone/{Inf,Slice}.lean` (rational cones and faces, already ported in
`RationalPolyhedralCone.lean`). `content:semifan`, `content:toroidal compactification cone` and
`content:Fan support rational polyhedral`: no file — Looijenga's semifans (his Definition 6.1, the
next unit) are not formalized anywhere in the corpus. `content:Lorentz cone` and
`content:Baily-Borel`: no relevant hit (one quantum-logical-framework `lakefile.lean`, one
unrelated Shimura-curve file). `content:totally isotropic subspace signature bound` and
`content:cone cut by rational inequalities generated by rational points`: no file — the
extension-of-scalars statement that the last section's gap names is not formalized in the corpus.

Extended search for that statement (the reduction Example 4.3 (b) needs), run under several
formulations with the Mathlib-style identifiers among them: `content:rational inequalities real
hull rational points` → ShouqiaoW/erdos `1038/lean/Erdos1038/RationalInterval.lean`, a
kernel-checked rational interval evaluator, unrelated; `content:extension of scalars cone
rational points dense` → one hit, `mathlib4/Mathlib.lean`, the import list, no file;
`content:isRationalCone hull of rational points` → no file; `content:polyhedral cone defined
over Q real cone generated by rational points` → one hit, CakeML `candle`, unrelated;
`content:solution set rational linear inequalities convex hull rational points` → cut by the
client's time limit with no result. On the Mathlib side (`Mathlib/Geometry/Convex/`,
searched on disk) there is no `PointedCone.IsRational` or `ConvexCone.IsRational`, so the
statement is not in Mathlib under those names either. Nothing to port; it is to be proved
here.

### LC-09 record for the independence of `L_σ` (this unit)

The formulations the unit names for the general case of Lemma-Definition 4.5, run against the
corpus API with the Mathlib-style identifiers among them, with every hit read:

`content:Submodule.mkQ`: 398 files, 1095 matches; the returned hits are quotient maps of Lie
ideals and of subgroups — atlas `MathlibExt/Algebra/Lie/Ado.lean`, TauCeti
`Algebra/Lie/Quotient.lean` (`coe_mkQ`), `Algebra/Lie/Coadjoint.lean`, `RingTheory/Length.lean`,
LeanPool `PFR/WeakPFR.lean` — and none is about the quotient of a vector space by an isotropic
line. `content:Polyhedron`: 136 files, 773 matches; TauCeti `Analysis/Convex/Polyhedron/Basic.lean`
(`IsConvexPolyhedron`), `Polyhedron/Homogenization.lean`, `Topology/PL/Map.lean`
(`IsPiecewiseAffineOn`) — polyhedra as sets and the cone of a polyhedron's inequality rows, with
nothing on the support space of a member of a decomposition. `content:affine translation space`:
189 files, 11319 matches; the one file returned is atlas `WantedExt/Geometry/SpaceGroupsWanted.lean`
(the 230 space groups), unrelated. `content:quotient by isotropic`: 35 files, 4223 matches; TauCeti
`Geometry/Contact/Isotropic.lean`, isotropic *maps* into a contact manifold, not a quotient.
`content:recession cone`: 8 files, 211 matches; TauCeti `Topology/PL/Cone.lean`, coning of
piecewise-affine maps. `content:polar dual cone face cone`: 19 files, 2179 matches; LeanPool
`Malliavin/ClarkOcone.lean`, unrelated. `content:PointedCone.dual`: 12 files, 39 matches; TauCeti
`Analysis/Convex/Homogenization.lean` (`homogeneousInequalityCone`, the dual cone of the inequality
rows of a polyhedron) and atlas `MathlibExt/Analysis/InnerProductSpace/PolarSet.lean` (the inner
dual cone and `Submodule.dualAnnihilator`, a survey of the three duals) — the cone API, not the
face step. `content:support space of a cone`: 82 files, 371507 matches, too broad to be a signal;
the returned file is qinz1yang `Geometry/Metric/ConeRadius.lean`, the radius of a metric cone.
`content:isotropic halfspace projection`: 1 file, 17 matches; CBirkbeck `LeanBridge`
`Siegel/KlingenEisenstein.lean`, unrelated. `content:exposed face of a cone`: 21 files; qinz1yang
`DifferentialGeometry/Analysis/Convex/ProperConeFace.lean`, faces of proper cones stated over
Mathlib's `Mathlib.Analysis.Convex.Exposed` — the nearest thing in the corpus to the exposure
hypothesis, and not about support spaces.

Nothing to port: the independence below is linear algebra over the dual cone, and every cone
statement it uses is already in Mathlib (`PointedCone.dual (Module.Dual.eval ℝ ·)`,
`PointedCone.ofSubmodule`, `PointedCone.hull_le_span`, `Submodule.span_le`) or is the repository's
own ported `halfspaceCone` (`ForMathlib/PointedConeMinkowskiWeyl.lean`). Nothing in Mathlib either,
under the names searched on disk (`PointedCone.IsFaceOf` has no support-space or face-duality
statement; `Mathlib/Analysis/Convex/Cone/Dual.lean` is `ProperCone.dual` and its double dual).

### LC-09 record for the connectivity of a decomposition (2026-11-17)

The formulations the unit names for the step from adjacent members to all members, run against
the corpus API with every hit read:

`content:PolyhedralComplex`: TauCeti `Geometry/Convex/PolyhedralComplex/{Basic,Map,
CommonRefinement,Subcomplex,MinimalCell}.lean`, a `FinitePolyhedralComplex` on a real vector space
with `IsExposed` faces and `MinimalCell` — a finite complex of *polyhedra* in an ambient space,
where the connectivity here is about a locally finite family of cones covering a convex set and is
used only through closedness. Not imported: its `MinimalCell` API is the unique-cell-through-a-point
statement, not the chain along a segment, and its members are assumed polyhedral, which is the
hypothesis this unit deliberately does not make. `content:Polyhedron face`: TauCeti
`Analysis/Convex/Polyhedron/{Basic,Homogenization,Rational}.lean`, the cone of the inequality
rows of a polyhedron — the `halfspaceCone` of
`ForMathlib/PointedConeFiniteGeneration.lean`, already ported and used.
`content:connected codimension one`: TauCeti `Order/Catenary.lean`
(`IsCatenary.exists_covBy_series_of_lt`: in a catenary preorder any two comparable elements
are joined by a saturated chain) — a chain through covers in an order, which is the shape of the
conclusion and not its proof; the order here is not catenary and the chain is supplied by
connectedness. `content:locally finite cover convex`: TauCeti `Analysis/Convex/Lipschitz.lean`
("a common Lipschitz bound on the members of a finite closed cover of a convex set holds on the
whole set"), which runs a *continuous induction along a segment* across a finite closed cover —
the nearest thing in the corpus to the argument below, and not portable: its conclusion is a
Lipschitz estimate and its induction is over a metric. `content:finite closed cover preconnected`
and `content:preconnected iUnion closed`: no hit about a chain of members of a cover.
`content:common face adjacent cell`: mccorvie `Schoenflies/MoiseBandCells.lean`, cells of a Moise
band, unrelated. `content:translation space polyhedron`: TauCeti
`Analysis/Convex/Polyhedron/Rational/Map.lean`, integral affine transport of rational-normal
polyhedra, unrelated.

Nothing to port. The argument carried is the clopen one:
`isPreconnected_iff_subset_of_disjoint_closed` (`Mathlib/Topology/Connected/Clopen.lean:300`),
`Set.Finite.isClosed_biUnion` (`Mathlib/Topology/Basic.lean:185`) and
`LocallyFinite.finite_nonempty_inter_compact`
(`Mathlib/Topology/Compactness/LocallyFinite.lean:30`), all in Mathlib and used as they are.

### LC-09 record for the density of `L(ℚ)` in `L(ℝ)` (2026-11-17)

`content:rational points dense base change` and `content:convex hull dense interior`: no file
about the density of the rational points of a base change. Mathlib has the three ingredients and
nothing assembled: `Rat.denseRange_cast` (density of `ℚ` in `ℝ`),
`image_closure_subset_closure_image`
(a continuous image of a closure lands in the closure of the image) and `Set.MapsTo.closure` (a map
that carries `s` into a closed set carries `closure s` into it). Nothing to port: the proof of
`dense_range_rationalPoint` is those three, plus `TensorProduct.inductionOn`.
`content:IsExposed face polyhedral` and `content:PointedCone face exposed` belong to the exposure
question of the pair of members, not to this one; their hits are recorded in the section
"Lemma-Definition 4.5, the general case" as the nearest thing the corpus has to the cutting form.

### LC-09 record for `C ⊆ C₊` and the two descriptions of `L_σ` (2026-11-18)

The formulations of this unit, run against the corpus API, with every returned file read:

`content:convex set interior closure equal`: 60 files, all of them about closures of convex sets in
general; the one file returned is TauCeti `Topology/ClusterSet.lean`, cluster sets of a map, no
`interior (closure s) = interior s`. `content:interior_closure_eq_interior`: 8 files, 12 matches —
TauCeti `Analysis/Convex/Topology.lean`, a mirror of Mathlib's `Analysis/Convex/Topology.lean` in
which `Convex.interior_closure_eq_interior_of_nonempty_interior` appears under the same name, and
TauCeti `Analysis/Convex/Cone/StrictInward.lean`, which applies it. Nothing to port: the lemma is
Mathlib's and is used here directly. `content:affineSpan_eq_top_of_nonempty_interior`: 10 matches —
LeanPool `Polytopes/Halfspace.lean` and atlas `Geometry/Euclidean/Viviani.lean`, both applying the
same Mathlib lemma to a half-space and to a triangle. `content:rational points dense convex hull`:
9 files, the one returned being TauCeti `Geometry/Convex/PolyhedralCochain/Pairing.lean` (affine
test simplices in a polyhedral cochain complex), nothing about a convex hull of rational points
being dense in an open convex set — no file formalizes `C ⊆ C₊`, and the two Mathlib lemmas above
plus `IsOpen.affineSpan_eq_top` and `interior_maximal` are the whole proof. `content:continuous
linear map finite dimensional moduleTopology`: 7 files, the one returned ImperialCollegeLondon
`FLT/NumberField/AdeleRing.lean`; the statement used is Mathlib's
`IsModuleTopology.continuous_of_linearMap`, which the repository's own module-topology section
already uses, and `Module.finBasis` supplies the basis.

For the two descriptions: `content:self dual cone Lorentz`: 5 files, the one returned leanprover
`Physlib.lean`'s import list — Physlib's order-unit cones are not the light cone and carry no
self-duality statement for a quadratic form of signature `(1, n − 1)`. The self-duality used in
`supportSpace_le_ker_associated_of_isotropic` is the repository's own
`nonneg_associated_of_quadratic_eq_zero_of_mem_closedSheet`, not a corpus import.
`content:isExposed face cone`: 2 files, the one returned qinz1yang
`Analysis/Convex/ProperConeFace.lean` (`ProperCone.IsDualElement`), the same file the earlier record
names as the corpus's nearest neighbour to the exposure question; nothing about a support space
being the span of a cone whose span is the kernel of a nonnegative form. Nothing to port for either
description: both are linear algebra over `supportForms` and `PointedCone.hull_le_span`.

For the facial case of the isotropic description
(`supportSpace_closedSheet_hull_eq_ker`) the two searches that matter are the self-duality one
above — no hit, the statement is proved from the repository's own
`quadratic_spatialPart_nonpos`, `mul_self_le_associated_sq` and
`eq_zero_of_perp_of_quadratic_eq_zero` — and `content:support space of a cone` (recorded above,
82 files, too broad to be a signal). The general proportional statement
`exists_smul_of_associated_eq_zero_of_mem_closedSheet_self` is the file's own rational
`exists_smul_of_associated_eq_zero_of_mem_closedSheet` with the rationality dropped; nothing to
port. Mathlib's `LinearMap.BilinForm.toDual` (`LinearAlgebra/BilinearForm/Properties.lean:351`) is
what turns an arbitrary functional into a vector of the sheet, used as it is.

### LC-09 record for discreteness and properness (2026-11-16)

The five queries the unit names for the discreteness of an arithmetic subgroup and the properness
of its action on hyperbolic space, run against the corpus API, with every hit listed.
`content:IsDiscrete orthogonalGroup`: no file (0 files, 0 matches) — no discreteness statement for
an orthogonal group anywhere in the corpus. `content:ProperlyDiscontinuous`: 143 files, 344
matches; the relevant ones are Mathlib's `ProperlyDiscontinuousSMul` API
(`Topology/Algebra/ConstMulAction.lean`, and
`Mathlib/NumberTheory/ModularForms/ProperlyDiscontinuous.lean` for the action of `SL(2,ℤ)` on the
upper half plane) and qinz1yang/differential-geometry
`DifferentialGeometry/Topology/Manifold/Quotient.lean` and `Geometry/Thurston/Descent.lean`
(`properlyDiscontinuousSMul_of_affine`: an affine action with a discrete translation group is
properly discontinuous, and the quotient is a covering map). Those are actions of a group on a
space *given* as properly discontinuous; none of them derives properness from discreteness in an
isometry group. `content:properlyDiscontinuousSMul`: the same API — the consequences for the
quotient (local diffeomorphism, covering map), nothing on `O(L)`. `content:arithmetic subgroup
discrete`: one hit, TauCeti `Topology/MetricSpace/DiscreteAddSubgroup.lean` —
`AddSubgroup.finite_inter`, a discrete additive subgroup of a proper metric group meets a bounded
set in a finite set, proved from Mathlib's `Metric.finite_isBounded_inter_isClosed`
(`Mathlib/Topology/MetricSpace/Bounded.lean:627`). That is the *second* half of the local
finiteness argument (bounded and discrete implies finite), not the discreteness of an arithmetic
subgroup; since the substance is Mathlib's own lemma, nothing is ported for it.
`content:Lorentz hyperbolic space proper`: 7 files, 551 matches, all of them qinz1yang's
hyperbolic-geometry development (cusps, universal covers, covering spaces) — no statement that an
arithmetic subgroup of `O(L)` acts properly on the positive cone.

Nothing to port for either discreteness or properness. The Mathlib material the argument would
use, should it be carried out, is: `Metric.finite_isBounded_inter_isClosed` together with
`ZSpan.setFinite_inter` (`Mathlib/Algebra/Module/ZLattice/Basic.lean:328`: the `ℤ`-span of a basis
meets a bounded set in a finite set) for the discreteness half, and for the properness half the
boundedness of `{v | v · v = c, v ⊥ p}` for a fixed timelike `p`, which is the definiteness of the
form on `p^⊥` and is not in the corpus. Note that what these give is local finiteness on `C`, not
the hypothesis of the theorem below (`CutsFinitelyOnRational`); see the section on Example 4.3 (b)
above for why local finiteness on `C` does not give it.

### LC-09 record for the counting lemma and the spacelike normal (2026-11-15, #161)

The queries this unit names, with every hit. `content:Finite lattice bounded norm`: 163 files,
one returned — LionSR `TNLean/Lattice/FiniteDomain.lean`, finite domains of the square lattice
(a graph-diameter development), unrelated. `content:ZLattice finite ball`: 43 files, one returned,
`mathlib4/Mathlib.lean`, the import list, no file. `content:Set.Finite norm le`: 153 files, one
returned — TauCeti `RingTheory/Length/Norm.lean`, the order of a field norm, unrelated.
`content:ZLattice`: 124 files, one returned — CBirkbeck/LeanBridge's import list, whose
`ForMathlib/Algebra/Module/ZLattice/` directory is the live development. `content:ZLattice finite`
and `file:MinimalVectors content:Finite`: two files, and the one statement there that the counting
lemma needs is LeanBridge `ZLattice/MinimalVectors.lean`'s
`finite_inter_closedBall (r : ℝ) : (Metric.closedBall 0 r ∩ (L : Set E)).Finite`, a two-line
corollary of Mathlib's `Metric.finite_isBounded_inter_isClosed`
(`Mathlib/Topology/MetricSpace/Bounded.lean:627`); its substance is Mathlib's own lemma, so nothing
is ported for it — the same ground on which the discreteness half of the local-finiteness argument
was left to Mathlib in the record above. `content:lattice vectors bounded norm finite`: 58 files,
one returned — QudeLeap `QuantumAlg/Util/FiniteCyclicDLP.lean`, discrete logarithms, unrelated. On
the Mathlib side the finiteness step is `ZSpan.setFinite_inter`
(`Mathlib/Algebra/Module/ZLattice/Basic.lean:328`, the `ℤ`-span of a real basis meets a bounded set
in a finite set), which is the lemma named in (ii) above; nothing to port.

For the spacelike-normal step (i) the repository's own signature facts are the ones used, and
nothing new was needed: `mul_self_le_associated_sq` (`PositiveCone.lean`, the key inequality of
signature `(1, n)`) and `eq_zero_of_perp_of_quadratic_eq_zero` (above) give
`neg_quadratic_of_associated_eq_zero`, and `sigPos_isotropicQuotientForm` /
`sigNeg_isotropicQuotientForm` (`IsotropicQuotientSignature.lean:513`, `:520`, the `e^⊥/e`
signature on main) carry the negative definiteness of `w^⊥/w` that (ii) quotes.

### LC-09 record for integrality over `ℚ` (2026-11-15, #161, second unit)

The four queries this unit names, with every hit. `content:ZLattice`: 124 files, one returned —
CBirkbeck/LeanBridge's import list, whose `ForMathlib/Algebra/Module/ZLattice/MinimalVectors.lean`
has `finite_inter_closedBall`, a two-line corollary of Mathlib's
`Metric.finite_isBounded_inter_isClosed`; nothing is ported for it, on the same ground as the record
above. `content:Submodule.span ℤ finite`: 71 files, one returned — carlok/leanfrontier
`Topology/FurstenbergFiniteIndex.lean`, finite-index subgroups of `ℤ`, unrelated.
`content:Rat.den bounded`: 51 files, one returned — leanprover-community/physlib
`Units/Exponent.lean`, rational exponents, unrelated. `content:Set.Finite integer points`: 52 files,
one returned — LionSR/TNLean `PEPS/AreaLaw/Geometry/TemplatePolygonFiniteIntegerPoints.lean`, whose
`finite_integerPoints` is a subset of `Set.finite_Icc ... .prod`, i.e. Mathlib's `Set.finite_Icc`
again; nothing to port. What the two lemmas proved here use is Mathlib's
`Module.Basis.sum_repr` and `Module.Basis.mem_span_iff_repr_mem`
(`Mathlib/Algebra/Module/ZLattice/Basic.lean:148`), `Set.Finite.pi` and `Set.finite_Icc`.

### LC-09 record for the dual family (2026-11-15, #161, third unit: `exists_dual_family` retired)

The four queries of this unit, with every hit. `content:dualBasis`: 139 files, 3 returned —
TauCeti `Algebra/Lie/Dual.lean` and `Algebra/Lie/Sl2/Killing.lean` (the `B`-dual basis of Mathlib,
`sum_apply_smul_dualBasis`), mrdouglasny/jacobian-challenge `Periods.lean` (`Basis.dualBasis` of
the *linear* dual); none of them a dual family for a nondegenerate bilinear form.
`content:BilinForm dual basis nondegenerate`: 134 files, 9031 matches, none returned as a file.
`content:apply_dualBasis_left`: 16 files, 3 returned — facebookresearch/atlas-lean
`MathlibExt/Algebra/Lie/LeviDecomposition.lean` and
`v1/Atlas/NumberTheoryI/code/PairingsTheorems.lean`, whose `prop_5_7_existence` is exactly the
statement the retired declaration carried
(`∃ b' : Basis ι K V, ∀ i j, B (b' i) (b j) = if j = i then 1 else 0`, with
`fun i j => BilinForm.apply_dualBasis_left hB b i j` as its proof — i.e. already a two-line
corollary of Mathlib, and the same entries for `prop_5_7_uniqueness` and `cor_5_14`), and TauCeti
`LinearAlgebra/BilinearForm/Basic.lean` (the same rewrite). `content:Gram matrix inverse dual basis
delta`: 22 files, 5699 matches, no file returned. Nothing to port: Mathlib owns the statement, at
`LinearMap.BilinForm.dualBasis` / `apply_dualBasis_left` / `apply_dualBasis_right` /
`dualBasis_repr_apply` / `dualBasis_dualBasis`
(`Mathlib/LinearAlgebra/BilinearForm/Properties.lean`,
the `DualBasis` section), and the hand-rolled injective-implies-surjective derivation that stood in
this file was that lemma with more work. The retired declaration is gone; `apply_dualBasis_right`
supplies the `δ` pairings and `dualBasis_repr_apply` read through `dualBasis_dualBasis` supplies the
coordinate identity, which replaces twenty lines of `Finset.sum_eq_single`.

## References

* E. Looijenga, *Compactifications defined by arrangements II: locally symmetric varieties
  of type IV*, arXiv math/0201218v2 (2002), §4.
* The Tau Ceti contributors, the TauCeti repository (the sign-cell machine this file uses).
-/

@[expose] public section

open PointedCone

open scoped TensorProduct Topology Pointwise

namespace LeanCategories.Lattices.Valued

open QuadraticMap

universe u

variable {V : Type u} [AddCommGroup V] [Module ℚ V]

/-! ## The real form `L(ℝ) = L ⊗_ℚ ℝ` -/

/-- The real form of a `ℚ`-vector space: `L(ℝ) = L ⊗_ℚ ℝ`, carried as `ℝ ⊗[ℚ] L`. -/
abbrev realified (V : Type u) [AddCommGroup V] [Module ℚ V] : Type u := ℝ ⊗[ℚ] V

/-- The canonical topology of the real form: Mathlib's module topology. -/
noncomputable instance realifiedTopology : TopologicalSpace (realified V) :=
  moduleTopology ℝ _

instance realifiedIsModuleTopology : IsModuleTopology ℝ (realified V) := ⟨rfl⟩

instance realifiedContinuousAdd : ContinuousAdd (realified V) :=
  IsModuleTopology.toContinuousAdd ℝ (realified V)

instance realifiedContinuousSMul : ContinuousSMul ℝ (realified V) :=
  IsModuleTopology.toContinuousSMul ℝ (realified V)

/-- `L(ℚ) ⊂ L(ℝ)`: the rational points of the real form. -/
noncomputable def rationalPoint : V →ₗ[ℚ] (realified V) :=
  (TensorProduct.mk ℚ ℝ V) 1

theorem rationalPoint_apply (v : V) : rationalPoint v = (1 : ℝ) ⊗ₜ[ℚ] v := rfl

/-- Scaling a rational point by a rational scalar scales its image by the same real scalar. -/
theorem rationalPoint_rat_smul (q : ℚ) (v : V) :
    rationalPoint (q • v) = (q : ℝ) • rationalPoint v := by
  rw [rationalPoint_apply, rationalPoint_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  have h : (q : ℝ) = (q : ℚ) • (1 : ℝ) := by simp
  rw [h, TensorProduct.smul_tmul]

/-- **The rational points of `L(ℝ) = L ⊗_ℚ ℝ` are dense in it.** A simple tensor `r ⊗ₜ v` is the
limit of the rational points `q ⊗ₜ v` with `q → r` (`Rat.denseRange_cast`), because scalar
multiplication is continuous and `q ⊗ₜ v = 1 ⊗ₜ (q v)` is a rational point; a general element of
the tensor product is a finite sum of simple tensors, and a sum of limits of rational points is a
limit of their sums, which are again rational points, since adding rational points adds the
vectors. This is the density of `L(ℚ)` in `L(ℝ)`. -/
theorem dense_range_rationalPoint : Dense (Set.range (rationalPoint (V := V))) := by
  have hS : ∀ (r : ℝ) (v : V),
      r • rationalPoint v ∈ closure (Set.range (rationalPoint (V := V))) := by
    intro r v
    have hcont : Continuous fun t : ℝ => t • rationalPoint (V := V) v := by
      show Continuous ((fun t : ℝ => t) • fun _ : ℝ => rationalPoint (V := V) v)
      exact continuous_id.smul continuous_const
    have himg := image_closure_subset_closure_image hcont
      (s := Set.range ((↑) : ℚ → ℝ))
    rw [(Rat.denseRange_cast (𝕜 := ℝ)).closure_eq, Set.image_univ] at himg
    have hmem : r • rationalPoint (V := V) v ∈
        closure ((fun t : ℝ => t • rationalPoint (V := V) v) '' Set.range ((↑) : ℚ → ℝ)) :=
      himg (Set.mem_range_self r)
    refine closure_mono ?_ hmem
    rintro _ ⟨q, ⟨qq, rfl⟩, rfl⟩
    exact ⟨qq • v, by
      rw [map_smul]
      exact IsScalarTower.algebraMap_smul (A := ℝ) qq (rationalPoint (V := V) v)⟩
  rw [dense_iff_closure_eq, Set.eq_univ_iff_forall]
  intro x
  induction x using TensorProduct.inductionOn with
  | tmul r v =>
      have h : r ⊗ₜ[ℚ] v = r • rationalPoint v := by
        rw [rationalPoint_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [h]
      exact hS r v
  | add y z hy hz =>
      have hmaps : Set.MapsTo (fun p : realified V × realified V => p.1 + p.2)
          (Set.range (rationalPoint (V := V)) ×ˢ Set.range (rationalPoint (V := V)))
          (closure (Set.range (rationalPoint (V := V)))) := by
        rintro ⟨a, b⟩ ⟨⟨va, rfl⟩, ⟨vb, rfl⟩⟩
        exact subset_closure ⟨va + vb, by rw [map_add]⟩
      have hcl := hmaps.closure (continuous_fst.add continuous_snd)
      rw [closure_prod_eq, closure_closure] at hcl
      exact hcl (x := (y, z)) ⟨hy, hz⟩

/-! ## Definition 4.1: rational cones and rational cone systems -/

/-- Looijenga, Definition 4.1, p. 16 (text version
`.tmp-sources/looijenga-math0201218v2.md:459`): a cone in `L(ℝ)` is *rational* when it is the
convex cone spanned by a finite subset of `L(ℚ)`. -/
def IsRationalCone (σ : PointedCone ℝ (realified V)) : Prop :=
  ∃ s : Finset V, σ = PointedCone.hull ℝ (rationalPoint '' (s : Set V))

/-- The cone generated by the union of two rational generating sets is the join of the two
rational cones. -/
theorem IsRationalCone.sup {P Q : PointedCone ℝ (realified V)}
    (hP : IsRationalCone P) (hQ : IsRationalCone Q) : IsRationalCone (P ⊔ Q) := by
  classical
  obtain ⟨s, hs⟩ := hP
  obtain ⟨t, ht⟩ := hQ
  refine ⟨s ∪ t, ?_⟩
  change P ⊔ Q = Submodule.span (Nonneg ℝ) (rationalPoint '' ((s ∪ t : Finset V) : Set V))
  rw [hs, ht, Finset.coe_union, Set.image_union, Submodule.span_union]

/-- The points of a finite generating set that lie on a cone `τ` generate the intersection of
the cone hull of the set with `τ`. -/
theorem image_inter_eq_image_of_mem {s : Finset V} {τ : PointedCone ℝ (realified V)} :
    rationalPoint '' (s : Set V) ∩ (τ : Set (realified V)) =
      rationalPoint '' {v : V | v ∈ s ∧ rationalPoint v ∈ τ} := by
  ext x
  constructor
  · rintro ⟨⟨v, hv, rfl⟩, hvτ⟩
    exact ⟨v, ⟨hv, hvτ⟩, rfl⟩
  · rintro ⟨v, ⟨hv, hvτ⟩, rfl⟩
    exact ⟨⟨v, hv, rfl⟩, hvτ⟩

/-- A face of a rational cone is rational: it is spanned by those of its rational generators
that lie on it (Looijenga, Definition 4.1, p. 16; #37's `IsLatticeRational.of_isFaceOf`). -/
theorem IsRationalCone.of_isFaceOf {σ τ : PointedCone ℝ (realified V)}
    (hσ : IsRationalCone σ) (hτ : τ.IsFaceOf σ) : IsRationalCone τ := by
  classical
  obtain ⟨s, rfl⟩ := hσ
  refine ⟨s.filter fun v => rationalPoint v ∈ τ, ?_⟩
  refine (hτ.eq_hull_inter_of_eq_hull rfl).trans ?_
  rw [image_inter_eq_image_of_mem]
  congr 1
  ext v
  simp

/-- A rational cone has finitely many faces: each is spanned by a subset of one finite
generating set. -/
theorem finite_faces_of_isRationalCone {σ : PointedCone ℝ (realified V)}
    (hσ : IsRationalCone σ) :
    {F : PointedCone ℝ (realified V) | F.IsFaceOf σ}.Finite := by
  classical
  obtain ⟨s, rfl⟩ := hσ
  refine Set.Finite.subset (s.powerset.finite_toSet.image fun t : Finset V =>
    PointedCone.hull ℝ (rationalPoint '' (t : Set V))) ?_
  rintro F hF
  have hface : F.IsFaceOf (PointedCone.hull ℝ (rationalPoint '' (s : Set V))) := hF
  refine ⟨s.filter fun v => rationalPoint v ∈ F, Finset.mem_powerset.2 (Finset.filter_subset _ _),
    ?_⟩
  refine (?_ : PointedCone.hull ℝ (rationalPoint '' ((s.filter fun v => rationalPoint v ∈ F
      : Finset V) : Set V)) = PointedCone.hull ℝ (rationalPoint '' (s : Set V)
        ∩ (F : Set (realified V)))).trans (hface.eq_hull_inter_of_eq_hull rfl).symm
  rw [image_inter_eq_image_of_mem]
  congr 1
  ext v
  simp

/-! ## Fourier–Motzkin: a rational cone cut by a rational half-space

Looijenga, Example 4.3 (b), pp. 17-18, needs that a cell of `Σ(H)` — a rational cone cut by the
sign conditions of rational hyperplanes — is again a rational cone. One step of Fourier–Motzkin
elimination gives it: the cone cut out of `hull s` by the halfspace `{x | 0 ≤ φ x}` is generated by
the points of `s` on which `φ` is nonnegative together with the boundary combinations
`(-φ v) • u + (φ u) • v` over pairs with opposite strict signs (Ziegler, *Lectures on Polytopes*,
Theorem 1.3, p. 30).

The halfspace cut is **not re-derived here**: it is `Finset.hull_halfspaceGenerators` of
`LeanCategories/ForMathlib/PointedConeFiniteGeneration.lean`, this repository's port of
`TauCeti/Geometry/Convex/Cone/FiniteGeneration.lean` (Mei commit `68536122`, Apache 2.0), which
proves that `Finset.halfspaceGenerators s f` generates `hull s ⊓ {x | 0 ≤ f x}` over any linearly
ordered field. What is added is the rationality: when the cutting form is the extension of a
`ℚ`-linear form, the generators of the cut are the images under `rationalPoint` of finitely many
points of `L(ℚ)` (`image_sliceGens_eq_halfspaceGenerators`), so the cut is a rational cone.

### LC-09 record (2026-11-15)

`content:FourierMotzkin` → `mathlib4/Mathlib/Tactic/Linarith/Oracle/FourierMotzkin.lean` only (the
`linarith` oracle, no cone statement). `content:PointedCone inf halfspace FG` →
`TauCeti/Geometry/Convex/Cone/FiniteGeneration.lean`, `Finset.halfspaceGenerators` and
`Finset.hull_halfspaceGenerators` — the hit, already ported into this repository
(`ForMathlib/PointedConeFiniteGeneration.lean`) and **used** below. `Submodule.FG inf` →
`TauCeti/Algebra/Module/Lattice.lean` (lattice indices), unrelated. `PointedCone.FG` → TauCeti
`Geometry/Convex/Cone/Face/Finite.lean` (finiteness of the face lattice) and LeanPool
`FgConeClosed.lean` (`PointedCone.FG.isClosed`), neither a halfspace cut. The repository's
`ForMathlib/PointedConeMinkowskiWeyl.lean` is the finitely-many-inequalities direction
(`Submodule.FG.cone_dualFG`), cited below for Ziegler's theorem; it does not give the generators
of a cut. Nothing to port beyond the halfspace cut already present.
-/

/-- The half-space `{x | 0 ≤ φ x}` as a cone. -/
def halfspaceCone (φ : (realified V) →ₗ[ℝ] ℝ) : PointedCone ℝ (realified V) where
  carrier := {x | 0 ≤ φ x}
  zero_mem' := by
    show 0 ≤ φ 0
    simp
  add_mem' {x y} hx hy := by
    show 0 ≤ φ (x + y)
    rw [map_add]
    have hx' : 0 ≤ φ x := hx
    have hy' : 0 ≤ φ y := hy
    linarith
  smul_mem' c x hx := by
    show 0 ≤ φ (c • x)
    rw [← Nonneg.coe_smul, map_smul, smul_eq_mul]
    have hx' : 0 ≤ φ x := hx
    exact mul_nonneg c.2 hx'

@[simp] theorem mem_halfspaceCone {φ : (realified V) →ₗ[ℝ] ℝ} {x : realified V} :
    x ∈ halfspaceCone φ ↔ 0 ≤ φ x := Iff.rfl

/-- The halfspace cone is the dual cone of the singleton of the form: the shape in which the
ported `Finset.hull_halfspaceGenerators` states the cut. -/
theorem halfspaceCone_eq_dual (φ : (realified V) →ₗ[ℝ] ℝ) :
    halfspaceCone φ = PointedCone.dual (LinearMap.id : Module.Dual ℝ (realified V) →ₗ[ℝ]
      Module.Dual ℝ (realified V)) {φ} := by
  ext x
  show (0 ≤ φ x) ↔ _
  simp [PointedCone.mem_dual]

/-- A real linear form is *rational* when it is the extension of a `ℚ`-linear form. -/
def IsRationalForm (φ : (realified V) →ₗ[ℝ] ℝ) : Prop :=
  ∃ l : V →ₗ[ℚ] ℚ, ∀ v : V, φ (rationalPoint v) = (l v : ℝ)

theorem IsRationalForm.neg {φ : (realified V) →ₗ[ℝ] ℝ} (h : IsRationalForm φ) :
    IsRationalForm (-φ) := by
  obtain ⟨l, hl⟩ := h
  refine ⟨-l, fun v => ?_⟩
  rw [LinearMap.neg_apply, hl v, LinearMap.neg_apply]
  push_cast
  ring

/-- A rational scalar multiple of a rational form is rational. -/
theorem IsRationalForm.qsmul {φ : (realified V) →ₗ[ℝ] ℝ} (h : IsRationalForm φ) (q : ℚ) :
    IsRationalForm ((q : ℝ) • φ) := by
  obtain ⟨l, hl⟩ := h
  refine ⟨q • l, fun v => ?_⟩
  rw [LinearMap.smul_apply, smul_eq_mul, hl v, LinearMap.smul_apply, smul_eq_mul]
  push_cast
  ring

/-- The difference of two rational forms is rational. -/
theorem IsRationalForm.sub {φ ψ : (realified V) →ₗ[ℝ] ℝ}
    (hφ : IsRationalForm φ) (hψ : IsRationalForm ψ) : IsRationalForm (φ - ψ) := by
  obtain ⟨l, hl⟩ := hφ
  obtain ⟨m, hm⟩ := hψ
  refine ⟨l - m, fun v => ?_⟩
  rw [LinearMap.sub_apply, hl v, hm v, LinearMap.sub_apply]
  push_cast
  ring

/-- The `i`-th coordinate against a `ℚ`-basis, extended to `L(ℝ)` by base change. -/
noncomputable def rationalCoordinate {ι : Type*} (b : Module.Basis ι ℚ V) (i : ι) :
    (realified V) →ₗ[ℝ] ℝ :=
  (Finsupp.lapply i).comp (b.baseChange ℝ).repr.toLinearMap

theorem rationalCoordinate_apply {ι : Type*} (b : Module.Basis ι ℚ V) (i : ι)
    (x : realified V) : rationalCoordinate b i x = (b.baseChange ℝ).repr x i := rfl

theorem rationalCoordinate_rationalPoint {ι : Type*} (b : Module.Basis ι ℚ V) (i : ι) (v : V) :
    rationalCoordinate b i (rationalPoint v) = (b.repr v i : ℝ) := by
  simp [rationalCoordinate, rationalPoint_apply]

/-- Every base-changed rational coordinate is a rational form. -/
theorem isRationalForm_rationalCoordinate {ι : Type*} (b : Module.Basis ι ℚ V) (i : ι) :
    IsRationalForm (rationalCoordinate b i) := by
  refine ⟨(Finsupp.lapply i).comp b.repr.toLinearMap, fun v => ?_⟩
  simp [rationalCoordinate_rationalPoint]

/-- The generators of the cone cut out of `hull (rationalPoint '' s)` by the halfspace of `l`, as
points of `L(ℚ)`: the points of `s` on which `l` is nonnegative, and the boundary combinations
`(-l j) • i + (l i) • j` for `l i > 0 > l j`. This is the preimage under `rationalPoint` of the
ported `Finset.halfspaceGenerators` (`image_sliceGens_eq_halfspaceGenerators`). -/
noncomputable def sliceGens (s : Finset V) (l : V →ₗ[ℚ] ℚ) : Finset V := by
  classical
  exact (s.filter fun v => 0 ≤ l v) ∪
    (((s ×ˢ s).filter fun p => 0 < l p.1 ∧ l p.2 < 0).image
      fun p => (-(l p.2)) • p.1 + (l p.1) • p.2)

theorem mem_sliceGens {s : Finset V} {l : V →ₗ[ℚ] ℚ} {v : V} :
    v ∈ sliceGens s l ↔ (v ∈ s ∧ 0 ≤ l v) ∨
      ∃ i ∈ s, ∃ j ∈ s, 0 < l i ∧ l j < 0 ∧ v = (-(l j)) • i + (l i) • j := by
  classical
  have h1 : sliceGens s l = (s.filter fun v => 0 ≤ l v) ∪
      (((s ×ˢ s).filter fun p => 0 < l p.1 ∧ l p.2 < 0).image
        fun p : V × V => (-(l p.2)) • p.1 + (l p.1) • p.2) := rfl
  rw [h1]
  constructor
  · intro hv
    rcases Finset.mem_union.1 hv with hpos | hneg
    · exact Or.inl ⟨(Finset.mem_filter.1 hpos).1, (Finset.mem_filter.1 hpos).2⟩
    · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hneg
      obtain ⟨a, b⟩ := p
      obtain ⟨hpab, hpa, hpb⟩ := Finset.mem_filter.1 hp
      obtain ⟨ha, hb⟩ := Finset.mem_product.1 hpab
      exact Or.inr ⟨a, ha, b, hb, hpa, hpb, rfl⟩
  · rintro (⟨hm, hp⟩ | ⟨a, ha, b, hb, hpa, hpb, rfl⟩)
    · exact Finset.mem_union.2 (Or.inl (Finset.mem_filter.2 ⟨hm, hp⟩))
    · exact Finset.mem_union.2 (Or.inr (Finset.mem_image.2
        ⟨(a, b), Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨ha, hb⟩, hpa, hpb⟩, rfl⟩))

/-- The boundary combination of two rational points is a rational point. -/
theorem rationalPoint_sliceGen (l : V →ₗ[ℚ] ℚ) (i j : V) :
    rationalPoint ((-(l j)) • i + (l i) • j)
      = (((-(l j) : ℚ)) : ℝ) • rationalPoint i + (((l i : ℚ)) : ℝ) • rationalPoint j := by
  rw [← rationalPoint_rat_smul (q := -(l j)) (v := i),
    ← rationalPoint_rat_smul (q := (l i)) (v := j), ← map_add]

/-- The boundary combination of two rational points, as a rational point. -/
theorem boundaryCombination_rationalPoint {l : V →ₗ[ℚ] ℚ} {φ : (realified V) →ₗ[ℝ] ℝ}
    (hφ : ∀ v : V, φ (rationalPoint v) = (l v : ℝ)) (i j : V) :
    LinearMap.boundaryCombination φ (rationalPoint i) (rationalPoint j)
      = rationalPoint ((-(l j)) • i + (l i) • j) := by
  rw [LinearMap.boundaryCombination_def, hφ i, hφ j,
    show -(((l j : ℚ)) : ℝ) = (((-(l j) : ℚ)) : ℝ) from by push_cast; ring]
  exact (rationalPoint_sliceGen l i j).symm

/-- The rational points of a finite set, as a finset of the real form. -/
noncomputable def rationalPoints (s : Finset V) : Finset (realified V) := by
  classical exact s.image rationalPoint

@[simp] theorem mem_rationalPoints {s : Finset V} {x : realified V} :
    x ∈ rationalPoints s ↔ ∃ v ∈ s, rationalPoint v = x := by
  classical
  rw [rationalPoints, Finset.mem_image]

@[simp] theorem coe_rationalPoints (s : Finset V) :
    (↑(rationalPoints s) : Set (realified V)) = rationalPoint '' (s : Set V) := by
  classical
  rw [rationalPoints, Finset.coe_image]

/-- The image of `sliceGens` in the real form. -/
noncomputable def sliceImage (s : Finset V) (l : V →ₗ[ℚ] ℚ) : Finset (realified V) := by
  classical exact (sliceGens s l).image rationalPoint

@[simp] theorem coe_sliceImage (s : Finset V) (l : V →ₗ[ℚ] ℚ) :
    (↑(sliceImage s l) : Set (realified V)) = rationalPoint '' (sliceGens s l : Set V) := by
  classical
  rw [sliceImage, Finset.coe_image]

/-- **The halfspace cut of a rational cone is generated by rational points**: the generators of
the ported `Finset.halfspaceGenerators` are exactly the images of the points of `sliceGens`. -/
theorem image_sliceGens_eq_halfspaceGenerators {s : Finset V} {l : V →ₗ[ℚ] ℚ}
    {φ : (realified V) →ₗ[ℝ] ℝ} (hφ : ∀ v : V, φ (rationalPoint v) = (l v : ℝ)) :
    sliceImage s l = Finset.halfspaceGenerators (rationalPoints s) φ := by
  classical
  ext x
  rw [sliceImage, rationalPoints, Finset.mem_image, Finset.mem_halfspaceGenerators_iff]
  constructor
  · rintro ⟨v, hv, rfl⟩
    rcases mem_sliceGens.1 hv with ⟨hvs, hvl⟩ | ⟨i, hi, j, hj, hli, hlj, rfl⟩
    · refine Or.inl ⟨Finset.mem_image.2 ⟨v, hvs, rfl⟩, ?_⟩
      rw [hφ v]
      exact_mod_cast hvl
    · refine Or.inr ⟨rationalPoint i, Finset.mem_image.2 ⟨i, hi, rfl⟩, rationalPoint j,
        Finset.mem_image.2 ⟨j, hj, rfl⟩, ?_, ?_, ?_⟩
      · rw [hφ i]
        exact_mod_cast hli
      · rw [hφ j]
        exact_mod_cast hlj
      · exact boundaryCombination_rationalPoint hφ i j
  · rintro (⟨hx, hfx⟩ | ⟨u, hu, v, hv, hfu, hfv, hbc⟩)
    · obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 hx
      refine ⟨w, mem_sliceGens.2 (Or.inl ⟨hw, ?_⟩), rfl⟩
      rw [hφ w] at hfx
      exact_mod_cast hfx
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hu
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hv
      refine ⟨(-(l j)) • i + (l i) • j,
        mem_sliceGens.2 (Or.inr ⟨i, hi, j, hj, ?_, ?_, rfl⟩), ?_⟩
      · rw [hφ i] at hfu
        exact_mod_cast hfu
      · rw [hφ j] at hfv
        exact_mod_cast hfv
      · rw [← hbc]
        exact (boundaryCombination_rationalPoint hφ i j).symm

/-- **The cone cut out of a rational cone by a rational half-space is a rational cone**
(Looijenga, Example 4.3 (b), pp. 17-18, by Fourier–Motzkin elimination): the ported
`Finset.hull_halfspaceGenerators` gives the generators of the cut, and
`image_sliceGens_eq_halfspaceGenerators` shows they are rational points. -/
theorem isRationalCone_inf_halfspace {P : PointedCone ℝ (realified V)} (hP : IsRationalCone P)
    {φ : (realified V) →ₗ[ℝ] ℝ} (hφ : IsRationalForm φ) :
    IsRationalCone (P ⊓ halfspaceCone φ) := by
  classical
  obtain ⟨s, rfl⟩ := hP
  obtain ⟨l, hl⟩ := hφ
  refine ⟨sliceGens s l, ?_⟩
  have hgen := Finset.hull_halfspaceGenerators (rationalPoints s) φ
  rw [← image_sliceGens_eq_halfspaceGenerators hl, coe_sliceImage, coe_rationalPoints,
    ← halfspaceCone_eq_dual] at hgen
  exact hgen.symm

/-- **The whole real form is a rational cone.** A finite `ℚ`-basis and the negatives of its
members generate it. The set is self-negating, so its pointed-cone hull agrees with the linear
span, which is the whole space by `Module.Basis.baseChange`. -/
theorem isRationalCone_top [Module.Finite ℚ V] :
    IsRationalCone (⊤ : PointedCone ℝ (realified V)) := by
  classical
  let b := Module.finBasis ℚ V
  let t : Finset V := Finset.univ.image fun p : Fin (Module.finrank ℚ V) × Bool =>
    if p.2 then b p.1 else -b p.1
  have hmem (i) : rationalPoint (b i) ∈ rationalPoint '' (t : Set V) := by
    refine ⟨(b i), ?_, rfl⟩
    exact Finset.mem_coe.2 (Finset.mem_image.2 ⟨(i, true), by simp⟩)
  have htneg : ∀ v ∈ t, -v ∈ t := by
    intro v hv
    obtain ⟨p, -, rfl⟩ := Finset.mem_image.1 hv
    refine Finset.mem_image.2 ⟨(p.1, !p.2), Finset.mem_univ _, ?_⟩
    cases p.2 <;> simp_all
  have hself : -(rationalPoint '' (t : Set V)) = rationalPoint '' (t : Set V) := by
    rw [← Set.image_neg_eq_neg]
    ext y
    constructor
    · rintro ⟨_, ⟨v, hv, rfl⟩, rfl⟩
      exact ⟨-v, htneg v hv, by rw [map_neg]⟩
    · rintro ⟨v, hv, rfl⟩
      exact ⟨-rationalPoint v, ⟨-v, htneg v hv, by rw [map_neg]⟩, by simp⟩
  have hspan : Submodule.span ℝ (rationalPoint '' (t : Set V)) = ⊤ := by
    apply top_unique
    rw [← (b.baseChange ℝ).span_eq]
    refine Submodule.span_mono ?_
    rintro y ⟨i, rfl⟩
    simpa only [Module.Basis.baseChange_apply, rationalPoint_apply] using hmem i
  refine ⟨t, ?_⟩
  have hcone : PointedCone.hull ℝ (rationalPoint '' (t : Set V)) = ⊤ := by
    rw [PointedCone.hull_eq_span_of_neg_eq (R := ℝ) hself, hspan]
    rfl
  exact hcone.symm

/-- A cone cut out of the whole real form by normalized coordinate bounds. At a point with
`0 < ell x`, the ratios `rationalCoordinate b i x / ell x` lie between `lo i` and `up i`.
The construction is used for Lemma-Definition 4.5's rational neighbourhood of a point of `C`. -/
noncomputable def normalizedConeOn {ι : Type*} [DecidableEq ι] (F : Finset ι)
    (b : Module.Basis ι ℚ V) (ell : (realified V) →ₗ[ℝ] ℝ) (lo up : ι → ℚ) :
    PointedCone ℝ (realified V) :=
  (F.inf fun i => halfspaceCone (rationalCoordinate b i - (lo i : ℝ) • ell) ⊓
    halfspaceCone ((up i : ℝ) • ell - rationalCoordinate b i)) ⊓ halfspaceCone ell

theorem mem_normalizedConeOn {ι : Type*} [DecidableEq ι] {F : Finset ι}
    {b : Module.Basis ι ℚ V} {ell : (realified V) →ₗ[ℝ] ℝ} {lo up : ι → ℚ}
    {y : realified V} :
    y ∈ normalizedConeOn F b ell lo up ↔
      (∀ i ∈ F, 0 ≤ (rationalCoordinate b i - (lo i : ℝ) • ell) y ∧
        0 ≤ ((up i : ℝ) • ell - rationalCoordinate b i) y) ∧ 0 ≤ ell y := by
  simp only [normalizedConeOn, Submodule.mem_inf, mem_halfspaceCone, Finset.inf_eq_iInf,
    Submodule.mem_iInf]

/-- Normalized rational coordinate bounds define a rational cone. Induction on the finite set of
cuts uses `isRationalCone_inf_halfspace` and starts from `isRationalCone_top`. -/
theorem isRationalCone_normalizedConeOn {ι : Type*} [DecidableEq ι]
    (F : Finset ι) (b : Module.Basis ι ℚ V) [Module.Finite ℚ V]
    {ell : (realified V) →ₗ[ℝ] ℝ}
    (hell : IsRationalForm ell) (lo up : ι → ℚ) :
    IsRationalCone (normalizedConeOn F b ell lo up) := by
  have hrlo (i : ι) : IsRationalForm (rationalCoordinate b i - (lo i : ℝ) • ell) :=
    IsRationalForm.sub (isRationalForm_rationalCoordinate b i)
      (IsRationalForm.qsmul hell (lo i))
  have hrup (i : ι) : IsRationalForm ((up i : ℝ) • ell - rationalCoordinate b i) :=
    IsRationalForm.sub (IsRationalForm.qsmul hell (up i))
      (isRationalForm_rationalCoordinate b i)
  induction F using Finset.induction with
  | empty =>
      simpa [normalizedConeOn] using
        (isRationalCone_inf_halfspace (P := (⊤ : PointedCone ℝ (realified V)))
          isRationalCone_top hell)
  | @insert i F hi ih =>
      have h := isRationalCone_inf_halfspace
        (isRationalCone_inf_halfspace ih (hrlo i)) (hrup i)
      simpa [normalizedConeOn, Finset.inf_insert, inf_assoc, inf_left_comm, inf_comm] using h

/-- **A nonzero point in the interior of a cone has a rational cone neighbourhood contained in
the cone** (the local input to Looijenga's Lemma-Definition 4.5). Choose a signed coordinate `ell`
positive at `x`, take a small closed coordinate ball around `x` inside `C`, and choose rational
bounds around the ratios `rationalCoordinate b i x / ell x`. Their normalized cone is a
neighbourhood of `x`. Conversely, if `y` satisfies the bounds, normalize it to `ell z = ell x`;
the coordinate bounds put `z` in the closed ball inside `C`; and `y` is a nonnegative multiple
of `z`. This handles arbitrary real `x`, not only rational points. The open-cone statement is the
wrapper `exists_rationalCone_mem_nhds_subset_of_ne_zero` immediately below. -/
theorem exists_rationalCone_mem_nhds_subset_of_mem_interior [Module.Finite ℚ V]
    {C : PointedCone ℝ (realified V)} {x : realified V} (hx : x ∈ interior C) (hx0 : x ≠ 0) :
    ∃ K : PointedCone ℝ (realified V), IsRationalCone K ∧
      (K : Set (realified V)) ∈ 𝓝 x ∧ K ≤ C := by
  classical
  let b := Module.finBasis ℚ V
  let e := (b.baseChange ℝ).equivFun
  have hex (i) (y : realified V) : rationalCoordinate b i y = e y i := by
    simp only [rationalCoordinate_apply, e, Module.Basis.equivFun_apply]
  obtain ⟨j, hj⟩ : ∃ j, e x j ≠ 0 := by
    by_contra h
    push Not at h
    apply hx0
    apply e.injective
    ext i
    simp [h i]
  let s : ℚ := if 0 < e x j then 1 else -1
  let ell : (realified V) →ₗ[ℝ] ℝ := (s : ℝ) • rationalCoordinate b j
  have hell : IsRationalForm ell :=
    IsRationalForm.qsmul (isRationalForm_rationalCoordinate b j) s
  have hellx : 0 < ell x := by
    dsimp [ell, s]
    split_ifs with hpos
    · rw [hex]
      simpa using hpos
    · have hneg : e x j < 0 := (lt_or_gt_of_ne hj).resolve_right hpos
      simp only [Rat.cast_neg, Rat.cast_one]
      rw [hex]
      simpa using hneg
  let ex : Fin (Module.finrank ℚ V) → ℝ := e x
  let r : Fin (Module.finrank ℚ V) → ℝ := fun i => ex i / ell x
  have hcont : Continuous e.symm := IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap
  have hxint : e.symm ex ∈ interior (C : Set (realified V)) := by
    dsimp [ex]
    rw [LinearEquiv.symm_apply_apply]
    exact hx
  have hpre : (C : Set (realified V)) ∈ 𝓝 (e.symm ex) := mem_interior_iff_mem_nhds.1 hxint
  have hnhood : e.symm ⁻¹' (C : Set (realified V)) ∈ 𝓝 ex :=
    hcont.continuousAt.preimage_mem_nhds hpre
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hnhood
  let R := ε / 2
  have hR : 0 < R := by dsimp [R]; positivity
  let η := R / ell x
  have hη : 0 < η := div_pos hR hellx
  have hballsub : Metric.closedBall ex R ⊆ e.symm ⁻¹' (C : Set (realified V)) :=
    (Metric.closedBall_subset_ball (by dsimp [R]; linarith)).trans hball
  choose lo hlo₁ hlo₂ using fun i =>
    exists_rat_btwn (show r i - η < r i from sub_lt_self (r i) hη)
  choose up hup₁ hup₂ using fun i =>
    exists_rat_btwn (show r i < r i + η from lt_add_of_pos_right (r i) hη)
  let K := normalizedConeOn Finset.univ b ell lo up
  have hKrat : IsRationalCone K := isRationalCone_normalizedConeOn _ _ hell _ _
  refine ⟨K, hKrat, ?_, ?_⟩
  · let U : Set (realified V) := {y | 0 < ell y} ∩ {y | ∀ i,
      0 < (rationalCoordinate b i - (lo i : ℝ) • ell) y ∧
        0 < ((up i : ℝ) • ell - rationalCoordinate b i) y}
    have hUopen : IsOpen U := by
      dsimp only [U]
      refine (isOpen_lt continuous_const (IsModuleTopology.continuous_of_linearMap ell)).inter ?_
      rw [show {y | ∀ i, 0 < (rationalCoordinate b i - (lo i : ℝ) • ell) y ∧
          0 < ((up i : ℝ) • ell - rationalCoordinate b i) y} =
        ⋂ i, {y | 0 < (rationalCoordinate b i - (lo i : ℝ) • ell) y ∧
          0 < ((up i : ℝ) • ell - rationalCoordinate b i) y} from by
        ext y
        simp only [Set.mem_iInter, Set.mem_ofPred_eq]]
      apply isOpen_iInter_of_finite
      intro i
      change IsOpen ({y | (0 : ℝ) < (rationalCoordinate b i - (lo i : ℝ) • ell) y} ∩
        {y | (0 : ℝ) < ((up i : ℝ) • ell - rationalCoordinate b i) y})
      exact (isOpen_lt continuous_const (IsModuleTopology.continuous_of_linearMap
        (rationalCoordinate b i - (lo i : ℝ) • ell))).inter
        (isOpen_lt continuous_const (IsModuleTopology.continuous_of_linearMap
          ((up i : ℝ) • ell - rationalCoordinate b i)))
    have hxU : x ∈ U := by
      refine ⟨hellx, fun i => ?_⟩
      constructor <;>
        simp only [LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, hex]
      · exact sub_pos.mpr ((lt_div_iff₀ hellx).1 (hlo₂ i))
      · exact sub_pos.mpr ((div_lt_iff₀ hellx).1 (hup₁ i))
    have hUK : U ⊆ (K : Set (realified V)) := by
      intro y hy
      change y ∈ normalizedConeOn Finset.univ b ell lo up
      rw [mem_normalizedConeOn]
      exact ⟨fun i _ => ⟨(hy.2 i).1.le, (hy.2 i).2.le⟩, hy.1.le⟩
    exact Filter.mem_of_superset (hUopen.mem_nhds hxU) hUK
  · intro y hy
    rw [mem_normalizedConeOn] at hy
    have hbnd (i) := hy.1 i (Finset.mem_univ i)
    rcases hy.2.eq_or_lt with helly | helly
    · have hcoord (i) : rationalCoordinate b i y = 0 := by
        have hm := hbnd i
        simp only [LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul] at hm
        rw [← helly] at hm
        simp only [mul_zero, sub_zero, zero_sub] at hm
        exact le_antisymm (neg_nonneg.mp hm.2) hm.1
      have hy0 : y = 0 := by
        apply (b.baseChange ℝ).repr.injective
        ext i
        rw [← rationalCoordinate_apply]
        exact hcoord i
      rw [hy0]
      exact C.zero_mem
    · have helly0 : ell y ≠ 0 := ne_of_gt helly
      let z := (ell x / ell y) • y
      have hzcoord (i) : rationalCoordinate b i z = (ell x / ell y) * rationalCoordinate b i y := by
        dsimp [z]
        rw [map_smul, smul_eq_mul]
      have hzball : e z ∈ Metric.closedBall ex R := by
        rw [closedBall_pi ex hR.le]
        intro i _
        change e z i ∈ Metric.closedBall (ex i) R
        rw [Real.closedBall_eq_Icc, Set.mem_Icc]
        have hzratio : e z i / ell x = rationalCoordinate b i y / ell y := by
          rw [← hex i z, hzcoord]
          field_simp
        have hlow : (r i - η) * ell x < e z i := by
          apply (lt_div_iff₀ hellx).1
          rw [hzratio]
          have hl : r i - η < (lo i : ℝ) := hlo₁ i
          have hb : (lo i : ℝ) ≤ rationalCoordinate b i y / ell y := by
            apply (le_div_iff₀ helly).2
            have hm := hbnd i
            simp only [LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul] at hm
            exact sub_nonneg.mp hm.1
          exact hl.trans_le hb
        have hupp : e z i < (r i + η) * ell x := by
          apply (div_lt_iff₀ hellx).1
          rw [hzratio]
          have hu : (up i : ℝ) < r i + η := hup₂ i
          have hb : rationalCoordinate b i y / ell y ≤ (up i : ℝ) := by
            apply (div_le_iff₀ helly).2
            have hm := hbnd i
            simp only [LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul] at hm
            exact sub_nonneg.mp hm.2
          exact hb.trans_lt hu
        have hid₁ : (r i - η) * ell x = ex i - R := by
          dsimp [r, η]
          field_simp
        have hid₂ : (r i + η) * ell x = ex i + R := by
          dsimp [r, η]
          field_simp
        rw [hid₁] at hlow
        rw [hid₂] at hupp
        constructor <;> linarith
      have hzC : z ∈ (C : Set (realified V)) := by
        have hm := hballsub hzball
        change e.symm (e z) ∈ (C : Set (realified V)) at hm
        simpa only [LinearEquiv.symm_apply_apply] using hm
      have hy_eq : (ell y / ell x) • z = y := by
        dsimp [z]
        rw [smul_smul]
        field_simp
        simp
      rw [← hy_eq]
      exact C.smul_mem (div_nonneg helly.le hellx.le) hzC

/-- A nonzero point of an open cone has a rational cone neighbourhood contained in the cone.
This is the open-cone wrapper of `exists_rationalCone_mem_nhds_subset_of_mem_interior`. -/
theorem exists_rationalCone_mem_nhds_subset_of_ne_zero [Module.Finite ℚ V]
    {C : PointedCone ℝ (realified V)} (hCopen : IsOpen (C : Set (realified V)))
    {x : realified V} (hx : x ∈ C) (hx0 : x ≠ 0) :
    ∃ K : PointedCone ℝ (realified V), IsRationalCone K ∧
      (K : Set (realified V)) ∈ 𝓝 x ∧ K ≤ C :=
  exists_rationalCone_mem_nhds_subset_of_mem_interior
    (mem_interior_iff_mem_nhds.2 (hCopen.mem_nhds hx)) hx0

/-- Looijenga, Definition 4.1, p. 16: a *rational cone system* in `L(ℝ)` is a finite
collection of nondegenerate rational convex cones such that a face of a member is a member,
and any two members meet along a common face. -/
structure IsRationalConeSystem (S : Set (PointedCone ℝ (realified V))) : Prop where
  /-- A rational cone system is finite. -/
  finite : S.Finite
  /-- Every member is nondegenerate: it contains no affine line. -/
  salient : ∀ σ ∈ S, (σ : ConvexCone ℝ (realified V)).Salient
  /-- Every member is a rational cone. -/
  isRational : ∀ σ ∈ S, IsRationalCone σ
  /-- A face of a member is a member. -/
  mem_of_isFaceOf : ∀ ⦃σ τ⦄, σ ∈ S → τ.IsFaceOf σ → τ ∈ S
  /-- Two members meet along a common face. -/
  inf_isFaceOf_left : ∀ ⦃σ τ⦄, σ ∈ S → τ ∈ S → (σ ⊓ τ).IsFaceOf σ

namespace IsRationalConeSystem

variable {S : Set (PointedCone ℝ (realified V))}

/-- The intersection of two members of a rational cone system is a member. -/
theorem inf_mem (hS : IsRationalConeSystem S) {σ τ : PointedCone ℝ (realified V)}
    (hσ : σ ∈ S) (hτ : τ ∈ S) : σ ⊓ τ ∈ S :=
  hS.mem_of_isFaceOf hσ (hS.inf_isFaceOf_left hσ hτ)

/-- The intersection of two members is a face of the second one. -/
theorem inf_isFaceOf_right (hS : IsRationalConeSystem S) {σ τ : PointedCone ℝ (realified V)}
    (hσ : σ ∈ S) (hτ : τ ∈ S) : (σ ⊓ τ).IsFaceOf τ :=
  inf_comm σ τ ▸ hS.inf_isFaceOf_left hτ hσ

end IsRationalConeSystem

/-- The faces of a nondegenerate rational cone form a rational cone system: the facial
system of Definition 4.1, p. 16. -/
theorem isRationalConeSystem_faces {σ : PointedCone ℝ (realified V)} (hσ : IsRationalCone σ)
    (hσ' : (σ : ConvexCone ℝ (realified V)).Salient) :
    IsRationalConeSystem {F : PointedCone ℝ (realified V) | F.IsFaceOf σ} where
  finite := finite_faces_of_isRationalCone hσ
  salient F hF := hσ'.anti fun x hx => hF.le hx
  isRational F hF := IsRationalCone.of_isFaceOf (σ := σ) (τ := F) hσ hF
  mem_of_isFaceOf := by
    intro _ _ G hG
    exact hG.trans G
  inf_isFaceOf_left := by
    intro A B hA hB
    exact (IsFaceOf.isFaceOf_iff_le (hA.inf_left hB) hA).2 inf_le_left

/-! ## Definition 4.2: the rational closure and locally rational decompositions -/

/-- `L(ℚ) ∩ C̄`: the rational points in the closure of `C` (Looijenga, Definition 4.2, p. 17). -/
noncomputable def rationalBoundary (C : PointedCone ℝ (realified V)) : Set (realified V) :=
  rationalPoint '' (Set.univ : Set V) ∩ (C.closure : Set (realified V))

theorem zero_mem_rationalBoundary (C : PointedCone ℝ (realified V)) :
    (0 : realified V) ∈ rationalBoundary C :=
  ⟨⟨0, Set.mem_univ 0, by simp [rationalPoint]⟩, C.closure.zero_mem⟩

/-- `L(ℚ) ∩ C̄` is closed under scaling by nonnegative rationals. -/
theorem rat_smul_mem_rationalBoundary (C : PointedCone ℝ (realified V)) {q : ℚ} (hq : 0 ≤ q)
    {x : realified V} (hx : x ∈ rationalBoundary C) : (q : ℝ) • x ∈ rationalBoundary C := by
  obtain ⟨⟨v, -, hvx⟩, hxcl⟩ := hx
  rw [← hvx] at hxcl ⊢
  refine ⟨⟨q • v, Set.mem_univ _, ?_⟩, ?_⟩
  · rw [rationalPoint_apply, rationalPoint_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    have h : (q : ℝ) = (q : ℚ) • (1 : ℝ) := by simp
    rw [h, TensorProduct.smul_tmul]
  · exact PointedCone.smul_mem C.closure (by exact_mod_cast hq) hxcl

/-- The convex hull of `L(ℚ) ∩ C̄` is closed under scaling by nonnegative rationals. -/
theorem convexHull_rat_smul_mem (C : PointedCone ℝ (realified V)) {q : ℚ} (hq : 0 ≤ q)
    {x : realified V} (hx : x ∈ convexHull ℝ (rationalBoundary C)) :
    (q : ℝ) • x ∈ convexHull ℝ (rationalBoundary C) := by
  have hconv : Convex ℝ {y : realified V | (q : ℝ) • y ∈ convexHull ℝ (rationalBoundary C)} := by
    intro y hy z hz a b ha hb hab
    have hsplit : (q : ℝ) • (a • y + b • z) = a • ((q : ℝ) • y) + b • ((q : ℝ) • z) := by
      rw [smul_add, smul_comm (q : ℝ) a y, smul_comm (q : ℝ) b z]
    change (q : ℝ) • (a • y + b • z) ∈ convexHull ℝ (rationalBoundary C)
    rw [hsplit]
    exact (convex_convexHull ℝ (rationalBoundary C)) hy hz ha hb hab
  exact convexHull_min (s := rationalBoundary C)
    (t := {y : realified V | (q : ℝ) • y ∈ convexHull ℝ (rationalBoundary C)})
    (fun y hy => subset_convexHull ℝ _ (rat_smul_mem_rationalBoundary C hq hy)) hconv hx

/-- **The convex hull of `L(ℚ) ∩ C̄` is a cone**, and is closed under scaling by every
nonnegative real: for `a > 0` and rationals `q₁ < a < q₂`, the point `a • x` is the point
`q₁ • x` moved a fraction `(a - q₁)/(q₂ - q₁)` of the way towards `q₂ • x`, and both ends lie
in the hull by the rational scaling above (Looijenga, Definition 4.2, p. 17). -/
theorem convexHull_smul_mem (C : PointedCone ℝ (realified V)) {a : ℝ} (ha : 0 ≤ a)
    {x : realified V} (hx : x ∈ convexHull ℝ (rationalBoundary C)) :
    a • x ∈ convexHull ℝ (rationalBoundary C) := by
  rcases ha.eq_or_lt with h0 | hapos
  · rw [← h0, zero_smul]
    exact subset_convexHull ℝ _ (zero_mem_rationalBoundary C)
  · obtain ⟨q₁, hq₁pos, hq₁a⟩ := exists_rat_btwn hapos
    obtain ⟨q₂, haq₂, -⟩ := exists_rat_btwn (show a < a + 1 by linarith)
    have hq₁ : (0 : ℚ) ≤ q₁ := by exact_mod_cast hq₁pos.le
    have hq₂ : (0 : ℚ) ≤ q₂ := by
      have h : (0 : ℝ) < (q₂ : ℝ) := hq₁pos.trans (hq₁a.trans haq₂)
      exact_mod_cast h.le
    set t : ℝ := (a - q₁) / (q₂ - q₁) with ht
    have hq₂q₁ : (0 : ℝ) < (q₂ : ℝ) - q₁ := by
      have : (q₁ : ℝ) < (q₂ : ℝ) := hq₁a.trans haq₂
      linarith
    have ht0 : 0 ≤ t := div_nonneg (by linarith) hq₂q₁.le
    have ht1 : t ≤ 1 := by
      rw [ht, div_le_one hq₂q₁]
      linarith
    have hcomb : t • ((q₂ : ℝ) • x) + (1 - t) • ((q₁ : ℝ) • x) = a • x := by
      rw [smul_smul, smul_smul, ← add_smul]
      congr 1
      rw [ht]
      field_simp
      ring
    rw [← hcomb]
    refine (convex_convexHull ℝ (rationalBoundary C))
      (convexHull_rat_smul_mem C hq₂ hx) (convexHull_rat_smul_mem C hq₁ hx) ht0 ?_ ?_
    · linarith
    · ring

/-- **The convex hull of `L(ℚ) ∩ C̄` is closed under conical combinations.** Both scaled points
lie in the hull by `convexHull_smul_mem`, so their midpoint does, and the sum is twice the
midpoint. -/
theorem convexHull_coneComb (C : PointedCone ℝ (realified V))
    {x y : realified V} (hx : x ∈ convexHull ℝ (rationalBoundary C))
    (hy : y ∈ convexHull ℝ (rationalBoundary C)) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    a • x + b • y ∈ convexHull ℝ (rationalBoundary C) := by
  have hax : a • x ∈ convexHull ℝ (rationalBoundary C) := convexHull_smul_mem C ha hx
  have hby : b • y ∈ convexHull ℝ (rationalBoundary C) := convexHull_smul_mem C hb hy
  have hmid : (1 / 2 : ℝ) • (a • x) + (1 / 2 : ℝ) • (b • y)
      ∈ convexHull ℝ (rationalBoundary C) :=
    (convex_convexHull ℝ (rationalBoundary C)) hax hby (by norm_num) (by norm_num) (by norm_num)
  have h2 : (a • x + b • y : realified V)
      = (2 : ℝ) • ((1 / 2 : ℝ) • (a • x) + (1 / 2 : ℝ) • (b • y)) := by
    rw [smul_add]
    rw [show (2 : ℝ) • ((1 / 2 : ℝ) • (a • x)) = a • x by rw [smul_smul]; norm_num]
    rw [show (2 : ℝ) • ((1 / 2 : ℝ) • (b • y)) = b • y by rw [smul_smul]; norm_num]
  rw [h2]
  exact convexHull_smul_mem C (by norm_num) hmid

/-- Looijenga, Definition 4.2, p. 17: the *rational closure* `C₊` of a convex cone `C` is the
convex hull of `L(ℚ) ∩ closure C`. It is a cone (`convexHull_coneComb`), and it is the cone
generated by that set: the hull contains the set and is a cone, so it contains the generated
cone, and the generated cone is convex and contains the set (`rationalClosure_eq_hull`). -/
noncomputable def rationalClosure (C : PointedCone ℝ (realified V)) :
    PointedCone ℝ (realified V) where
  carrier := convexHull ℝ (rationalBoundary C)
  zero_mem' := subset_convexHull ℝ _ (zero_mem_rationalBoundary C)
  add_mem' {x y} hx hy := by
    simpa using convexHull_coneComb C hx hy (a := 1) (b := 1) zero_le_one zero_le_one
  smul_mem' c {x} hx := convexHull_smul_mem C (a := (c : ℝ)) c.2 hx

theorem coe_rationalClosure (C : PointedCone ℝ (realified V)) :
    (rationalClosure C : Set (realified V)) = convexHull ℝ (rationalBoundary C) := rfl

/-- The rational closure is the cone generated by `L(ℚ) ∩ C̄`: the convex hull of a set that
contains `0` and is closed under positive rational scaling is a cone
(Looijenga, Definition 4.2, p. 17). -/
theorem rationalClosure_eq_hull (C : PointedCone ℝ (realified V)) :
    rationalClosure C = PointedCone.hull ℝ (rationalBoundary C) := by
  refine le_antisymm ?_ ?_
  · intro x hx
    change x ∈ convexHull ℝ (rationalBoundary C) at hx
    exact convexHull_min (s := rationalBoundary C)
      (t := (PointedCone.hull ℝ (rationalBoundary C) : Set (realified V)))
      (fun y hy => PointedCone.subset_hull hy)
      ((PointedCone.hull ℝ (rationalBoundary C) : ConvexCone ℝ (realified V)).convex) hx
  · refine Submodule.span_le (R := {c : ℝ // 0 ≤ c}) (M := realified V)
      (s := rationalBoundary C) (p := rationalClosure C) |>.2 fun x hx => ?_
    change x ∈ convexHull ℝ (rationalBoundary C)
    exact subset_convexHull ℝ _ hx

theorem mem_rationalClosure {C : PointedCone ℝ (realified V)} {x : realified V} :
    x ∈ rationalClosure C ↔ x ∈ convexHull ℝ (rationalBoundary C) :=
  Iff.rfl

/-- **Every point of `C₊` lies in a rational subcone of `C₊`.** Its finite nonnegative expansion in
`rationalClosure` supplies the generators. This is the pointwise statement needed when face and
intersection properties are lifted from rational traces to the original members. -/
theorem exists_rationalCone_le_rationalClosure_and_mem {C : PointedCone ℝ (realified V)}
    {x : realified V} (hx : x ∈ rationalClosure C) :
    ∃ K : PointedCone ℝ (realified V), IsRationalCone K ∧ K ≤ rationalClosure C ∧ x ∈ K := by
  classical
  rw [rationalClosure_eq_hull] at hx
  obtain ⟨n, f, g, hgsum⟩ := Submodule.mem_span_set'.1 hx
  choose v hv using fun i => (g i).2.1
  let a : Fin n → realified V := fun i => ((g i) : realified V)
  have ha : ∀ i, a i = rationalPoint (v i) := fun i => (hv i).2.symm
  let s := Finset.univ.image v
  let K := PointedCone.hull ℝ (rationalPoint '' (s : Set V))
  have hgen : ∀ i, rationalPoint (v i) ∈ rationalPoint '' (s : Set V) := by
    intro i
    have hvi : v i ∈ (s : Set V) := by
      apply Finset.mem_coe.2
      dsimp [s]
      exact Finset.mem_image.2 ⟨i, Finset.mem_univ _, rfl⟩
    exact Set.mem_image_of_mem rationalPoint hvi
  have hsheet : ∀ i, rationalPoint (v i) ∈ rationalBoundary C := by
    intro i
    rw [← ha i]
    exact (g i).2
  refine ⟨K, ⟨s, rfl⟩, ?_, ?_⟩
  · change Submodule.span (Nonneg ℝ) (rationalPoint '' (s : Set V)) ≤ rationalClosure C
    rw [rationalClosure_eq_hull C]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨w, hw, rfl⟩
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hw
    exact PointedCone.subset_hull (hsheet i)
  · rw [← hgsum]
    exact Submodule.sum_mem _ fun i _ => PointedCone.smul_mem K (f i).2 (by
      change a i ∈ K
      rw [ha i]
      exact PointedCone.subset_hull (hgen i))

/-- **The open cone `C` lies in the closure of `L(ℚ) ∩ C̄`.** A neighbourhood of `x ∈ C` meets the
rational points (they are dense, `dense_range_rationalPoint`) and meets `C` (it is open), so it
meets `L(ℚ) ∩ C`, which is contained in `L(ℚ) ∩ C̄`. -/
theorem subset_closure_rationalBoundary (C : PointedCone ℝ (realified V))
    (hC : IsOpen (C : Set (realified V))) :
    (C : Set (realified V)) ⊆ closure (rationalBoundary C) := by
  intro x hx
  rw [mem_closure_iff_nhds]
  intro T hT
  obtain ⟨U, hUT, hU, hxU⟩ := mem_nhds_iff.1 hT
  have hopen : IsOpen (U ∩ (C : Set (realified V))) := hU.inter hC
  have hne : (U ∩ (C : Set (realified V))).Nonempty := ⟨x, hxU, hx⟩
  obtain ⟨y, hyS, hy⟩ := dense_range_rationalPoint.exists_mem_open hopen hne
  exact ⟨y, hUT hy.1, ⟨by simpa using hyS, subset_closure hy.2⟩⟩

/-- **The open cone `C` lies in the closure of its rational closure `C₊`** (Looijenga, Definition
4.2, p. 17). This does not by itself give `C ⊆ C₊`: the convex hull of the rational points of `C̄`
is not known to be closed. That step is `subset_rationalClosure` below, which needs the finite
dimensionality of `L` and the simplex around a point of the open cone. -/
theorem subset_closure_rationalClosure (C : PointedCone ℝ (realified V))
    (hC : IsOpen (C : Set (realified V))) :
    (C : Set (realified V)) ⊆ closure (rationalClosure C) := by
  refine (subset_closure_rationalBoundary C hC).trans (closure_mono ?_)
  intro x hx
  exact mem_rationalClosure.2 (subset_convexHull ℝ (rationalBoundary C) hx)

/-! ### `C ⊆ C₊`

Looijenga, Definition 4.2, p. 17, writes the rational closure of the open cone `C` as `C₊ ⊃ C`.
`subset_closure_rationalClosure` above carries `C ⊆ closure C₊`; this section closes the gap to
`C ⊆ C₊` itself, which is what the cover hypothesis of the support-space theorems needs.

The step is the simplex: a point of the open cone is a convex combination of finitely many
rational points of `C̄`. Around a point `x` of the open cone there is a simplex whose centroid is
`x` and whose vertices are in `C`, and a rational point is taken near each vertex; the barycentric
coordinates of `x` are continuous in the vertices, so `x` is still inside the convex hull of the
approximating rational points, which lie in `C₊`.

Three of the covering lemmas are Mathlib's and are stated for sets in a normed space: an open
set contained in a closure is contained in the interior of the closure (`interior_maximal`), the
affine span of a nonempty open set is everything (`IsOpen.affineSpan_eq_top`), and for a convex
set with nonempty interior the interior of its closure is its interior
(`Convex.interior_closure_eq_interior_of_nonempty_interior`). `L(ℝ)` here carries the module
topology, not a norm, so the argument runs in the coordinate space `Fin n → ℝ` after the
continuous linear equivalence `realified V ≃L[ℝ] (Fin n → ℝ)` — every linear map out of a
finite-dimensional module with the module topology is continuous,
`IsModuleTopology.continuous_of_linearMap`, in particular both directions of the equivalence —
and is transported back along its homeomorphism. This is where the finite dimensionality of `L`
is used: `C ⊆ C₊` is false for a convex cone with empty interior dense in its closure, so no
general-topological argument can give it. -/

/-- **A convex set whose closure contains an open set contains that open set.** The open set
`C'` is contained in the interior of `closure T'`, and the affine span of a nonempty open set is
everything, so `affineSpan T' = ⊤` (an affine subspace of a finite-dimensional space is closed,
so `affineSpan (closure T') ≤ affineSpan T'`); a convex set spanning an affine space has nonempty
interior (`Convex.interior_nonempty_iff_affineSpan_eq_top`), which makes
`interior (closure T') = interior T'`. -/
theorem subset_of_subset_closure_of_convex {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {C' T' : Set E} (hopen : IsOpen C') (hsub : C' ⊆ closure T')
    (hconv : Convex ℝ T') : C' ⊆ T' := by
  intro x hx
  have hsub' : C' ⊆ interior (closure T') := interior_maximal hsub hopen
  have hne : (interior (closure T')).Nonempty := ⟨x, hsub' hx⟩
  have haff₁ : affineSpan ℝ (interior (closure T')) = ⊤ :=
    IsOpen.affineSpan_eq_top isOpen_interior hne
  have haff : affineSpan ℝ (closure T') = ⊤ :=
    top_le_iff.mp (haff₁.ge.trans (affineSpan_mono ℝ interior_subset))
  have hclosed : IsClosed ((affineSpan ℝ T' : AffineSubspace ℝ E) : Set E) :=
    AffineSubspace.isClosed_of_finiteDimensional _
  have hclsub : closure T' ⊆ (affineSpan ℝ T' : Set E) :=
    hclosed.closure_subset_iff.mpr (subset_affineSpan ℝ T')
  have haff' : affineSpan ℝ T' = ⊤ := by
    have hle : affineSpan ℝ (closure T') ≤ affineSpan ℝ T' := by
      rw [← AffineSubspace.affineSpan_coe (affineSpan ℝ T')]
      exact affineSpan_mono ℝ hclsub
    exact top_le_iff.mp (haff.ge.trans hle)
  have hne₂ : (interior T').Nonempty :=
    (Convex.interior_nonempty_iff_affineSpan_eq_top hconv).mpr haff'
  have hEq : interior (closure T') = interior T' :=
    Convex.interior_closure_eq_interior_of_nonempty_interior hconv hne₂
  exact interior_subset (hEq ▸ hsub' hx)

/-- **The open cone lies in its rational closure**, the `C₊ ⊃ C` of Looijenga, Definition 4.2,
p. 17. Transported to `Fin n → ℝ` along `Module.finBasis`, `C` becomes an open set inside the
closure of the convex set `C₊`, and `subset_of_subset_closure_of_convex` closes the gap. -/
theorem subset_rationalClosure (C : PointedCone ℝ (realified V)) [Module.Finite ℚ V]
    (hC : IsOpen (C : Set (realified V))) :
    (C : Set (realified V)) ⊆ (rationalClosure C : Set (realified V)) := by
  classical
  let e : realified V ≃ₗ[ℝ] (Fin (Module.finrank ℝ (realified V)) → ℝ) :=
    (Module.finBasis ℝ (realified V)).equivFun
  have h1 : Continuous e := IsModuleTopology.continuous_of_linearMap e.toLinearMap
  have h2 : Continuous e.symm := IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap
  let E' : realified V ≃L[ℝ] (Fin (Module.finrank ℝ (realified V)) → ℝ) :=
    { e with continuous_toFun := h1, continuous_invFun := h2 }
  have hconv : Convex ℝ (E' '' (rationalClosure C : Set (realified V))) :=
    (rationalClosure C).convex.linear_image E'.toLinearMap
  have hopen : IsOpen (E' '' (C : Set (realified V))) := E'.toHomeomorph.isOpenMap _ hC
  have himg : E' '' closure (rationalClosure C : Set (realified V)) =
      closure (E' '' (rationalClosure C : Set (realified V))) :=
    Homeomorph.image_closure E'.toHomeomorph _
  have hsub : E' '' (C : Set (realified V)) ⊆
      closure (E' '' (rationalClosure C : Set (realified V))) := by
    rw [← himg]
    exact Set.image_mono (subset_closure_rationalClosure C hC)
  have key : E' '' (C : Set (realified V)) ⊆ E' '' (rationalClosure C : Set (realified V)) :=
    subset_of_subset_closure_of_convex hopen hsub hconv
  rintro x hx
  obtain ⟨y, hy, hyx⟩ := key ⟨x, hx, rfl⟩
  rwa [E'.injective hyx] at hy

/-- **The members of a locally rational decomposition cover the open cone**, given that they cover
`C₊`: the cover hypothesis `hcover` of the support-space theorems, discharged through `C ⊆ C₊`. -/
theorem exists_mem_of_mem_of_cover_rationalClosure {C : PointedCone ℝ (realified V)}
    [Module.Finite ℚ V] (hC : IsOpen (C : Set (realified V)))
    {S : Set (PointedCone ℝ (realified V))}
    (hcover : ∀ z ∈ rationalClosure C, ∃ τ ∈ S, z ∈ τ) :
    ∀ z ∈ C, ∃ τ ∈ S, z ∈ τ :=
  fun z hz => hcover z (subset_rationalClosure C hC hz)

/-- Rational closure is monotone under inclusion of the topological closures.
LC-09 (2026-11-19): `content:rationalClosure content:mono` and
`content:convex hull content:monotone content:closure` found no competing declaration or
specialized analogue; the generator-level proof is immediate from `rationalClosure_eq_hull`. -/
theorem rationalClosure_mono {C D : PointedCone ℝ (realified V)}
    (h : C.closure ≤ D.closure) : rationalClosure C ≤ rationalClosure D := by
  rw [rationalClosure_eq_hull C, rationalClosure_eq_hull D]
  apply Submodule.span_mono
  rintro x ⟨hx, hxc⟩
  exact ⟨hx, h hxc⟩

/-- An open cone contained in another cone's closure lies in that other cone's rational closure.
This specializes to the open upper sheet inside the rational closure of `closedSheet`. -/
theorem subset_rationalClosure_of_subset [Module.Finite ℚ V]
    {C D : PointedCone ℝ (realified V)} (hDC : D ≤ C.closure)
    (hDopen : IsOpen (D : Set (realified V))) :
    (D : Set (realified V)) ⊆ (rationalClosure C : Set (realified V)) := by
  intro x hx
  exact rationalClosure_mono
    (closure_minimal hDC (Submodule.isClosed_topologicalClosure C))
    (subset_rationalClosure D hDopen hx)

/-- Looijenga, Definition 4.2, p. 17: a cone is *locally rational* in `C₊` when its
intersection with every rational subcone of `C₊` is rational. -/
def IsLocallyRationalCone (Cplus σ : PointedCone ℝ (realified V)) : Prop :=
  ∀ P : PointedCone ℝ (realified V), IsRationalCone P → P ≤ Cplus → IsRationalCone (σ ⊓ P)

/-- The traces of a family of cones on every rational subcone of `C₊` are locally finite. This
is *not* Looijenga's Definition 4.2 (which asks for a rational cone system, so a finite family,
on every rational subcone); it is the property the semitoric construction of §4-5 uses, kept
here because it is what local finiteness buys. -/
def HasLocallyFiniteTraces (Cplus : PointedCone ℝ (realified V))
    (S : Set (PointedCone ℝ (realified V))) : Prop :=
  ∀ P : PointedCone ℝ (realified V), IsRationalCone P → P ≤ Cplus →
    LocallyFinite fun σ : {σ // σ ∈ S} =>
      ((σ.1 : PointedCone ℝ (realified V)) : Set (realified V)) ∩ (P : Set (realified V))

/-- The *restriction* of a family of cones to a subcone `P`: the traces `σ ⊓ P`
(Looijenga, Definition 4.2, p. 17). -/
def restrictionTo (S : Set (PointedCone ℝ (realified V))) (P : PointedCone ℝ (realified V)) :
    Set (PointedCone ℝ (realified V)) :=
  {τ | ∃ σ ∈ S, τ = σ ⊓ P}

theorem mem_restrictionTo {S : Set (PointedCone ℝ (realified V))}
    {P τ : PointedCone ℝ (realified V)} :
    τ ∈ restrictionTo S P ↔ ∃ σ ∈ S, τ = σ ⊓ P :=
  Iff.rfl

/-- The face-closure of a family of cones: the faces of its members. It is in this form that the
*restriction* of Definition 4.2, p. 17, is read in `IsLocallyRationalDecomposition`; see the
module docstring for why, and `IsLocallyRationalDecompositionTraces` for the literal reading. -/
def faceClosure (S : Set (PointedCone ℝ (realified V))) :
    Set (PointedCone ℝ (realified V)) :=
  {F | ∃ σ ∈ S, F.IsFaceOf σ}

theorem mem_faceClosure {S : Set (PointedCone ℝ (realified V))}
    {F : PointedCone ℝ (realified V)} :
    F ∈ faceClosure S ↔ ∃ σ ∈ S, F.IsFaceOf σ :=
  Iff.rfl

/-- The face-closure of a family is closed under taking faces. -/
theorem isFaceOf_mem_faceClosure {S : Set (PointedCone ℝ (realified V))}
    {F G : PointedCone ℝ (realified V)} (hG : G ∈ faceClosure S) (hFG : F.IsFaceOf G) :
    F ∈ faceClosure S := by
  obtain ⟨σ, hσ, hGσ⟩ := mem_faceClosure.1 hG
  exact mem_faceClosure.2 ⟨σ, hσ, hFG.trans hGσ⟩

/-- Looijenga, Definition 4.2, p. 17: a *locally rational decomposition* of `C₊` is a collection
of convex cones whose union is `C₊` and whose restriction to every rational subcone of `C₊` is
a rational cone system (Definition 4.1, p. 16, so in particular a *finite* set of nondegenerate
rational cones, closed under taking faces and with pairwise intersections along common faces).

**The reading of "the restriction".** The clause of Definition 4.2 (p. 17) reads "the
restriction to every rational subcone of `C₊` is a rational cone system"
(`.tmp-sources/looijenga-math0201218v2.md:481`). The restriction of `Σ` to `P` is taken here
to be the collection of *faces* of the traces `σ ⊓ P`, `σ ∈ Σ`
(`faceClosure (restrictionTo Σ P)`), not the traces themselves. Definition 4.2 has two
readings, and this one is forced by the uses the source makes of it: he asserts (p. 17) that
the facial decomposition `Σ(bb)` is a locally rational decomposition, and with the traces
themselves it is not one — in the setting of
Example 4.3, `P` spanned by two rational points of the open cone is a trace of `Σ(bb)`, a ray of
`P` is a face of `P`, and no trace is that ray, so face-closure fails
(`not_isLocallyRationalDecompositionTraces_facialDecomposition`). With the faces of the traces
the definition holds (`facialDecomposition_isLocallyRational`), and that is what the later
sections use: the source cuts the semitoric extension of §4-5 along the cones of `Σ` and their
faces. The finiteness in Definition 4.1 is not relaxed: a rational subcone `P` has finitely
many faces, and every trace of `Σ` on `P` is one of them, so the face-closure of the traces is
finite. `HasLocallyFiniteTraces` below records local finiteness separately. -/
structure IsLocallyRationalDecomposition (Cplus : PointedCone ℝ (realified V))
    (S : Set (PointedCone ℝ (realified V))) : Prop where
  /-- The union of the members is `C₊`. -/
  union_eq : (⋃ σ ∈ S, (σ : Set (realified V))) = (Cplus : Set (realified V))
  /-- Every member is a locally rational cone in `C₊`. -/
  isLocallyRational : ∀ σ ∈ S, IsLocallyRationalCone Cplus σ
  /-- The restriction to every rational subcone of `C₊` — the faces of the traces — is a
  rational cone system. -/
  restriction : ∀ P : PointedCone ℝ (realified V), IsRationalCone P → P ≤ Cplus →
    IsRationalConeSystem (faceClosure (restrictionTo S P))

/-- Looijenga, Definition 4.2, p. 17, read *literally*: the restriction of `Σ` to a rational
subcone `P` is the family of traces `σ ⊓ P` itself. This is the reading that fails for `Σ(bb)`
(`not_isLocallyRationalDecompositionTraces_facialDecomposition`); it is kept because the
statement that it fails is what settles the reading of `IsLocallyRationalDecomposition`. -/
structure IsLocallyRationalDecompositionTraces (Cplus : PointedCone ℝ (realified V))
    (S : Set (PointedCone ℝ (realified V))) : Prop where
  /-- The union of the members is `C₊`. -/
  union_eq : (⋃ σ ∈ S, (σ : Set (realified V))) = (Cplus : Set (realified V))
  /-- Every member is a locally rational cone in `C₊`. -/
  isLocallyRational : ∀ σ ∈ S, IsLocallyRationalCone Cplus σ
  /-- The traces on every rational subcone of `C₊` are a rational cone system. -/
  restriction : ∀ P : PointedCone ℝ (realified V), IsRationalCone P → P ≤ Cplus →
    IsRationalConeSystem (restrictionTo S P)

/-- The facial decomposition `Σ(bb)` of `C₊`: its faces, `C₊` itself included (Looijenga,
Definition 4.2, p. 17). -/
def facialDecomposition (Cplus : PointedCone ℝ (realified V)) :
    Set (PointedCone ℝ (realified V)) :=
  {σ | σ.IsFaceOf Cplus}

/-- A face of `C₊` intersected with a subcone `P ≤ C₊` is a face of `P`. -/
theorem isFaceOf_inf_of_le {σ P : PointedCone ℝ (realified V)} (hσ : σ.IsFaceOf P) :
    (σ ⊓ P).IsFaceOf P :=
  hσ.inf_left (PointedCone.IsFaceOf.refl P)

/-- A face of `C₊` has rational traces on a rational cone: its intersection with a rational
subcone `P ≤ C₊` is a face of `P`, and faces of rational cones are rational. -/
theorem isLocallyRationalCone_facialDecomposition (Cplus : PointedCone ℝ (realified V))
    {σ : PointedCone ℝ (realified V)} (hσ : σ ∈ facialDecomposition Cplus) :
    IsLocallyRationalCone Cplus σ := by
  intro P hP hPC
  have hface : (σ ⊓ P).IsFaceOf P := by
    refine ⟨inf_le_right, ?_⟩
    intro x y a hx hy ha hxy
    exact ⟨hσ.mem_of_smul_add_mem (hPC hx) (hPC hy) ha hxy.1, hx⟩
  exact hP.of_isFaceOf hface

/-- The facial decomposition covers `C₊`: `C₊` is a face of itself. -/
theorem union_facialDecomposition (Cplus : PointedCone ℝ (realified V)) :
    (⋃ σ ∈ facialDecomposition Cplus, (σ : Set (realified V))) = (Cplus : Set (realified V)) := by
  refine Set.eq_of_subset_of_subset ?_ ?_
  · refine Set.iUnion_subset fun σ => Set.iUnion_subset fun hσ => ?_
    exact hσ.le
  · intro x hx
    exact Set.mem_iUnion.2 ⟨Cplus, Set.mem_iUnion.2 ⟨PointedCone.IsFaceOf.refl Cplus, hx⟩⟩

/-- **A trace of `Σ(bb)` on a rational subcone `P ≤ C₊` is a face of `P`**: it is `σ ⊓ P` for a
face `σ` of `C₊`, and a face of the ambient cone meets a subcone in a face of the subcone. -/
theorem isFaceOf_of_mem_restrictionTo {Cplus P τ : PointedCone ℝ (realified V)} (hPle : P ≤ Cplus)
    (hτ : τ ∈ restrictionTo (facialDecomposition Cplus) P) : τ.IsFaceOf P := by
  obtain ⟨σ, hσ, rfl⟩ := mem_restrictionTo.1 hτ
  refine ⟨inf_le_right, ?_⟩
  intro x y a hx hy ha hxy
  exact ⟨hσ.mem_of_smul_add_mem (hPle hx) (hPle hy) ha hxy.1, hx⟩

/-- `P` itself is a trace of `Σ(bb)` on `P`, through the face `C₊`. -/
theorem mem_restrictionTo_self {Cplus P : PointedCone ℝ (realified V)} (hPle : P ≤ Cplus) :
    P ∈ restrictionTo (facialDecomposition Cplus) P :=
  mem_restrictionTo.2 ⟨Cplus, PointedCone.IsFaceOf.refl Cplus, (inf_eq_right.2 hPle).symm⟩

/-- **Two faces of a cone meet along a face of each**: `F ⊓ G` is a face of `F` when both are
faces of `P`. The face property of `G` in `P` does the work. -/
theorem inf_isFaceOf_of_isFaceOf {F G P : PointedCone ℝ (realified V)}
    (hF : F.IsFaceOf P) (hG : G.IsFaceOf P) : (F ⊓ G).IsFaceOf F := by
  refine ⟨inf_le_left, ?_⟩
  intro x y a hx hy ha hxy
  have hxP : x ∈ P := hF.le hx
  have hyP : y ∈ P := hF.le hy
  have hxG : x ∈ G := hG.mem_of_smul_add_mem hxP hyP ha hxy.2
  have hyG : y ∈ G := by
    refine hG.mem_of_smul_add_smul_mem_right hxP hyP ha zero_lt_one ?_
    simpa using hxy.2
  exact ⟨hx, hxG⟩

/-- **The face-closure of the traces of `Σ(bb)` on a rational subcone is a rational cone
system** (Looijenga, Definition 4.1, p. 16, for the restriction of Definition 4.2, p. 17).
Every trace `σ ⊓ P` of a face `σ` of `C₊` on `P` is a face of `P`
(`isFaceOf_of_mem_restrictionTo`), so the members of the face-closure are faces of `P`; a
rational cone has finitely many faces, each of them a rational cone, and the faces of a salient
cone are salient. -/
theorem isRationalConeSystem_faceClosure_restriction {Cplus P : PointedCone ℝ (realified V)}
    (hsal : (Cplus : ConvexCone ℝ (realified V)).Salient) (hP : IsRationalCone P)
    (hPle : P ≤ Cplus) :
    IsRationalConeSystem (faceClosure (restrictionTo (facialDecomposition Cplus) P)) where
  finite := by
    refine (finite_faces_of_isRationalCone hP).subset ?_
    rintro F ⟨τ, hτ, hFτ⟩
    exact hFτ.trans (isFaceOf_of_mem_restrictionTo hPle hτ)
  salient F hF := by
    obtain ⟨τ, hτ, hFτ⟩ := hF
    exact hsal.anti ((hFτ.trans (isFaceOf_of_mem_restrictionTo hPle hτ)).le.trans hPle)
  isRational F hF := by
    obtain ⟨τ, hτ, hFτ⟩ := hF
    exact hP.of_isFaceOf (hFτ.trans (isFaceOf_of_mem_restrictionTo hPle hτ))
  mem_of_isFaceOf := by
    rintro F G ⟨τ, hτ, hFτ⟩ hGF
    exact mem_faceClosure.2 ⟨P, mem_restrictionTo_self hPle,
      hGF.trans (hFτ.trans (isFaceOf_of_mem_restrictionTo hPle hτ))⟩
  inf_isFaceOf_left := by
    rintro F G ⟨τ, hτ, hFτ⟩ ⟨τ', hτ', hGτ'⟩
    exact inf_isFaceOf_of_isFaceOf (hFτ.trans (isFaceOf_of_mem_restrictionTo hPle hτ))
      (hGτ'.trans (isFaceOf_of_mem_restrictionTo hPle hτ'))

/-- **The facial decomposition `Σ(bb)` is a locally rational decomposition of `C₊`**
(Looijenga, Definition 4.2, p. 17), with the restriction read as the faces of the traces. The
only hypothesis is that `C₊` is nondegenerate, which is what the source asserts of it ("this is
a nondegenerate cone also", p. 17); in the setting of Example 4.3 it is
`IsHyperbolicConeComponent.salient_rationalClosure`. -/
theorem facialDecomposition_isLocallyRational (Cplus : PointedCone ℝ (realified V))
    (hsal : (Cplus : ConvexCone ℝ (realified V)).Salient) :
    IsLocallyRationalDecomposition Cplus (facialDecomposition Cplus) where
  union_eq := union_facialDecomposition Cplus
  isLocallyRational := fun _ hσ => isLocallyRationalCone_facialDecomposition Cplus hσ
  restriction := fun _ hP hPle => isRationalConeSystem_faceClosure_restriction hsal hP hPle

/-- `Σ(bb)` is the coarsest locally rational decomposition: every cone of any locally
rational decomposition of `C₊` lies in a member of `Σ(bb)` (Looijenga, Definition 4.2,
p. 17). -/
theorem facialDecomposition_coarsest (Cplus : PointedCone ℝ (realified V))
    {S : Set (PointedCone ℝ (realified V))} (hS : IsLocallyRationalDecomposition Cplus S) :
    ∀ σ ∈ S, ∃ F ∈ facialDecomposition Cplus, σ ≤ F := by
  intro σ hσ
  refine ⟨Cplus, PointedCone.IsFaceOf.refl Cplus, ?_⟩
  intro x hx
  have hunion : (⋃ σ ∈ S, (σ : Set (realified V))) = (Cplus : Set (realified V)) :=
    hS.union_eq
  have hx' : x ∈ (⋃ σ ∈ S, (σ : Set (realified V))) :=
    Set.mem_iUnion.2 ⟨σ, Set.mem_iUnion.2 ⟨hσ, hx⟩⟩
  rw [hunion] at hx'
  simpa using hx'

/-- **Two members of a locally rational decomposition meet along a common face.** For
`x, y ∈ a` and `a • x + y ∈ a ⊓ b`, choose a rational subcone containing the three points.
The restriction clause applies to that cone, and the common trace's face property returns the
two memberships in `b`. This lifts Definition 4.2's local incidence to `a ⊓ b`. -/
theorem inf_isFaceOf_of_isLocallyRationalDecomposition {C : PointedCone ℝ (realified V)}
    {S : Set (PointedCone ℝ (realified V))} (hS : IsLocallyRationalDecomposition (rationalClosure C) S)
    {a b : PointedCone ℝ (realified V)} (ha : a ∈ S) (hb : b ∈ S) : (a ⊓ b).IsFaceOf a := by
  have hle {c : PointedCone ℝ (realified V)} (hc : c ∈ S) : c ≤ rationalClosure C := by
    intro z hz
    have hz' : z ∈ (⋃ d ∈ S, (d : Set (realified V))) :=
      Set.mem_iUnion.2 ⟨c, Set.mem_iUnion.2 ⟨hc, hz⟩⟩
    rwa [hS.union_eq] at hz'
  refine ⟨inf_le_left, ?_⟩
  intro x y r hx hy hr hxy
  obtain ⟨Kx, hKrx, hKlex, hxK⟩ := exists_rationalCone_le_rationalClosure_and_mem (hle ha hx)
  obtain ⟨Ky, hKry, hKley, hyK⟩ := exists_rationalCone_le_rationalClosure_and_mem (hle ha hy)
  obtain ⟨Kxy, hKrxy, hKlexy, hxyK⟩ :=
    exists_rationalCone_le_rationalClosure_and_mem (hle ha hxy.1)
  let K := Kx ⊔ Ky ⊔ Kxy
  have hxa : x ∈ a := hx
  have hya : y ∈ a := hy
  have hxr : x ∈ K := by
    exact (show Kx ≤ K from
      (le_sup_left : Kx ≤ Kx ⊔ Ky).trans (le_sup_left : Kx ⊔ Ky ≤ K)) hxK
  have hyr : y ∈ K := by
    exact (show Ky ≤ K from
      (le_sup_right : Ky ≤ Kx ⊔ Ky).trans (le_sup_left : Kx ⊔ Ky ≤ K)) hyK
  have hxyr : r • x + y ∈ K := by
    exact (show Kxy ≤ K from le_sup_right : Kxy ≤ K) hxyK
  have hKr : IsRationalCone K := hKrx.sup hKry |>.sup hKrxy
  have hKle : K ≤ rationalClosure C := sup_le (sup_le hKlex hKley) hKlexy
  let R := hS.restriction K hKr hKle
  let A := a ⊓ K
  let B := b ⊓ K
  have hA : A ∈ faceClosure (restrictionTo S K) :=
    mem_faceClosure.2 ⟨A, mem_restrictionTo.2 ⟨a, ha, rfl⟩, PointedCone.IsFaceOf.refl A⟩
  have hB : B ∈ faceClosure (restrictionTo S K) :=
    mem_faceClosure.2 ⟨B, mem_restrictionTo.2 ⟨b, hb, rfl⟩, PointedCone.IsFaceOf.refl B⟩
  have hface : (A ⊓ B).IsFaceOf A := R.inf_isFaceOf_left hA hB
  have hxF := hface.mem_of_smul_add_mem (show x ∈ A from ⟨hxa, hxr⟩)
    (show y ∈ A from ⟨hya, hyr⟩) hr (show r • x + y ∈ A ⊓ B from ⟨⟨hxy.1, hxyr⟩, ⟨hxy.2, hxyr⟩⟩)
  exact ⟨hxF.1.1, hxF.2.1⟩

/-! ## Example 4.3: the facial decomposition against the literal reading of Definition 4.2

Looijenga, Example 4.3, pp. 17-18: `C` is a connected component of the set of `x` with
`x · x > 0`, for a form of signature `(1, dim L - 1)` over `ℚ`. What Definition 4.2 asks of
the facial decomposition `Σ(bb)` is that its restriction to every rational subcone be a
rational cone system, and the source's ground for it is that the faces of `C₊` are `C₊`, the
rays spanned by rational isotropic vectors on the boundary, and `{0}`: a rational subcone
meets only finitely many of those.

What `Σ(bb)` does not have is face-closure. A face of `C₊` that contains a rational
*timelike* point is all of `C₊` (`eq_of_isFaceOf_of_mem_pos`): for a rational point `v` of the
closed cone, a large rational multiple of that timelike point minus `v` is again a rational
point of the open cone, hence lies in `C₊`, and the face relation applied to
`(q • u - v) + v = q • u` forces `v` into the face. Take then a rational cone `P` spanned by
two rational points `u`, `v` of the open cone with `v` not a multiple of `u`. The cone `P` is
itself a trace of `Σ(bb)` (the trace on the face `C₊`), and the ray `ℝ≥0 u` is a face of `P`
(`isFaceOf_hull_singleton`); but a trace `σ ⊓ P` of `Σ(bb)` that contains `u` has `u ∈ σ`, so
`σ = C₊` and the trace is `P`, which is not that ray. So the restriction of `Σ(bb)` to `P`
fails `mem_of_isFaceOf`, and `Σ(bb)` is not a locally rational decomposition when the
restriction is read as the traces themselves
(`not_isLocallyRationalDecompositionTraces_facialDecomposition`).

The failing clause is therefore face-closure, not finiteness: the traces are finitely many and
each is a rational cone, as the source's description of the faces of `C₊` says, and what they
are not closed under is taking faces, which is why the restriction of Definition 4.2 is read in
`IsLocallyRationalDecomposition` as the faces of the traces. -/

section Example43

variable {Q : QuadraticForm ℝ (realified V)} {t : realified V}

/-- The part of Looijenga's Example 4.3, p. 17, hypothesis on `C` — that it is a connected
component of `x · x > 0` for a form of signature `(1, dim L - 1)` — that the argument below
uses: the rational points of the open sheet lie in the closure of `C`, and `Q` is nonnegative
there. (The signature hypothesis enters only through these two consequences, which an actual
component satisfies.) -/
structure IsPositiveConeComponent (C : PointedCone ℝ (realified V))
    (Q : QuadraticForm ℝ (realified V)) (t : realified V) : Prop where
  /-- The rational points of the open sheet lie in the closure of `C`. -/
  open_points : ∀ v : V, 0 < Q (rationalPoint v) →
    0 < (QuadraticMap.associated Q) (rationalPoint v) t → rationalPoint v ∈ C.closure
  /-- `Q` is nonnegative on the closure of `C`. -/
  nonneg : ∀ x ∈ C.closure, 0 ≤ Q x

/-- **A face of `C₊` that contains a rational point of the open sheet is `C₊` itself.** -/
theorem eq_of_isFaceOf_of_mem_pos {C F : PointedCone ℝ (realified V)} {u : V}
    (hC : IsPositiveConeComponent C Q t)
    (hu : 0 < Q (rationalPoint u))
    (hut : 0 < (QuadraticMap.associated Q) (rationalPoint u) t)
    (hF : F.IsFaceOf (rationalClosure C)) (hFu : rationalPoint u ∈ F) :
    F = rationalClosure C := by
  set Qu : ℝ := Q (rationalPoint u) with hQu_def
  set bu : ℝ := (QuadraticMap.associated Q) (rationalPoint u) t with hbu_def
  have hQu : 0 < Qu := hQu_def ▸ hu
  have hbu : 0 < bu := hbu_def ▸ hut
  refine le_antisymm hF.le ?_
  rw [rationalClosure_eq_hull]
  refine Submodule.span_le.2 ?_
  rintro p ⟨⟨v, -, rfl⟩, hvcl⟩
  set b : ℝ := (QuadraticMap.associated Q) (rationalPoint u) (rationalPoint v) with hb_def
  set c : ℝ := (QuadraticMap.associated Q) (rationalPoint v) t with hc_def
  set A : ℝ := 2 * |b| / Qu + 1 with hA_def
  set B : ℝ := (c + 1) / bu with hB_def
  obtain ⟨q, hq⟩ := exists_rat_gt (max A (max B 1))
  have hq1 : (1 : ℝ) ≤ (q : ℝ) :=
    le_trans (le_max_right B 1) (le_trans (le_max_right A (max B 1)) hq.le)
  have hqA : A < (q : ℝ) := lt_of_le_of_lt (le_max_left A (max B 1)) hq
  have hqB : B < (q : ℝ) :=
    lt_of_le_of_lt (le_trans (le_max_left B 1) (le_max_right A (max B 1))) hq
  rw [hA_def] at hqA
  rw [hB_def] at hqB
  have hqpos : (0 : ℚ) < q := by exact_mod_cast lt_of_lt_of_le zero_lt_one hq1
  set z : realified V := rationalPoint (q • u - v) with hz_def
  have hzrep : z = (q : ℝ) • rationalPoint u - rationalPoint v := by
    rw [hz_def, map_sub, rationalPoint_rat_smul]
  have hQv : 0 ≤ Q (rationalPoint v) := hC.nonneg _ hvcl
  have hQz : 0 < Q z := by
    have hrep2 : z = (q : ℝ) • rationalPoint u + (-1 : ℝ) • rationalPoint v := by
      rw [hzrep, sub_eq_add_neg]
      congr 1
      exact (neg_one_smul ℝ (rationalPoint v)).symm
    have h1 : 2 * |b| + Qu ≤ (q : ℝ) * Qu := by
      have h2 : 2 * |b| / Qu < (q : ℝ) - 1 := by linarith
      have h4 : 2 * |b| / Qu * Qu < ((q : ℝ) - 1) * Qu := mul_lt_mul_of_pos_right h2 hQu
      have h5 : 2 * |b| / Qu * Qu = 2 * |b| := by field_simp
      rw [h5] at h4
      nlinarith
    have hbq : 2 * (q : ℝ) * b ≤ 2 * (q : ℝ) * |b| := by
      have h0 : (0 : ℝ) ≤ 2 * (q : ℝ) := by linarith
      nlinarith [le_abs_self b]
    have hexp : Q z = (q : ℝ) ^ 2 * Q (rationalPoint u) - 2 * (q : ℝ) * b
        + Q (rationalPoint v) := by
      rw [hrep2, quadratic_expand, hb_def]
      ring
    rw [hexp]
    nlinarith [h1, hbq, hQv, hq1, hQu]
  have hbz : 0 < (QuadraticMap.associated Q) z t := by
    have hstep : (QuadraticMap.associated Q) z
        = (q : ℝ) • (QuadraticMap.associated Q) (rationalPoint u)
          - (QuadraticMap.associated Q) (rationalPoint v) := by
      rw [hzrep, map_sub, map_smul]
    have h1 : c < (q : ℝ) * bu := by
      rw [div_lt_iff₀ hbu] at hqB
      linarith
    rw [hstep, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
    have hgoal : (q : ℝ) * ((QuadraticMap.associated Q) (rationalPoint u) t)
        - (QuadraticMap.associated Q) (rationalPoint v) t = (q : ℝ) * bu - c := by
      rw [hbu_def, hc_def]
    rw [hgoal]
    linarith
  have hzC : z ∈ rationalClosure C := by
    rw [mem_rationalClosure, hz_def]
    exact subset_convexHull ℝ _ ⟨⟨q • u - v, Set.mem_univ _, rfl⟩,
      hC.open_points _ (by rw [← hz_def]; exact hQz) (by rw [← hz_def]; exact hbz)⟩
  have hpC : rationalPoint v ∈ rationalClosure C := by
    rw [mem_rationalClosure]
    exact subset_convexHull ℝ _ ⟨⟨v, Set.mem_univ v, rfl⟩, hvcl⟩
  have hsum : z + rationalPoint v ∈ F := by
    have heq : z + rationalPoint v = (q : ℝ) • rationalPoint u := by
      rw [hzrep]
      abel
    rw [heq]
    exact PointedCone.smul_mem _ (by linarith) hFu
  exact ((hF.add_mem_iff_mem hzC hpC).mp hsum).2

/-- A functional nonnegative on two points is nonnegative on their cone. -/
theorem nonneg_of_mem_hull_pair {m : (realified V) →ₗ[ℝ] ℝ} {x y z : realified V}
    (hx : 0 ≤ m x) (hy : 0 ≤ m y)
    (hz : z ∈ PointedCone.hull ℝ ({x, y} : Set (realified V))) : 0 ≤ m z := by
  induction hz using Submodule.span_induction with
  | mem w hw =>
    rcases Set.mem_insert_iff.1 hw with rfl | hw
    · exact hx
    · rw [Set.mem_singleton_iff] at hw
      exact hw ▸ hy
  | zero =>
    rw [map_zero]
  | add u v _ _ hu hv =>
    rw [map_add]
    linarith
  | smul c u _ hu =>
    have hcu : c • u = c.1 • u := rfl
    rw [hcu, map_smul, smul_eq_mul]
    exact mul_nonneg c.2 hu

/-- A real linear functional vanishing on `x` and taking the value `1` at `y`, when `y` is not a
multiple of `x`. -/
theorem exists_dual_eq_zero_of_notMem {x y : realified V}
    (hy : y ∉ Submodule.span ℝ ({x} : Set (realified V))) :
    ∃ m : (realified V) →ₗ[ℝ] ℝ, m x = 0 ∧ m y = 1 := by
  obtain ⟨f, hfy, hfker⟩ :=
    Submodule.exists_dual_map_eq_bot_of_notMem (p := Submodule.span ℝ ({x} : Set (realified V)))
      hy (inferInstance : Module.Projective ℝ
        ((realified V) ⧸ Submodule.span ℝ ({x} : Set (realified V))))
  have hfx : f x = 0 := by
    have hmem : f x ∈ (Submodule.span ℝ ({x} : Set (realified V))).map f :=
      ⟨x, Submodule.subset_span (by simp), rfl⟩
    rw [hfker] at hmem
    simpa using hmem
  refine ⟨(f y)⁻¹ • f, ?_, ?_⟩
  · simp [hfx]
  · simp [hfy]

/-- **The ray through `x` is a face of the cone spanned by `x` and `y`** when `y` is not a
multiple of `x`: applying the `y`-coordinate functional to `a • p + q` shows that the
`y`-coordinate of `p` vanishes, and both coordinates of `p` are nonnegative. -/
theorem isFaceOf_hull_singleton {x y : realified V} (hx0 : x ≠ 0)
    (hy : y ∉ Submodule.span ℝ ({x} : Set (realified V))) :
    (PointedCone.hull ℝ ({x} : Set (realified V))).IsFaceOf
      (PointedCone.hull ℝ ({x, y} : Set (realified V))) where
  le := Submodule.span_le.2 fun z hz => PointedCone.subset_hull (by
    rcases Set.mem_singleton_iff.1 hz with rfl
    exact Set.mem_insert _ _)
  mem_of_smul_add_mem := by
    obtain ⟨m, hmx, hmy⟩ := exists_dual_eq_zero_of_notMem hy
    have hxnotin : x ∉ Submodule.span ℝ ({y} : Set (realified V)) := by
      intro hxspan
      obtain ⟨cc, hcc⟩ := Submodule.mem_span_singleton.1 hxspan
      apply hy
      rcases eq_or_ne cc 0 with hc0 | hc0
      · rw [hc0, zero_smul] at hcc
        exact absurd hcc.symm hx0
      · rw [Submodule.mem_span_singleton]
        exact ⟨cc⁻¹, by rw [← hcc, smul_smul, inv_mul_cancel₀ hc0, one_smul]⟩
    obtain ⟨l, hly, hlx⟩ := exists_dual_eq_zero_of_notMem hxnotin
    have hxl : l x = 1 := hlx
    intro p q a hp hq ha hsum
    have hmp : 0 ≤ m p :=
      nonneg_of_mem_hull_pair (m := m) (x := x) (y := y)
        (by simp [hmx]) (by simp [hmy]) hp
    have hmq : 0 ≤ m q :=
      nonneg_of_mem_hull_pair (m := m) (x := x) (y := y)
        (by simp [hmx]) (by simp [hmy]) hq
    have hzero : a * m p + m q = 0 := by
      have hsumspan : a • p + q ∈ Submodule.span ℝ ({x} : Set (realified V)) :=
        PointedCone.hull_le_span ℝ _ hsum
      obtain ⟨cc, hcc⟩ := Submodule.mem_span_singleton.1 hsumspan
      have h1 : m (a • p + q) = a * m p + m q := by
        rw [map_add, map_smul, smul_eq_mul]
      have h2 : m (a • p + q) = 0 := by
        rw [← hcc, map_smul, hmx, smul_eq_mul, mul_zero]
      linarith
    have hmp0 : m p = 0 := by nlinarith
    obtain ⟨a₁, b₁, ha₁⟩ := Submodule.mem_span_pair.1
      (PointedCone.hull_le_span ℝ _ hp : p ∈ Submodule.span ℝ ({x, y} : Set (realified V)))
    have hb₁ : b₁ = 0 := by
      have h1 : m p = a₁ * m x + b₁ * m y := by
        rw [← ha₁, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
      simp only [hmx, hmy, mul_zero, mul_one] at h1
      rw [hmp0] at h1
      simpa using h1.symm
    have ha₁nonneg : 0 ≤ a₁ := by
      have h2 := nonneg_of_mem_hull_pair (m := l) (x := x) (y := y)
        (by simp [hxl]) (by simp [hly]) hp
      rw [← ha₁, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul, hxl, hly] at h2
      simpa using h2
    rw [← ha₁, hb₁, zero_smul, add_zero]
    exact PointedCone.smul_mem _ ha₁nonneg (PointedCone.subset_hull (by simp))

/-- **`Σ(bb)` is not a locally rational decomposition of `C₊` in the setting of Example 4.3**,
with Definition 4.2 read literally, the restriction being the traces themselves. The rational
cone `P` spanned by two rational points `u`, `v` of the open sheet has only `P` and `{0}` among
its traces on `Σ(bb)`, and the ray through `u` — a face of `P`, not a trace, and not `P` — is
what the face-closure clause of Definition 4.1 asks for. This is what settles the reading of
Definition 4.2 in favour of `IsLocallyRationalDecomposition`. -/
theorem not_isLocallyRationalDecompositionTraces_facialDecomposition
    {C : PointedCone ℝ (realified V)} (hC : IsPositiveConeComponent C Q t)
    {u v : V} (hu : 0 < Q (rationalPoint u))
    (hut : 0 < (QuadraticMap.associated Q) (rationalPoint u) t)
    (hv : 0 < Q (rationalPoint v))
    (hvt : 0 < (QuadraticMap.associated Q) (rationalPoint v) t)
    (hindep : rationalPoint v ∉ Submodule.span ℝ ({rationalPoint u} : Set (realified V))) :
    ¬ IsLocallyRationalDecompositionTraces (rationalClosure C)
      (facialDecomposition (rationalClosure C)) := by
  classical
  intro h
  have huC : rationalPoint u ∈ rationalClosure C := by
    rw [mem_rationalClosure]
    exact subset_convexHull ℝ _ ⟨⟨u, Set.mem_univ u, rfl⟩, hC.open_points u hu hut⟩
  have hvC : rationalPoint v ∈ rationalClosure C := by
    rw [mem_rationalClosure]
    exact subset_convexHull ℝ _ ⟨⟨v, Set.mem_univ v, rfl⟩, hC.open_points v hv hvt⟩
  set P : PointedCone ℝ (realified V) :=
    PointedCone.hull ℝ ({rationalPoint u, rationalPoint v} : Set (realified V)) with hPdef
  have hPle : P ≤ rationalClosure C := by
    refine Submodule.span_le.2 ?_
    intro z hz
    rcases Set.mem_insert_iff.1 hz with rfl | hz
    · exact huC
    · rw [Set.mem_singleton_iff] at hz
      exact hz ▸ hvC
  have hPrat : IsRationalCone P := by
    refine ⟨({u, v} : Finset V), ?_⟩
    rw [hPdef]
    congr 1
    ext z
    simp
  have hsys := h.restriction P hPrat hPle
  have hPmem : P ∈ restrictionTo (facialDecomposition (rationalClosure C)) P :=
    ⟨rationalClosure C, PointedCone.IsFaceOf.refl _, (inf_eq_right.2 hPle).symm⟩
  have hx0 : rationalPoint u ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hu
    exact lt_irrefl 0 hu
  have hrayface : (PointedCone.hull ℝ ({rationalPoint u} : Set (realified V))).IsFaceOf P :=
    isFaceOf_hull_singleton hx0 hindep
  have hraymem := hsys.mem_of_isFaceOf hPmem hrayface
  obtain ⟨σ, hσ, heq⟩ := mem_restrictionTo.1 hraymem
  have huσ : rationalPoint u ∈ σ := by
    have hmem : rationalPoint u ∈ PointedCone.hull ℝ ({rationalPoint u} : Set (realified V)) :=
      PointedCone.subset_hull (by simp)
    rw [heq] at hmem
    exact hmem.1
  have hσtop : σ = rationalClosure C :=
    eq_of_isFaceOf_of_mem_pos hC hu hut hσ huσ
  have hrayeq : PointedCone.hull ℝ ({rationalPoint u} : Set (realified V)) = P := by
    rw [heq, hσtop, inf_eq_right.2 hPle]
  have hvray : rationalPoint v ∈ PointedCone.hull ℝ ({rationalPoint u} : Set (realified V)) := by
    rw [hrayeq]
    exact PointedCone.subset_hull (by simp)
  exact hindep (PointedCone.hull_le_span ℝ _ hvray)

end Example43

/-! ## Continuity of a quadratic form on a finite-dimensional module

LC-09 (2026-11-19): `content:Continuous content:QuadraticMap` and
`content:finite dimensional quadratic form continuous` found only specialized smooth Hessian
material, not a module-topology statement. The proof uses the matrix of the associated bilinear
form: basis coordinates are continuous by `IsModuleTopology.continuous_of_linearMap`, and after
that expansion every summand is a product of continuous real-valued functions.
-/

namespace LinearMap

/-- A bilinear form on a finite-dimensional real module is jointly continuous in the module
topology. -/
theorem continuous_bilin_of_moduleTopology {E : Type*} [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] [IsModuleTopology ℝ E] [Module.Finite ℝ E]
    (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) : Continuous (fun x : E × E => B x.1 x.2) := by
  let b := Module.finBasis ℝ E
  let A := LinearMap.BilinForm.toMatrix b B
  have hb : Continuous b.equivFun := IsModuleTopology.continuous_of_linearMap b.equivFun.toLinearMap
  have hdot : Continuous (fun p : (Fin (Module.finrank ℝ E) → ℝ) ×
      (Fin (Module.finrank ℝ E) → ℝ) => dotProduct p.1 (Matrix.mulVec A p.2)) := by
    unfold dotProduct Matrix.mulVec
    fun_prop
  have h := hdot.comp (hb.prodMap hb)
  refine Continuous.congr h fun x => ?_
  exact (LinearMap.BilinForm.apply_eq_dotProduct_toMatrix_mulVec b B x.1 x.2).symm

end LinearMap

namespace QuadraticMap

/-- A quadratic form on a finite-dimensional real module is continuous in the module topology. -/
theorem continuous_of_moduleTopology {E : Type*} [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] [IsModuleTopology ℝ E] [Module.Finite ℝ E]
    (Q : QuadraticForm ℝ E) : Continuous Q := by
  have h := (LinearMap.continuous_bilin_of_moduleTopology (associated Q)).comp
    (continuous_id.prodMk continuous_id)
  refine Continuous.congr h fun x => ?_
  change (associated Q) x x = Q x
  exact associated_self_apply (Q := Q) x

end QuadraticMap

set_option maxHeartbeats 600000 in
-- The finite-basis expansion also elaborates the two preimage intersections.
/-- The upper sheet of a quadratic form is open in the finite-dimensional module topology. -/
theorem isOpen_positiveCone_upper_of_moduleTopology {E : Type*} [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] [IsModuleTopology ℝ E] [Module.Finite ℝ E]
    (Q : QuadraticForm ℝ E) (t : E) : IsOpen (positiveCone.upper Q t) := by
  have hQ : IsOpen (Q ⁻¹' Set.Ioi (0 : ℝ)) :=
    isOpen_Ioi.preimage (QuadraticMap.continuous_of_moduleTopology Q)
  have hpair : Continuous (fun x : E => (associated Q) x t) :=
    (LinearMap.continuous_bilin_of_moduleTopology (associated Q)).comp
      (continuous_id.prodMk continuous_const)
  have hB : IsOpen ((fun x : E => (associated Q) x t) ⁻¹' Set.Ioi (0 : ℝ)) :=
    isOpen_Ioi.preimage hpair
  show IsOpen {x : E | 0 < Q x ∧ 0 < (associated Q) x t}
  exact hQ.inter hB

/-! ## The hyperbolic setting of Example 4.3, pp. 17-18

Looijenga, Example 4.3, pp. 17-18 (`.tmp-sources/looijenga-math0201218v2.md:487`): `C` is a
connected component of the set of `x` with `x · x > 0`,
for a *nondegenerate* symmetric bilinear form of hyperbolic signature `(1, dim L − 1)` defined
over `ℚ`, and `Γ` an arithmetic subgroup of `O(L(ℚ))` preserving `C`. The closed component —
the sheet cut out by a fixed positive vector `t` — is a cone (`closedSheet`), and it is salient
(`closedSheet_salient`): a vector with `Q x = 0` and `x ⊥ t` must vanish, since `t^⊥` is
negative definite for a nondegenerate form of signature `(1, dim − 1)` and no two-dimensional
subspace is positive definite. That salience is what makes `C₊` a nondegenerate cone, the
hypothesis of `facialDecomposition_isLocallyRational`, in this setting
(`salient_rationalClosure`).

The topological input is the continuity of `Q` on the real form `L(ℝ)`: `C₊` is the hull of
`L(ℚ) ∩ C̄`, so it lies on the sheet as soon as the rational points of `C̄` satisfy its two
defining inequalities. The earlier statements retain the hypothesis `hcl` of
`salient_rationalClosure`, stated at the rational points where it is used. The section above now
supplies that continuity by a finite-basis matrix expansion
(`QuadraticMap.continuous_of_moduleTopology`), and
`isOpen_positiveCone_upper_of_moduleTopology` packages the openness of the upper sheet. Earlier
`hcl` signatures are left intact; the new theorem means no such hypothesis is needed in the final
support-space theorem below. -/

section Hyperbolic

variable [Module.Finite ℚ V]

omit [Module.Finite ℚ V] in
/-- A point of the closed sheet, pushed a positive amount towards `t`, lies in the open sheet:
this is what makes the closed sheet a cone. -/
theorem mem_upper_add_smul {Q : QuadraticForm ℝ (realified V)} {t z : realified V} {ε : ℝ}
    (hε : 0 < ε) (hQz : 0 ≤ Q z) (hzt : 0 ≤ (associated Q) z t) (ht : 0 < Q t) :
    z + ε • t ∈ positiveCone.upper Q t := by
  refine ⟨?_, ?_⟩
  · have hexp := quadratic_expand Q 1 ε z t
    simp only [one_smul, one_pow, one_mul] at hexp
    rw [hexp]
    nlinarith [mul_nonneg hε.le hzt, mul_pos hε ht, hQz]
  · have hsz : (associated Q) (z + ε • t) t = (associated Q) z t + ε * Q t := by
      rw [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
        associated_self_apply]
    rw [hsz]
    nlinarith

/-- **Two points of the closed sheet pair nonnegatively**: pushing both towards the positive
vector `t` puts them in the open sheet, where the form of signature `(1, dim − 1)` pairs points
of the same sheet positively (`associated_pos_of_mem_upper`). -/
theorem nonneg_associated_of_mem_closedSheet {Q : QuadraticForm ℝ (realified V)}
    (hpos : sigPos Q = 1) {t : realified V} (ht : 0 < Q t) {x y : realified V}
    (hx : 0 ≤ Q x) (hxt : 0 ≤ (associated Q) x t) (hy : 0 ≤ Q y)
    (hyt : 0 ≤ (associated Q) y t) : 0 ≤ (associated Q) x y := by
  by_contra hcon
  have hcon : (associated Q) x y < 0 := not_le.mp hcon
  set A := (associated Q) x y with hA
  set c := (associated Q) x t + (associated Q) y t with hc
  have hev : ∀ᶠ ε : ℝ in 𝓝 (0 : ℝ), A + ε * c + ε ^ 2 * Q t < 0 := by
    have hcont : ContinuousAt (fun ε : ℝ => A + ε * c + ε ^ 2 * Q t) 0 := by fun_prop
    have h0 : A + 0 * c + 0 ^ 2 * Q t = A := by ring
    have hmem : A + 0 * c + 0 ^ 2 * Q t ∈ Set.Iio (0 : ℝ) := by
      rw [h0]; exact hcon
    simpa using hcont.eventually (isOpen_Iio.mem_nhds hmem)
  obtain ⟨ε, hlt, hεpos⟩ := ((hev.filter_mono nhdsWithin_le_nhds).and
    (self_mem_nhdsWithin (s := Set.Ioi (0 : ℝ)))).exists
  have hxup := mem_upper_add_smul (Q := Q) hεpos hx hxt ht
  have hyup := mem_upper_add_smul (Q := Q) hεpos hy hyt ht
  have hpos' := associated_pos_of_mem_upper Q hpos ht hxup hyup
  have hexp : (associated Q) (x + ε • t) (y + ε • t) = A + ε * c + ε ^ 2 * Q t := by
    have h1 : (associated Q) (x + ε • t) (y + ε • t)
        = (associated Q) x y + ε * ((associated Q) x t) + ε * ((associated Q) y t)
          + ε ^ 2 * Q t := by
      simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
        associated_self_apply, associated_comm Q t]
      ring
    rw [h1, hA, hc]
    ring
  rw [hexp] at hpos'
  linarith

/-- **A vector of the closed sheet perpendicular to `t` is zero**: `t^⊥` is negative definite
for a nondegenerate form of signature `(1, dim − 1)`, so a *nonvanishing* `x ⊥ t` with
`Q x = 0` would, together with a vector pairing nontrivially with it, span a
two-dimensional positive definite subspace, which `sigPos Q = 1` forbids. -/
theorem eq_zero_of_perp_of_quadratic_eq_zero {Q : QuadraticForm ℝ (realified V)}
    (hpos : sigPos Q = 1) (hnd : Q.Nondegenerate) {t x : realified V} (ht : 0 < Q t)
    (hxt : (associated Q) x t = 0) (hQx : Q x = 0) : x = 0 := by
  by_contra hx0
  have hxrad : x ∉ Q.radical := by
    intro hmem
    rw [QuadraticMap.Nondegenerate.radical_eq_bot hnd] at hmem
    exact hx0 (by simpa using hmem)
  rw [QuadraticMap.mem_radical_iff'] at hxrad
  have hBex : ∃ z : realified V, (associated Q) x z ≠ 0 := by
    by_contra h
    push Not at h
    refine hxrad ⟨hQx, fun n => ?_⟩
    have hexp := quadratic_expand Q 1 1 x n
    simp only [one_smul, one_pow, one_mul] at hexp
    rw [hexp, h n, hQx]
    ring
  obtain ⟨z, hz⟩ := hBex
  set z' := z - ((associated Q) z t / Q t) • t with hz'
  have hxzt : (associated Q) x z' = (associated Q) x z := by
    rw [hz']
    simp only [map_sub, map_smul, smul_eq_mul, hxt, mul_zero, sub_zero]
  have hzxt : (associated Q) z' t = 0 := by
    rw [hz']
    simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul,
      associated_self_apply]
    field_simp
    ring
  have hxzt0 : (associated Q) x z' ≠ 0 := by rw [hxzt]; exact hz
  set lam : ℝ := (|Q z'| + 1) / (2 * (associated Q) x z') with hlam
  have hlamB : lam * (associated Q) x z' = (|Q z'| + 1) / 2 := by
    rw [hlam]; field_simp
  set p := lam • x + z' with hp
  have hpQ : 0 < Q p := by
    have hexp := quadratic_expand Q lam 1 x z'
    simp only [one_smul, one_pow, one_mul] at hexp
    rw [hp, hexp, hQx]
    have hlamB' : (associated Q) x z' * lam = (|Q z'| + 1) / 2 := by
      rw [mul_comm, hlamB]
    have h2 : 2 * (associated Q) x z' * lam = |Q z'| + 1 := by linarith
    nlinarith [abs_nonneg (Q z'), le_abs_self (Q z'), neg_abs_le (Q z')]
  have hpt : (associated Q) p t = 0 := by
    rw [hp, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, hxt,
      hzxt]
    ring
  have hp0 : p ≠ 0 := by
    intro h
    rw [h] at hpQ
    simp at hpQ
  have ht0 : t ≠ 0 := by
    intro h
    rw [h] at ht
    simp at ht
  have hPD : (Q.restrict (Submodule.span ℝ ({t, p} : Set (realified V)))).PosDef := by
    intro v hv
    obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.mp v.2
    rw [QuadraticMap.restrict_apply, ← hab, quadratic_expand Q a b t p, associated_comm Q t p,
      hpt]
    have hv' : ¬ (a = 0 ∧ b = 0) := by
      rintro ⟨rfl, rfl⟩
      exact hv (Subtype.ext (by rw [← hab]; simp))
    rcases eq_or_ne a 0 with ha | ha
    · rw [ha]
      have hb : b ≠ 0 := by rintro rfl; exact hv' ⟨ha, rfl⟩
      nlinarith [sq_pos_of_ne_zero hb, hpQ]
    · nlinarith [sq_pos_of_ne_zero ha, sq_nonneg b, ht, hpQ,
        mul_pos ht (sq_pos_of_ne_zero ha)]
  have hdim : Module.finrank ℝ (Submodule.span ℝ ({t, p} : Set (realified V))) ≤ 1 :=
    (le_sigPos_of_posDef (Q := Q) hPD).trans hpos.le
  have hsingle : Module.finrank ℝ (Submodule.span ℝ ({t} : Set (realified V))) = 1 := by
    rw [finrank_span_singleton]
    exact ht0
  have hspan : Submodule.span ℝ ({t} : Set (realified V))
      = Submodule.span ℝ ({t, p} : Set (realified V)) := by
    refine Submodule.eq_of_le_of_finrank_le ?_ ?_
    · exact Submodule.span_mono (Set.singleton_subset_iff.mpr (Set.mem_insert_iff.mpr (Or.inl rfl)))
    · rw [hsingle]; exact hdim
  have hp_mem : p ∈ Submodule.span ℝ ({t} : Set (realified V)) := by
    rw [hspan]
    exact Submodule.subset_span (Set.mem_insert_iff.mpr (Or.inr rfl))
  obtain ⟨cc, hcc⟩ := Submodule.mem_span_singleton.mp hp_mem
  have hct : (associated Q) p t = cc * Q t := by
    rw [← hcc, map_smul, LinearMap.smul_apply, smul_eq_mul, associated_self_apply]
  rw [hpt] at hct
  have hcc0 : cc = 0 := by
    rcases mul_eq_zero.mp hct.symm with h | h
    · exact h
    · exact absurd h ht.ne'
  rw [hcc0, zero_smul] at hcc
  exact hp0 hcc.symm

/-- **The normal of a `ℚ`-hyperplane through a timelike vector is spacelike**: for a nondegenerate
form of signature `(1, dim − 1)` over `ℝ`, a nonzero `l` whose hyperplane contains a positive vector
`x` has `Q l < 0`. This is step (i) of the arithmetic argument in the module docstring — a
`ℚ`-hyperplane that *meets* `C` has a spacelike normal, so its value `l · l` is negative — stated
for an arbitrary pair rather than for a cone: `Q l > 0` is excluded by `mul_self_le_associated_sq`
(`Q l * Q x ≤ ((associated Q) l x) ^ 2 = 0` with `0 < Q x`), and `Q l = 0` by
`eq_zero_of_perp_of_quadratic_eq_zero`, which makes `l` itself vanish. -/
theorem neg_quadratic_of_associated_eq_zero {Q : QuadraticForm ℝ (realified V)}
    (hpos : sigPos Q = 1) (hnd : Q.Nondegenerate) {l x : realified V} (hl : l ≠ 0)
    (hx : 0 < Q x) (hxl : (associated Q) l x = 0) : Q l < 0 := by
  have hle : Q l ≤ 0 := by
    have h := mul_self_le_associated_sq (Q := Q) hpos hx l
    rw [hxl] at h
    nlinarith
  rcases lt_or_eq_of_le hle with h | h
  · exact h
  · exact absurd (eq_zero_of_perp_of_quadratic_eq_zero (Q := Q) (t := x) (x := l) hpos hnd hx
      hxl h) hl

/-- **The closed sheet** of the light cone of a form of signature `(1, dim − 1)` at a positive
vector `t`: the vectors with `0 ≤ Q x` and `0 ≤ x · t`. It is the closure of the connected
component of `{x | 0 < Q x}` containing `t`, carried as a cone. -/
noncomputable def closedSheet (Q : QuadraticForm ℝ (realified V)) {t : realified V}
    (hpos : sigPos Q = 1) (ht : 0 < Q t) : PointedCone ℝ (realified V) where
  carrier := {x | 0 ≤ Q x ∧ 0 ≤ (associated Q) x t}
  zero_mem' := by simp
  add_mem' {x y} hx hy := by
    refine ⟨?_, ?_⟩
    · have hexp := quadratic_expand Q 1 1 x y
      simp only [one_smul, one_pow, one_mul] at hexp
      rw [hexp]
      have := nonneg_associated_of_mem_closedSheet hpos ht hx.1 hx.2 hy.1 hy.2
      nlinarith [hx.1, hy.1]
    · have h : (associated Q) (x + y) t = (associated Q) x t + (associated Q) y t := by
        rw [map_add, LinearMap.add_apply]
      rw [h]; linarith [hx.2, hy.2]
  smul_mem' c x hx := by
    refine ⟨?_, ?_⟩
    · rw [← Nonneg.coe_smul, QuadraticMap.map_smul, smul_eq_mul]
      exact mul_nonneg (mul_self_nonneg (c : ℝ)) hx.1
    · rw [← Nonneg.coe_smul, map_smul, LinearMap.smul_apply, smul_eq_mul]
      exact mul_nonneg c.2 hx.2

theorem mem_closedSheet {Q : QuadraticForm ℝ (realified V)} {t : realified V}
    (hpos : sigPos Q = 1) (ht : 0 < Q t) {x : realified V} :
    x ∈ closedSheet Q hpos ht ↔ 0 ≤ Q x ∧ 0 ≤ (associated Q) x t :=
  Iff.rfl

/-- **A null form is one-signed on the closed sheet**: an isotropic `u` of the sheet takes a value
of one sign on all of it, `0 ≤ (associated Q) u x`. This is the mechanism that bounds the counting
lemma below at an isotropic generator `w` of a rational cone: a direction `u` with `Q u = 0` cannot
separate two points of `C₊`, so the normals far along `u` do not cut the cone. -/
theorem nonneg_associated_of_quadratic_eq_zero_of_mem_closedSheet
    {Q : QuadraticForm ℝ (realified V)} (hpos : sigPos Q = 1) {t : realified V} (ht : 0 < Q t)
    {u x : realified V} (hu : Q u = 0) (hut : 0 ≤ (associated Q) u t)
    (hx : x ∈ closedSheet Q hpos ht) : 0 ≤ (associated Q) u x :=
  nonneg_associated_of_mem_closedSheet (Q := Q) hpos ht (le_of_eq hu.symm) hut hx.1 hx.2

/-- The open sheet lies on the closed sheet. -/
theorem subset_closedSheet {Q : QuadraticForm ℝ (realified V)} {t : realified V}
    (hpos : sigPos Q = 1) (ht : 0 < Q t) :
    positiveCone.upper Q t ⊆ (closedSheet Q hpos ht : Set (realified V)) :=
  fun _ hx => ⟨hx.1.le, hx.2.le⟩

/-- The open upper sheet with its cone apex adjoined. Positivity of pairings on the sheet proves
the addition law; positive scaling preserves the two defining strict inequalities. LC-09:
`content:convex open cone zero` and `content:PointedCone insert zero` found geometric coning APIs,
but no declaration for this pointed-cone wrapper. -/
noncomputable def positiveCone.upperZero {Q : QuadraticForm ℝ (realified V)}
    (hpos : sigPos Q = 1) {t : realified V} (ht : 0 < Q t) :
    PointedCone ℝ (realified V) where
  carrier := insert 0 (positiveCone.upper Q t)
  zero_mem' := Or.inl rfl
  add_mem' {x y} hx hy := by
    rcases hx with rfl | hx
    · rw [zero_add]
      exact hy
    rcases hy with rfl | hy
    · rw [add_zero]
      exact Or.inr hx
    right
    have hpair : 0 < (associated Q) x y := associated_pos_of_mem_upper Q hpos ht hx hy
    constructor
    · rw [show x + y = (1 : ℝ) • x + (1 : ℝ) • y by simp, quadratic_expand]
      nlinarith [hx.1, hy.1]
    · rw [map_add, LinearMap.add_apply]
      exact add_pos hx.2 hy.2
  smul_mem' c x hx := by
    rcases eq_or_lt_of_le c.2 with hc | hc
    · have hc0 : c = (0 : Nonneg ℝ) := Subtype.ext hc.symm
      simp [hc0]
    · rcases hx with rfl | hx
      · exact Or.inl rfl
      · right
        constructor
        · rw [← Nonneg.coe_smul, QuadraticMap.map_smul, smul_eq_mul]
          exact mul_pos (mul_pos hc hc) hx.1
        · rw [← Nonneg.coe_smul, map_smul, LinearMap.smul_apply, smul_eq_mul]
          exact mul_pos hc hx.2

/-- Membership in the pointed upper sheet is either the apex or membership in the open sheet. -/
@[simp] theorem mem_upperZero {Q : QuadraticForm ℝ (realified V)}
    {hpos : sigPos Q = 1} {t : realified V} {ht : 0 < Q t} {x : realified V} :
    x ∈ positiveCone.upperZero hpos ht ↔ x = 0 ∨ x ∈ positiveCone.upper Q t := Iff.rfl

/-- The pointed upper sheet lies in the closed sheet. -/
theorem upperZero_le_closedSheet {Q : QuadraticForm ℝ (realified V)}
    (hpos : sigPos Q = 1) {t : realified V} (ht : 0 < Q t) :
    positiveCone.upperZero hpos ht ≤ closedSheet Q hpos ht := by
  intro x hx
  rcases hx with rfl | hx
  · exact zero_mem _
  · exact subset_closedSheet hpos ht hx

/-- The open upper sheet is contained in the interior of its pointed version. -/
theorem upper_subset_interior_upperZero {Q : QuadraticForm ℝ (realified V)}
    (hpos : sigPos Q = 1) {t : realified V} (ht : 0 < Q t) :
    positiveCone.upper Q t ⊆ interior (positiveCone.upperZero hpos ht) := by
  apply interior_maximal
  · exact fun x hx => Set.mem_insert_iff.mpr (Or.inr hx)
  · exact isOpen_positiveCone_upper_of_moduleTopology Q t

/-- A point in the interior of a cone contained in another cone's closure belongs to the latter's
rational closure. This is the pointwise form used for the open upper sheet. -/
theorem subset_rationalClosure_of_mem
    {C D : PointedCone ℝ (realified V)} (hDC : D ≤ C.closure) {x : realified V}
    (hx : x ∈ interior D) : x ∈ rationalClosure C := by
  classical
  let e : realified V ≃ₗ[ℝ] (Fin (Module.finrank ℝ (realified V)) → ℝ) :=
    (Module.finBasis ℝ (realified V)).equivFun
  have h1 : Continuous e := IsModuleTopology.continuous_of_linearMap e.toLinearMap
  have h2 : Continuous e.symm := IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap
  let E' : realified V ≃L[ℝ] (Fin (Module.finrank ℝ (realified V)) → ℝ) :=
    { e with continuous_toFun := h1, continuous_invFun := h2 }
  have hconv : Convex ℝ (E' '' (rationalClosure C : Set (realified V))) :=
    (rationalClosure C).convex.linear_image E'.toLinearMap
  have hopen : IsOpen (E' '' (interior D)) := E'.toHomeomorph.isOpenMap _ isOpen_interior
  have himg : E' '' closure (rationalClosure C : Set (realified V)) =
      closure (E' '' (rationalClosure C : Set (realified V))) :=
    Homeomorph.image_closure E'.toHomeomorph _
  have hrb : (interior D : Set (realified V)) ⊆ closure (rationalBoundary C) := by
    intro x hx
    rw [mem_closure_iff_nhds]
    intro T hT
    obtain ⟨U, hUT, hU, hxU⟩ := mem_nhds_iff.1 hT
    obtain ⟨y, hyQ, hy⟩ := dense_range_rationalPoint.exists_mem_open
      (hU.inter isOpen_interior) ⟨x, hxU, hx⟩
    exact ⟨y, hUT hy.1, ⟨by simpa using hyQ, hDC (interior_subset hy.2)⟩⟩
  have hcl : (interior D : Set (realified V)) ⊆
      closure (rationalClosure C : Set (realified V)) :=
    hrb.trans (closure_mono fun x hx => subset_convexHull ℝ _ hx)
  have hsub : E' '' (interior D) ⊆ closure (E' '' (rationalClosure C : Set (realified V))) := by
    rw [← himg]
    exact Set.image_mono hcl
  have key : E' '' (interior D) ⊆ E' '' (rationalClosure C : Set (realified V)) :=
    subset_of_subset_closure_of_convex hopen hsub hconv
  obtain ⟨y, hy, hyx⟩ := key ⟨x, hx, rfl⟩
  rwa [E'.injective hyx] at hy

/-- **The closed sheet is a nondegenerate cone**: `x` and `-x` both on it forces `x ⊥ t`,
`Q x = 0`, and then `x = 0` (`eq_zero_of_perp_of_quadratic_eq_zero`). -/
theorem closedSheet_salient {Q : QuadraticForm ℝ (realified V)} (hpos : sigPos Q = 1)
    (hnd : Q.Nondegenerate) {t : realified V} (ht : 0 < Q t) :
    (closedSheet Q hpos ht : ConvexCone ℝ (realified V)).Salient := by
  intro x hx hx0 hneg
  have hx' : 0 ≤ Q x ∧ 0 ≤ (associated Q) x t := hx
  have hneg' : 0 ≤ Q (-x) ∧ 0 ≤ (associated Q) (-x) t := hneg
  have hxt : (associated Q) x t = 0 := by
    have h1 : (associated Q) (-x) t = -((associated Q) x t) := by
      rw [show -x = (-1 : ℝ) • x by simp, map_smul, LinearMap.smul_apply, smul_eq_mul]
      ring
    rw [h1] at hneg'
    linarith [hx'.2, hneg'.1]
  have hQx : Q x = 0 := by
    rcases lt_or_eq_of_le hx'.1 with hlt | heq
    · exact absurd hxt (associated_ne_zero_of_mem_positiveCone Q hpos ht hlt)
    · exact heq.symm
  exact hx0 (eq_zero_of_perp_of_quadratic_eq_zero hpos hnd ht hxt hQx)

/-- **A face of `C₊` that contains a rational point of the open sheet is `C₊` itself**, in the
closed-sheet setting: for a large rational multiple `q • u` of the timelike point `u`, the point
`q • u - v` is again a rational point of the open sheet, hence lies on `C₊`, and the face relation
applied to `(q • u - v) + v = q • u` forces `v` into the face. This is
`eq_of_isFaceOf_of_mem_pos` with the two hypotheses of `IsPositiveConeComponent` replaced by the
continuity input `hcl` at the rational points where they are used. -/
theorem eq_of_isFaceOf_of_mem_pos_closedSheet {Q : QuadraticForm ℝ (realified V)}
    (hpos : sigPos Q = 1) {t : realified V} (ht : 0 < Q t)
    (hcl : ∀ v : V, rationalPoint v ∈ (closedSheet Q hpos ht).closure →
      0 ≤ Q (rationalPoint v) ∧ 0 ≤ (associated Q) (rationalPoint v) t)
    {F : PointedCone ℝ (realified V)} {u : V}
    (hu : 0 < Q (rationalPoint u))
    (hut : 0 < (associated Q) (rationalPoint u) t)
    (hF : F.IsFaceOf (rationalClosure (closedSheet Q hpos ht)))
    (hFu : rationalPoint u ∈ F) :
    F = rationalClosure (closedSheet Q hpos ht) := by
  set Qu : ℝ := Q (rationalPoint u) with hQu_def
  set bu : ℝ := (associated Q) (rationalPoint u) t with hbu_def
  have hQu : 0 < Qu := hQu_def ▸ hu
  have hbu : 0 < bu := hbu_def ▸ hut
  refine le_antisymm hF.le ?_
  rw [rationalClosure_eq_hull]
  refine Submodule.span_le.2 ?_
  rintro p ⟨⟨v, -, rfl⟩, hvcl⟩
  obtain ⟨hvQ, hvt⟩ := hcl v hvcl
  set b : ℝ := (associated Q) (rationalPoint u) (rationalPoint v) with hb_def
  set c : ℝ := (associated Q) (rationalPoint v) t with hc_def
  set A : ℝ := 2 * |b| / Qu + 1 with hA_def
  set B : ℝ := (c + 1) / bu with hB_def
  obtain ⟨q, hq⟩ := exists_rat_gt (max A (max B 1))
  have hq1 : (1 : ℝ) ≤ (q : ℝ) :=
    le_trans (le_max_right B 1) (le_trans (le_max_right A (max B 1)) hq.le)
  have hqA : A < (q : ℝ) := lt_of_le_of_lt (le_max_left A (max B 1)) hq
  have hqB : B < (q : ℝ) :=
    lt_of_le_of_lt (le_trans (le_max_left B 1) (le_max_right A (max B 1))) hq
  rw [hA_def] at hqA
  rw [hB_def] at hqB
  have hqpos : (0 : ℚ) < q := by exact_mod_cast lt_of_lt_of_le zero_lt_one hq1
  set z : realified V := rationalPoint (q • u - v) with hz_def
  have hzrep : z = (q : ℝ) • rationalPoint u - rationalPoint v := by
    rw [hz_def, map_sub, rationalPoint_rat_smul]
  have hQz : 0 < Q z := by
    have hrep2 : z = (q : ℝ) • rationalPoint u + (-1 : ℝ) • rationalPoint v := by
      rw [hzrep, sub_eq_add_neg]
      congr 1
      exact (neg_one_smul ℝ (rationalPoint v)).symm
    have h1 : 2 * |b| + Qu ≤ (q : ℝ) * Qu := by
      have h2 : 2 * |b| / Qu < (q : ℝ) - 1 := by linarith
      have h4 : 2 * |b| / Qu * Qu < ((q : ℝ) - 1) * Qu := mul_lt_mul_of_pos_right h2 hQu
      have h5 : 2 * |b| / Qu * Qu = 2 * |b| := by field_simp
      rw [h5] at h4
      nlinarith
    have hbq : 2 * (q : ℝ) * b ≤ 2 * (q : ℝ) * |b| := by
      have h0 : (0 : ℝ) ≤ 2 * (q : ℝ) := by linarith
      nlinarith [le_abs_self b]
    have hexp : Q z = (q : ℝ) ^ 2 * Q (rationalPoint u) - 2 * (q : ℝ) * b
        + Q (rationalPoint v) := by
      rw [hrep2, quadratic_expand, hb_def]
      ring
    rw [hexp]
    nlinarith [h1, hbq, hvQ, hq1, hQu]
  have hbz : 0 < (associated Q) z t := by
    have hstep : (associated Q) z
        = (q : ℝ) • (associated Q) (rationalPoint u)
          - (associated Q) (rationalPoint v) := by
      rw [hzrep, map_sub, map_smul]
    have h1 : c < (q : ℝ) * bu := by
      rw [div_lt_iff₀ hbu] at hqB
      linarith
    rw [hstep, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
    have hgoal : (q : ℝ) * ((associated Q) (rationalPoint u) t)
        - (associated Q) (rationalPoint v) t = (q : ℝ) * bu - c := by
      rw [hbu_def, hc_def]
    rw [hgoal]
    linarith
  have hzK : z ∈ closedSheet Q hpos ht := ⟨hQz.le, hbz.le⟩
  have hzC : z ∈ rationalClosure (closedSheet Q hpos ht) := by
    rw [mem_rationalClosure]
    exact subset_convexHull ℝ _
      ⟨⟨q • u - v, Set.mem_univ _, rfl⟩, subset_closure hzK⟩
  have hpC : rationalPoint v ∈ rationalClosure (closedSheet Q hpos ht) := by
    rw [mem_rationalClosure]
    exact subset_convexHull ℝ _
      ⟨⟨v, Set.mem_univ v, rfl⟩, subset_closure ⟨hvQ, hvt⟩⟩
  have hsum : z + rationalPoint v ∈ F := by
    have heq : z + rationalPoint v = (q : ℝ) • rationalPoint u := by
      rw [hzrep]
      abel
    rw [heq]
    exact PointedCone.smul_mem _ (by linarith) hFu
  exact ((hF.add_mem_iff_mem hzC hpC).mp hsum).2

/-- **`C₊` is a nondegenerate cone in the setting of Example 4.3** (Looijenga, p. 17: "this is a
nondegenerate cone also"), for the closed sheet `C` of a nondegenerate form of signature
`(1, dim − 1)`. The hypothesis `hcl` is the continuity of `Q` and of `x ↦ x · t` at the rational
points of the closure of `C`, where they are used; see the section docstring. -/
theorem salient_rationalClosure {Q : QuadraticForm ℝ (realified V)} (hpos : sigPos Q = 1)
    (hnd : Q.Nondegenerate) {t : realified V} (ht : 0 < Q t)
    (hcl : ∀ v : V, rationalPoint v ∈ (closedSheet Q hpos ht).closure →
      0 ≤ Q (rationalPoint v) ∧ 0 ≤ (associated Q) (rationalPoint v) t) :
    (rationalClosure (closedSheet Q hpos ht) : ConvexCone ℝ (realified V)).Salient := by
  have hsub : rationalBoundary (closedSheet Q hpos ht)
      ⊆ (closedSheet Q hpos ht : Set (realified V)) := by
    rintro x ⟨⟨v, -, rfl⟩, hvcl⟩
    exact hcl v hvcl
  have hle : rationalClosure (closedSheet Q hpos ht) ≤ closedSheet Q hpos ht := by
    rw [rationalClosure_eq_hull]
    exact Submodule.span_le.2 hsub
  exact (closedSheet_salient hpos hnd ht).anti hle

/-- **`Σ(bb)` is a locally rational decomposition of `C₊` in the setting of Example 4.3**
(Looijenga, pp. 17-18, the assertion that the facial decomposition is a locally rational
decomposition, with Definition 4.2 read as in `IsLocallyRationalDecomposition`). -/
theorem hyperbolicFacialDecomposition_isLocallyRational {Q : QuadraticForm ℝ (realified V)}
    (hpos : sigPos Q = 1) (hnd : Q.Nondegenerate) {t : realified V} (ht : 0 < Q t)
    (hcl : ∀ v : V, rationalPoint v ∈ (closedSheet Q hpos ht).closure →
      0 ≤ Q (rationalPoint v) ∧ 0 ≤ (associated Q) (rationalPoint v) t) :
    IsLocallyRationalDecomposition (rationalClosure (closedSheet Q hpos ht))
      (facialDecomposition (rationalClosure (closedSheet Q hpos ht))) :=
  facialDecomposition_isLocallyRational _ (salient_rationalClosure hpos hnd ht hcl)

end Hyperbolic

/-! ## The action of `Γ` on locally rational decompositions (Example 4.3, p. 17)

Looijenga, Example 4.3, p. 17: `Γ` is an arithmetic subgroup of the orthogonal group of
`L(ℚ)` preserving `C`. What the action on locally rational decompositions of `C₊` needs of `Γ`
is only that its elements are linear equivalences of `L(ℝ)` *defined over `ℚ`* — so that they
carry rational cones to rational cones (`IsRationalEquiv`) — and that they preserve `C₊`. The
form itself is not needed: salience, faces and traces are preserved by any linear equivalence.

The two statements are the action (`IsLocallyRationalDecomposition.coneMap`: the image of a
locally rational decomposition of `C₊` is again one) and invariance (`IsGammaInvariant`, and
`isGammaInvariant_facialDecomposition`: the facial decomposition `Σ(bb)` is fixed by every
element of such a group, as the coarsest locally rational decomposition must be). -/

section GammaAction

variable {e : (realified V) ≃ₗ[ℝ] (realified V)}

/-- The image of a cone under a real linear equivalence of `L(ℝ)`. -/
noncomputable def coneMap (e : (realified V) ≃ₗ[ℝ] (realified V))
    (P : PointedCone ℝ (realified V)) : PointedCone ℝ (realified V) where
  carrier := e '' (P : Set (realified V))
  zero_mem' := ⟨0, P.zero_mem, by simp⟩
  add_mem' := by
    rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    exact ⟨a + b, P.add_mem ha hb, by simp⟩
  smul_mem' := by
    rintro c _ ⟨a, ha, rfl⟩
    exact ⟨(c : ℝ) • a, P.smul_mem c.2 ha, by rw [map_smul, ← Nonneg.coe_smul]⟩

@[simp]
theorem mem_coneMap {P : PointedCone ℝ (realified V)} {x : realified V} :
    x ∈ coneMap e P ↔ e.symm x ∈ P := by
  constructor
  · rintro ⟨a, ha, rfl⟩
    simpa using ha
  · intro hx
    exact ⟨e.symm x, hx, by simp⟩

/-- The image under the inverse equivalence is the original cone. -/
theorem coneMap_symm_coneMap (P : PointedCone ℝ (realified V)) :
    coneMap e.symm (coneMap e P) = P := by
  refine SetLike.ext fun x => ?_
  rw [mem_coneMap, mem_coneMap]
  simp

/-- The image of the inverse image is the original cone. -/
theorem coneMap_coneMap_symm (P : PointedCone ℝ (realified V)) :
    coneMap e (coneMap e.symm P) = P :=
  coneMap_symm_coneMap (e := e.symm) P

/-- The image map on cones is injective. -/
theorem coneMap_injective : Function.Injective (coneMap e) := by
  intro P Q h
  have h' := congrArg (coneMap e.symm) h
  rwa [coneMap_symm_coneMap, coneMap_symm_coneMap] at h'

/-- The image of an intersection is the intersection of the images. -/
theorem coneMap_inf (P Q : PointedCone ℝ (realified V)) :
    coneMap e (P ⊓ Q) = coneMap e P ⊓ coneMap e Q := by
  refine SetLike.ext fun x => ?_
  rw [mem_coneMap, Submodule.mem_inf, Submodule.mem_inf, mem_coneMap, mem_coneMap]

/-- The image map on cones is monotone. -/
theorem coneMap_mono {P Q : PointedCone ℝ (realified V)} (h : P ≤ Q) :
    coneMap e P ≤ coneMap e Q := by
  rintro - ⟨y, hy, rfl⟩
  exact ⟨y, h hy, rfl⟩

/-- **Faces map to faces** under a linear equivalence. -/
theorem isFaceOf_coneMap {F P : PointedCone ℝ (realified V)} (hF : F.IsFaceOf P) :
    (coneMap e F).IsFaceOf (coneMap e P) where
  le := by
    rintro _ ⟨a, ha, rfl⟩
    exact ⟨a, hF.le ha, rfl⟩
  mem_of_smul_add_mem := by
    rintro x y a hx hy ha hxy
    rw [mem_coneMap] at hx hy hxy ⊢
    have h : e.symm (a • x + y) = a • e.symm x + e.symm y := by simp
    rw [h] at hxy
    exact hF.mem_of_smul_add_mem hx hy ha hxy

theorem isFaceOf_coneMap_iff {F P : PointedCone ℝ (realified V)} :
    (coneMap e F).IsFaceOf (coneMap e P) ↔ F.IsFaceOf P := by
  refine ⟨fun h => ?_, isFaceOf_coneMap⟩
  have h' := isFaceOf_coneMap (e := e.symm) h
  rwa [coneMap_symm_coneMap, coneMap_symm_coneMap] at h'

/-- **Salience is preserved** by a linear equivalence. -/
theorem salient_coneMap_iff {P : PointedCone ℝ (realified V)} :
    (coneMap e P : ConvexCone ℝ (realified V)).Salient ↔
      (P : ConvexCone ℝ (realified V)).Salient := by
  constructor
  · intro h x hx hx0 hneg
    refine h (e x) ⟨x, hx, rfl⟩ ?_ ⟨-x, hneg, by simp⟩
    intro h0
    exact hx0 (by simpa using congrArg e.symm h0)
  · intro h x hx hx0 hneg
    obtain ⟨a, ha, rfl⟩ := hx
    obtain ⟨b, hb, hbx⟩ := hneg
    have hba : b = -a := by
      have h' := congrArg e.symm hbx
      simpa using h'
    have hb' : -a ∈ P := hba ▸ hb
    have ha0 : a = 0 := by
      by_contra hne
      exact h a ha hne hb'
    exact hx0 (by rw [ha0]; simp)

/-- **A real linear equivalence defined over `ℚ`**: one that carries `L(ℚ)` to itself.
Looijenga's `Γ` is a subgroup of the orthogonal group of `L(ℚ)`, so each of its elements extends
to such an equivalence of `L(ℝ)`. -/
structure IsRationalEquiv (e : (realified V) ≃ₗ[ℝ] (realified V)) : Prop where
  /-- The `ℚ`-linear equivalence inducing `e` on `L(ℚ)`. -/
  exists_rat : ∃ g : V ≃ₗ[ℚ] V, ∀ v : V, e (rationalPoint v) = rationalPoint (g v)

theorem IsRationalEquiv.symm (he : IsRationalEquiv e) : IsRationalEquiv e.symm := by
  obtain ⟨g, hg⟩ := he.exists_rat
  refine ⟨g.symm, fun v => ?_⟩
  apply e.injective
  rw [LinearEquiv.apply_symm_apply, hg]
  simp

/-- **A rational cone maps to a rational cone** under an equivalence defined over `ℚ`. -/
theorem IsRationalEquiv.isRationalCone_coneMap (he : IsRationalEquiv e)
    {P : PointedCone ℝ (realified V)} (hP : IsRationalCone P) :
    IsRationalCone (coneMap e P) := by
  classical
  obtain ⟨s, rfl⟩ := hP
  obtain ⟨g, hg⟩ := he.exists_rat
  refine ⟨s.image g, ?_⟩
  refine le_antisymm ?_ ?_
  · rintro x ⟨y, hy, rfl⟩
    induction hy using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨v, hv, rfl⟩ := hz
      rw [hg]
      exact PointedCone.subset_hull
        ⟨g v, Finset.mem_coe.2 (Finset.mem_image_of_mem g (Finset.mem_coe.1 hv)), rfl⟩
    | zero => rw [map_zero]; exact (PointedCone.hull ℝ _).zero_mem
    | add u v _ _ hu hv => rw [map_add]; exact (PointedCone.hull ℝ _).add_mem hu hv
    | smul c u _ hu =>
      rw [show e (c • u) = c • e u by
        change e ((c : ℝ) • u) = (c : ℝ) • e u
        rw [map_smul]]
      exact (PointedCone.hull ℝ _).smul_mem c.2 hu
  · intro x hx
    rw [mem_coneMap]
    induction hx using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨w, hw, rfl⟩ := hz
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hw)
      have h : e.symm (rationalPoint (g v)) = rationalPoint v := by
        rw [← hg v]; simp
      rw [h]
      exact PointedCone.subset_hull ⟨v, hv, rfl⟩
    | zero => rw [map_zero]; exact (PointedCone.hull ℝ _).zero_mem
    | add u v _ _ hu hv => rw [map_add]; exact (PointedCone.hull ℝ _).add_mem hu hv
    | smul c u _ hu =>
      rw [show e.symm (c • u) = c • e.symm u by
        change e.symm ((c : ℝ) • u) = (c : ℝ) • e.symm u
        rw [map_smul]]
      exact (PointedCone.hull ℝ _).smul_mem c.2 hu

/-- The traces of the image of a family are the images of the traces. -/
theorem restrictionTo_coneMap (S : Set (PointedCone ℝ (realified V)))
    (P : PointedCone ℝ (realified V)) :
    restrictionTo (coneMap e '' S) P
      = coneMap e '' (restrictionTo S (coneMap e.symm P)) := by
  ext F
  constructor
  · rintro ⟨σ, hσ, rfl⟩
    obtain ⟨σ₀, hσ₀, rfl⟩ := hσ
    refine ⟨σ₀ ⊓ coneMap e.symm P, ⟨σ₀, hσ₀, rfl⟩, ?_⟩
    rw [coneMap_inf, coneMap_coneMap_symm]
  · rintro ⟨τ, hτ, rfl⟩
    obtain ⟨σ, hσ, rfl⟩ := mem_restrictionTo.1 hτ
    refine mem_restrictionTo.2 ⟨coneMap e σ, ⟨σ, hσ, rfl⟩, ?_⟩
    rw [coneMap_inf, coneMap_coneMap_symm]

/-- The face-closure of the image of a family is the image of its face-closure. -/
theorem faceClosure_coneMap (S : Set (PointedCone ℝ (realified V))) :
    faceClosure (coneMap e '' S) = coneMap e '' faceClosure S := by
  ext F
  constructor
  · rintro ⟨σ, hσ, hFσ⟩
    obtain ⟨σ₀, hσ₀, rfl⟩ := hσ
    refine ⟨coneMap e.symm F, mem_faceClosure.2 ⟨σ₀, hσ₀, ?_⟩, coneMap_coneMap_symm F⟩
    refine (isFaceOf_coneMap_iff (e := e) (F := coneMap e.symm F) (P := σ₀)).1 ?_
    rw [coneMap_coneMap_symm]
    exact hFσ
  · rintro ⟨F₀, ⟨σ₀, hσ₀, hF₀⟩, rfl⟩
    exact mem_faceClosure.2 ⟨coneMap e σ₀, ⟨σ₀, hσ₀, rfl⟩, isFaceOf_coneMap hF₀⟩

/-- **A rational cone system maps to a rational cone system** under an equivalence defined over
`ℚ`: Definition 4.1, p. 16, is invariant under `Γ`. -/
theorem IsRationalEquiv.isRationalConeSystem_coneMap (he : IsRationalEquiv e)
    {S : Set (PointedCone ℝ (realified V))} (hS : IsRationalConeSystem S) :
    IsRationalConeSystem (coneMap e '' S) where
  finite := hS.finite.image _
  salient σ hσ := by
    obtain ⟨σ₀, hσ₀, rfl⟩ := hσ
    exact salient_coneMap_iff.2 (hS.salient σ₀ hσ₀)
  isRational σ hσ := by
    obtain ⟨σ₀, hσ₀, rfl⟩ := hσ
    exact he.isRationalCone_coneMap (hS.isRational σ₀ hσ₀)
  mem_of_isFaceOf := by
    rintro σ τ ⟨σ₀, hσ₀, rfl⟩ hτσ
    refine ⟨coneMap e.symm τ, hS.mem_of_isFaceOf hσ₀ ?_, coneMap_coneMap_symm τ⟩
    refine (isFaceOf_coneMap_iff (e := e) (F := coneMap e.symm τ) (P := σ₀)).1 ?_
    rw [coneMap_coneMap_symm]
    exact hτσ
  inf_isFaceOf_left := by
    rintro σ τ ⟨σ₀, hσ₀, rfl⟩ ⟨τ₀, hτ₀, rfl⟩
    have h := isFaceOf_coneMap (e := e) (hS.inf_isFaceOf_left hσ₀ hτ₀)
    have hinf : coneMap e σ₀ ⊓ coneMap e τ₀ = coneMap e (σ₀ ⊓ τ₀) := (coneMap_inf _ _).symm
    rwa [hinf]

/-- A cone fixed by an equivalence fixes the rational cones of its inverse image: used to pull a
rational subcone back along `Γ`. -/
theorem coneMap_symm_le_of_eq {Cplus P : PointedCone ℝ (realified V)}
    (hC : coneMap e Cplus = Cplus) (hPle : P ≤ Cplus) : coneMap e.symm P ≤ Cplus := by
  have h1 : (e : realified V → realified V) '' (Cplus : Set (realified V))
      = (Cplus : Set (realified V)) :=
    congrArg (fun Q : PointedCone ℝ (realified V) => (Q : Set (realified V))) hC
  have key : ∀ y : realified V, y ∈ (Cplus : Set (realified V)) →
      e y ∈ (Cplus : Set (realified V)) := by
    intro y hy
    rw [← h1]
    exact Set.mem_image_of_mem _ hy
  have key' : ∀ y : realified V, e y ∈ (Cplus : Set (realified V)) →
      y ∈ (Cplus : Set (realified V)) := by
    intro y hy
    have hmem : e y ∈ (e : realified V → realified V) '' (Cplus : Set (realified V)) := by
      rw [h1]
      exact hy
    obtain ⟨z, hz, hzy⟩ := hmem
    have hyz : z = y := by
      have h' := congrArg e.symm hzy
      simpa using h'
    rw [hyz] at hz
    exact hz
  have himg : (e.symm : realified V → realified V) '' (Cplus : Set (realified V))
      = (Cplus : Set (realified V)) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact key' (e.symm x) (by simpa using hx)
    · intro hy
      exact ⟨e y, key y hy, by simp⟩
  intro x hx
  rw [mem_coneMap] at hx
  simp only [LinearEquiv.symm_symm] at hx
  change x ∈ (Cplus : Set (realified V))
  rw [← himg]
  have hxe : x = (e.symm : realified V → realified V) (e x) := by simp
  rw [hxe]
  exact Set.mem_image_of_mem _ (hPle hx)
/-- **The `Γ`-action on locally rational decompositions of `C₊`** (Looijenga, Example 4.3,
p. 17): an element of `Γ` — a `ℚ`-rational linear equivalence preserving `C₊` — carries a
locally rational decomposition of `C₊` to a locally rational decomposition of `C₊`. -/
theorem isLocallyRationalDecomposition_coneMap (he : IsRationalEquiv e)
    {Cplus : PointedCone ℝ (realified V)} {S : Set (PointedCone ℝ (realified V))}
    (hS : IsLocallyRationalDecomposition Cplus S) (hC : coneMap e Cplus = Cplus) :
    IsLocallyRationalDecomposition Cplus (coneMap e '' S) where
  union_eq := by
    have h1 : (⋃ σ ∈ S, ((coneMap e σ : PointedCone ℝ (realified V)) : Set (realified V)))
        = e '' (Cplus : Set (realified V)) := by
      rw [← hS.union_eq]
      ext x
      simp only [Set.mem_iUnion, Set.mem_image, exists_prop]
      constructor
      · rintro ⟨σ, hσ, z, hz, rfl⟩
        exact ⟨z, ⟨σ, hσ, hz⟩, rfl⟩
      · rintro ⟨z, ⟨σ, hσ, hz⟩, rfl⟩
        exact ⟨σ, hσ, z, hz, rfl⟩
    have h2 : (⋃ σ ∈ coneMap e '' S, (σ : Set (realified V)))
        = ⋃ σ ∈ S, ((coneMap e σ : PointedCone ℝ (realified V)) : Set (realified V)) := by
      ext x
      simp only [Set.mem_iUnion, exists_prop]
      constructor
      · rintro ⟨σ, ⟨σ₀, hσ₀, rfl⟩, hx⟩
        exact ⟨σ₀, hσ₀, hx⟩
      · rintro ⟨σ₀, hσ₀, hx⟩
        exact ⟨coneMap e σ₀, ⟨σ₀, hσ₀, rfl⟩, hx⟩
    rw [h2, h1]
    exact congrArg (fun P : PointedCone ℝ (realified V) => (P : Set (realified V))) hC
  isLocallyRational σ hσ := by
    obtain ⟨σ₀, hσ₀, rfl⟩ := hσ
    intro P hP hPle
    have hP' : IsRationalCone (coneMap e.symm P) := he.symm.isRationalCone_coneMap hP
    have hPle' : coneMap e.symm P ≤ Cplus := coneMap_symm_le_of_eq hC hPle
    have h := hS.isLocallyRational σ₀ hσ₀ (coneMap e.symm P) hP' hPle'
    have hinf : coneMap e σ₀ ⊓ P = coneMap e (σ₀ ⊓ coneMap e.symm P) := by
      rw [coneMap_inf, coneMap_coneMap_symm]
    rw [hinf]
    exact he.isRationalCone_coneMap h
  restriction P hP hPle := by
    have hP' : IsRationalCone (coneMap e.symm P) := he.symm.isRationalCone_coneMap hP
    have hPle' : coneMap e.symm P ≤ Cplus := coneMap_symm_le_of_eq hC hPle
    have h := hS.restriction (coneMap e.symm P) hP' hPle'
    rw [restrictionTo_coneMap, faceClosure_coneMap]
    exact he.isRationalConeSystem_coneMap h

/-- `Σ` is `Γ`-invariant when every element of `Γ` fixes it. -/
def IsGammaInvariant (Γ : Set ((realified V) ≃ₗ[ℝ] (realified V)))
    (S : Set (PointedCone ℝ (realified V))) : Prop :=
  ∀ e ∈ Γ, coneMap e '' S = S

/-- **The facial decomposition `Σ(bb)` is `Γ`-invariant** (Looijenga, Definition 4.2, p. 17): faces
map to faces under a linear equivalence, and `Σ(bb)` is the set of faces of `C₊`. -/
theorem isGammaInvariant_facialDecomposition (Γ : Set ((realified V) ≃ₗ[ℝ] (realified V)))
    (Cplus : PointedCone ℝ (realified V)) (hΓ : ∀ e ∈ Γ, coneMap e Cplus = Cplus) :
    IsGammaInvariant Γ (facialDecomposition Cplus) := by
  intro e he
  ext F
  constructor
  · rintro ⟨F₀, hF₀, rfl⟩
    have h := isFaceOf_coneMap (e := e) hF₀
    rwa [hΓ e he] at h
  · intro hF
    refine ⟨coneMap e.symm F, ?_, coneMap_coneMap_symm F⟩
    have h1 : (coneMap e (coneMap e.symm F)).IsFaceOf (coneMap e Cplus) := by
      rw [coneMap_coneMap_symm, hΓ e he]
      exact hF
    exact (isFaceOf_coneMap_iff (e := e) (F := coneMap e.symm F) (P := Cplus)).1 h1

end GammaAction

/-! ## Closedness of a finitely generated cone

LC-09 (2026-11-19): `content:PointedCone.FG.isClosed` found LeanPool's norm-space proof in
`FgConeClosed.lean`; `content:DualFG`, the repository's already-ported Minkowski–Weyl
representation, avoids its longer conic-Carathéodory proof. The needed module-topology statement
is the finite intersection of closed half-spaces supplied by `PointedCone.fg_iff_dualFG`, with
`IsModuleTopology.continuous_of_linearMap` for the individual inequalities.
-/

namespace PointedCone.FG

/-- A finitely generated cone in a finite-dimensional real module with the module topology is
closed. Minkowski–Weyl writes it as the intersection of finitely many linear half-spaces. -/
theorem isClosed_of_moduleTopology {E : Type*} [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] [IsModuleTopology ℝ E] [Module.Finite ℝ E]
    {C : PointedCone ℝ E} (hC : C.FG) : IsClosed (C : Set E) := by
  obtain ⟨s, hs⟩ := (PointedCone.fg_iff_dualFG (C := C)).1 hC
  rw [← hs]
  rw [show ((PointedCone.dual (LinearMap.id : Module.Dual ℝ E →ₗ[ℝ] Module.Dual ℝ E)
      (s : Set (Module.Dual ℝ E)) : PointedCone ℝ E) : Set E) =
      ⋂ f : Module.Dual ℝ E, ⋂ _ : f ∈ (s : Set (Module.Dual ℝ E)),
        {x : E | 0 ≤ f x} by
    ext x
    simp]
  exact isClosed_biInter fun f _ => isClosed_le continuous_const
    (IsModuleTopology.continuous_of_linearMap f)

/-- Linear images preserve finite generation of cones. LC-09 (2026-11-19):
`content:Submodule.map_span content:PointedCone` found the ray-level specialization; this is
`Submodule.map_span` at `Nonneg ℝ`, with no rational-structure requirement on the target. -/
theorem map {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
    {C : PointedCone ℝ E} (hC : C.FG) (f : E →ₗ[ℝ] F) : (C.map f).FG := by
  classical
  obtain ⟨s, hs⟩ := hC
  refine ⟨s.image f, ?_⟩
  rw [← hs]
  simp only [PointedCone.map, Finset.coe_image]
  exact (Submodule.map_span (f : E →ₗ[Nonneg ℝ] F) (s : Set E)).symm

end PointedCone.FG

/-! ## Faces exposed by a nonnegative functional

Looijenga's Lemma-Definition 4.5 uses the common faces of the finite rational traces of a
locally rational decomposition. The following declarations are the algebraic exposure input for
those traces, ported from TauCeti `Geometry/Convex/Cone/Face/Exposed.lean` at
`7b3aaabdeaef0c48b006d1ff4aa81e1f83ba020e`, itself adapted from Mei
`Geometry/Convex/Cone/Face/Exposed.lean` at `7f1e4c7714fb020473694755ad8748c8f15d0e7f`
(Apache 2.0).

LC-09 for this step (2026-11-19): the whole-corpus queries
`content:supportSpace PointedCone`, `content:locally rational decomposition`,
`content:IsExposed PointedCone.IsFaceOf`, `content:exists_nonneg_linear_zero_iff`,
`content:polyhedron recession cone`, `content:recessionCone`,
`content:FinitePolyhedralComplex MinimalCell`, `content:AffineSubspace polyhedron decomposition`,
`content:minimal IsConvexPolyhedron lineal`, `content:minimalCell affineSubspace`,
`content:translation space members decomposition invariant`, and
`content:locally finite polyhedral complex`. The third and fourth found this exact exposure
implementation; no hit supplied the locality or the affine decomposition argument. The recession
and homogenization hits are recorded below where the isotropic argument consumes them.
-/

section PointedConeExposure

variable {K E : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  [AddCommGroup E] [Module K E]

/-- A linear functional nonnegative on a pointed cone cuts out a face of the cone. Ported from
TauCeti `PointedCone.isFaceOf_inf_ker` (Apache 2.0). -/
theorem PointedCone.isFaceOf_inf_ker {C : PointedCone K E} {φ : Module.Dual K E}
    (hφ : ∀ x ∈ C, 0 ≤ φ x) :
    (C ⊓ PointedCone.ofSubmodule (LinearMap.ker φ)).IsFaceOf C := by
  refine ⟨inf_le_left, fun {x y a} hx hy ha hxy ↦ ⟨hx, ?_⟩⟩
  have hker : φ (a • x + y) = 0 := hxy.2
  rw [map_add, map_smul, smul_eq_mul] at hker
  have hax : a * φ x = 0 :=
    (add_eq_zero_iff_of_nonneg (mul_nonneg ha.le (hφ x hx)) (hφ y hy)).1 hker |>.1
  exact (mul_eq_zero.1 hax).resolve_left ha.ne'

/-- A nonnegative functional that vanishes at exactly the generators lying in a face cuts out
that face. Ported from TauCeti `PointedCone.inf_ker_eq_of_eq_hull` (Apache 2.0). -/
theorem PointedCone.inf_ker_eq_of_eq_hull {C F : PointedCone K E} {s : Set E}
    (hC : C = PointedCone.hull K s) (hF : F.IsFaceOf C) {φ : Module.Dual K E}
    (hφ : ∀ x ∈ s, 0 ≤ φ x) (hφF : ∀ x ∈ s, φ x = 0 ↔ x ∈ F) :
    C ⊓ PointedCone.ofSubmodule (LinearMap.ker φ) = F := by
  have hφC : ∀ x ∈ C, 0 ≤ φ x := by
    subst hC
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx => exact hφ x hx
    | zero => simp
    | add x y _ _ hx hy => rw [map_add]; exact add_nonneg hx hy
    | smul c x _ hx =>
        rw [← Nonneg.coe_smul, map_smul, smul_eq_mul]
        exact mul_nonneg c.2 hx
  refine le_antisymm (((PointedCone.isFaceOf_inf_ker hφC).eq_hull_inter_of_eq_hull hC).le.trans
    (Submodule.span_le.2 fun x hx ↦ (hφF x hx.1).1 hx.2.2)) ?_
  exact (hF.eq_hull_inter_of_eq_hull hC).le.trans <| Submodule.span_le.2 fun x hx ↦
    ⟨hC ▸ PointedCone.subset_hull hx.1, (hφF x hx.1).2 hx.2⟩

/-- Every face of a finitely generated cone is cut out by a linear functional nonnegative on
the cone. Ported from TauCeti `PointedCone.IsFaceOf.exists_nonneg_linear_inf_ker`, using the
repository's already-ported Tucker alternative at `LeanCategories.ForMathlib` (Apache 2.0). -/
theorem PointedCone.IsFaceOf.exists_nonneg_linear_inf_ker {C F : PointedCone K E}
    (hF : F.IsFaceOf C) (hC : C.FG) :
    ∃ f : Module.Dual K E, (∀ x ∈ C, 0 ≤ f x) ∧
      C ⊓ PointedCone.ofSubmodule (LinearMap.ker f) = F := by
  classical
  obtain ⟨s, hs⟩ := hC
  let J := {j : s // (j : E) ∈ F}
  let a : s ⊕ J → E := Sum.elim Subtype.val (fun j => -(j.val : E))
  obtain ⟨c, f, hc, hsum, hf, hpos⟩ :=
    LeanCategories.ForMathlib.exists_nonneg_sum_smul_eq_zero_and_forall_coeff_add_dual_pos
      (K := K) a
  have hsC : (s : Set E) ⊆ C := by
    rw [← hs]
    exact Submodule.subset_span
  have hsumF : (∑ j : s, c (.inl j) • (j : E)) ∈ F := by
    have heq : (∑ j : s, c (.inl j) • (j : E)) =
        ∑ j : J, c (.inr j) • (j.val : E) := by
      have h := hsum
      simp only [Fintype.sum_sum_type, a, Sum.elim_inl, Sum.elim_inr, smul_neg,
        Finset.sum_neg_distrib] at h
      exact sub_eq_zero.mp (by simpa only [sub_eq_add_neg] using h)
    rw [heq]
    exact F.sum_mem fun j _ => PointedCone.smul_mem F (hc (.inr j)) j.property
  have houtside (j : s) (hj : (j : E) ∉ F) : c (.inl j) = 0 := by
    by_contra hne
    have hp : 0 < c (.inl j) := lt_of_le_of_ne (hc (.inl j)) (Ne.symm hne)
    exact hj (hF.mem_of_sum_smul_mem
      (fun k : s => hsC k.property) (fun k => hc (.inl k)) hsumF j hp)
  have hfacezero (j : s) (hj : (j : E) ∈ F) : f (j : E) = 0 := by
    have hp : 0 ≤ f (j : E) := hf (.inl j)
    have hn : 0 ≤ -f (j : E) := by
      simpa only [a, Sum.elim_inr, map_neg] using hf (.inr ⟨j, hj⟩)
    exact le_antisymm (neg_nonneg.mp hn) hp
  have hfgen : ∀ x ∈ s, 0 ≤ f x := fun x hx => hf (.inl ⟨x, hx⟩)
  have hzgen : ∀ x ∈ s, f x = 0 ↔ x ∈ F := by
    intro x hx
    constructor
    · intro hzero
      by_contra hxF
      have hp := hpos (.inl ⟨x, hx⟩)
      have hc0 := houtside ⟨x, hx⟩ hxF
      simp only [hc0, zero_add, a, Sum.elim_inl, hzero, lt_self_iff_false] at hp
    · exact hfacezero ⟨x, hx⟩
  have hfC : ∀ x ∈ C, 0 ≤ f x := by
    have hdual : f ∈ PointedCone.dual (Module.Dual.eval K E) (s : Set E) :=
      fun _ hx => hfgen _ hx
    rw [← PointedCone.dual_hull, PointedCone.hull, hs] at hdual
    exact fun _ hx => hdual hx
  exact ⟨f, hfC, PointedCone.inf_ker_eq_of_eq_hull hs.symm hF hfgen hzgen⟩

end PointedConeExposure

/-! ## Lemma-Definition 4.5: the support space of a cone of a decomposition -/

/-- Looijenga, Lemma-Definition 4.5, p. 19: the real linear forms that are nonnegative on
`τ` and zero on `σ`. -/
def supportForms {E : Type*} [AddCommGroup E] [Module ℝ E]
    (τ σ : PointedCone ℝ E) : Set (E →ₗ[ℝ] ℝ) :=
  {φ | (∀ x ∈ τ, 0 ≤ φ x) ∧ (∀ x ∈ σ, φ x = 0)}

theorem mem_supportForms {E : Type*} [AddCommGroup E] [Module ℝ E]
    {τ σ : PointedCone ℝ E} {φ : E →ₗ[ℝ] ℝ} :
    φ ∈ supportForms τ σ ↔ (∀ x ∈ τ, 0 ≤ φ x) ∧ (∀ x ∈ σ, φ x = 0) :=
  Iff.rfl

/-- Looijenga, Lemma-Definition 4.5, p. 19 (text version
`.tmp-sources/looijenga-math0201218v2.md:519`): the common zero set of the real linear forms on
`L(ℝ)` that are nonnegative on `τ` and zero on `σ`. -/
noncomputable def supportSpace {E : Type*} [AddCommGroup E] [Module ℝ E]
    (τ σ : PointedCone ℝ E) : Submodule ℝ E :=
  ⨅ (φ : supportForms τ σ), LinearMap.ker (φ : E →ₗ[ℝ] ℝ)

theorem mem_supportSpace {E : Type*} [AddCommGroup E] [Module ℝ E]
    {τ σ : PointedCone ℝ E} {x : E} :
    x ∈ supportSpace τ σ ↔ ∀ φ ∈ supportForms τ σ, φ x = 0 := by
  rw [supportSpace, Submodule.mem_iInf]
  exact ⟨fun h φ hφ => h ⟨φ, hφ⟩, fun h φ => h φ.1 φ.2⟩

/-- The support space contains the span of `σ`: every form of `supportForms τ σ` vanishes on
`σ` (Looijenga, Lemma-Definition 4.5, p. 19). -/
theorem span_le_supportSpace {σ τ : PointedCone ℝ (realified V)} (_hστ : σ ≤ τ) :
    Submodule.span ℝ (σ : Set (realified V)) ≤ supportSpace τ σ := by
  refine Submodule.span_le.2 fun x hx => ?_
  exact mem_supportSpace.2 fun φ hφ => (mem_supportForms.1 hφ).2 x hx

/-- The support space is contained in the span of `τ`: a point outside the span of `τ` is
separated from `τ` by a form vanishing on `τ`, which is a form of `supportForms τ σ`
(Looijenga, Lemma-Definition 4.5, p. 19). -/
theorem supportSpace_le_span {σ τ : PointedCone ℝ (realified V)} (hστ : σ ≤ τ) :
    supportSpace τ σ ≤ Submodule.span ℝ (τ : Set (realified V)) := by
  intro x hx
  by_contra hxτ
  obtain ⟨f, hf0, hfker⟩ :=
    Submodule.exists_dual_map_eq_bot_of_notMem (p := Submodule.span ℝ (τ : Set (realified V)))
      hxτ (inferInstance : Module.Projective ℝ
        ((realified V) ⧸ Submodule.span ℝ (τ : Set (realified V))))
  have hfτ : ∀ y ∈ τ, f y = 0 := by
    intro y hy
    have hmem : f y ∈ (Submodule.span ℝ (τ : Set (realified V))).map f :=
      ⟨y, Submodule.subset_span hy, rfl⟩
    rw [hfker] at hmem
    simpa using hmem
  have hφ : f ∈ supportForms τ σ :=
    ⟨fun y hy => by rw [hfτ y hy], fun y hy => hfτ y (hστ hy)⟩
  exact hf0 (mem_supportSpace.1 hx f hφ)

/-- The support space of `σ` relative to `τ` is the span of `σ` when `τ = σ`. -/
theorem supportSpace_self (σ : PointedCone ℝ (realified V)) :
    supportSpace σ σ = Submodule.span ℝ (σ : Set (realified V)) :=
  le_antisymm (supportSpace_le_span le_rfl) (span_le_supportSpace le_rfl)

/-- The support space is monotone in `τ`: a form nonnegative on a larger cone is nonnegative
on a smaller one, so the common zero set grows with the cone. -/
theorem supportSpace_mono {σ τ τ' : PointedCone ℝ (realified V)} (hτ : τ ≤ τ') :
    supportSpace τ σ ≤ supportSpace τ' σ := by
  intro x hx
  refine mem_supportSpace.2 fun φ hφ => ?_
  exact mem_supportSpace.1 hx φ ⟨fun y hy => hφ.1 y (hτ hy), hφ.2⟩

/-- **A point outside a closed pointed cone is separated by a real nonnegative form.** Separation
is run in normed coordinates and composed with the continuous linear equivalence. This is the
form used by the closed-cone support-space lemmas below. -/
theorem exists_dual_nonneg_lt_of_isClosed {E : Type*} [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] [IsModuleTopology ℝ E] [Module.Finite ℝ E]
    {τ : PointedCone ℝ E} (hclosed : IsClosed (τ : Set E)) {x : E} (hx : x ∉ τ) :
    ∃ f : E →ₗ[ℝ] ℝ, (∀ y ∈ τ, 0 ≤ f y) ∧ f x < 0 := by
  let _ : IsTopologicalAddGroup E := IsModuleTopology.isTopologicalAddGroup ℝ E
  let e : E ≃ₗ[ℝ] (Fin (Module.finrank ℝ E) → ℝ) :=
    (Module.finBasis ℝ E).equivFun
  have h1 : Continuous e := IsModuleTopology.continuous_of_linearMap e.toLinearMap
  have h2 : Continuous e.symm := IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap
  let E' : E ≃L[ℝ] (Fin (Module.finrank ℝ E) → ℝ) :=
    { e with continuous_toFun := h1, continuous_invFun := h2 }
  let P : ProperCone ℝ (Fin (Module.finrank ℝ E) → ℝ) :=
    { toSubmodule := τ.map E'.toLinearMap
      isClosed' := by
        change IsClosed (E' '' (τ : Set E))
        exact E'.toHomeomorph.isClosedMap _ hclosed }
  have hxmap : E' x ∉ E' '' (τ : Set E) := by
    intro himage
    obtain ⟨y, hy, hyx⟩ := himage
    exact hx (E'.injective hyx ▸ hy)
  obtain ⟨f, hfP, hfx⟩ := P.hyperplane_separation_point (x₀ := E' x) hxmap
  refine ⟨(f.comp E'.toContinuousLinearMap).toLinearMap, ?_, hfx⟩
  intro y hy
  exact hfP (E' y) ⟨y, hy, rfl⟩

/-- **A closed pointed cone has zero support space over the zero cone.** If `x ∈ τ` is nonzero,
salience gives `-x ∉ τ`; if `x ∉ τ`, use `x` itself. In either case
`ProperCone.hyperplane_separation_point` supplies a continuous form nonnegative on `τ` and
negative on the separated point. If `x` lay in `supportSpace τ ⊥`, every such form would vanish
at `x`, a contradiction. -/
theorem supportSpace_bot_of_isClosed_of_salient [Module.Finite ℚ V]
    {τ : PointedCone ℝ (realified V)} (hclosed : IsClosed (τ : Set (realified V)))
    (hsal : (τ : ConvexCone ℝ (realified V)).Salient) : supportSpace τ ⊥ = ⊥ := by
  let e : realified V ≃ₗ[ℝ] (Fin (Module.finrank ℝ (realified V)) → ℝ) :=
    (Module.finBasis ℝ (realified V)).equivFun
  have h1 : Continuous e := IsModuleTopology.continuous_of_linearMap e.toLinearMap
  have h2 : Continuous e.symm := IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap
  let E' : realified V ≃L[ℝ] (Fin (Module.finrank ℝ (realified V)) → ℝ) :=
    { e with continuous_toFun := h1, continuous_invFun := h2 }
  let P : ProperCone ℝ (Fin (Module.finrank ℝ (realified V)) → ℝ) :=
    { toSubmodule := τ.map E'.toLinearMap
      isClosed' := by
        change IsClosed (E' '' (τ : Set (realified V)))
        exact E'.toHomeomorph.isClosedMap _ hclosed }
  have hseparate (x : realified V) (hx : x ∉ τ) :
      ∃ f : (realified V) →ₗ[ℝ] ℝ, (∀ y ∈ τ, 0 ≤ f y) ∧ f x ≠ 0 := by
    have hxmap : E' x ∉ E' '' (τ : Set (realified V)) := by
      intro himage
      obtain ⟨y, hy, hyx⟩ := himage
      exact hx (E'.injective hyx ▸ hy)
    obtain ⟨f, hfP, hfx⟩ := P.hyperplane_separation_point (x₀ := E' x) hxmap
    refine ⟨(f.comp E'.toContinuousLinearMap).toLinearMap, ?_, hfx.ne⟩
    intro y hy
    exact hfP (E' y) ⟨y, hy, rfl⟩
  apply le_antisymm ?_ bot_le
  intro x hx
  show x = 0
  by_contra hx0
  by_cases hxτ : x ∈ τ
  · obtain ⟨f, hfτ, hfx⟩ := hseparate (-x) (hsal x hxτ hx0)
    have hz : f x = 0 := mem_supportSpace.1 hx f ⟨fun y hy => hfτ y hy, by simp⟩
    rw [map_neg] at hfx
    exact hfx (by simp only [hz, neg_zero])
  · obtain ⟨f, hfτ, hfx⟩ := hseparate x hxτ
    have hz : f x = 0 := mem_supportSpace.1 hx f ⟨fun y hy => hfτ y hy, by simp⟩
    exact hfx (by simp only [hz])

/-- **The support space over zero is the lineality of the closure.** A point lies in it exactly
when both it and its negative lie in the closure. This is the double-dual statement over `ℝ`,
proved directly from `ProperCone.hyperplane_separation_point`; no salience is assumed. -/
theorem supportSpace_bot_eq_topologicalClosure_lineal {E : Type*} [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] [IsModuleTopology ℝ E] [Module.Finite ℝ E]
    (D : PointedCone ℝ E) :
    letI := IsModuleTopology.toContinuousAdd ℝ E
    supportSpace D ⊥ = PointedCone.lineal D.topologicalClosure := by
  haveI : ContinuousAdd E := IsModuleTopology.toContinuousAdd ℝ E
  have hclosed : IsClosed (D.topologicalClosure : Set E) :=
    Submodule.isClosed_topologicalClosure D
  have next {f : E →ₗ[ℝ] ℝ} (hf : ∀ y ∈ D, 0 ≤ f y) {x : E}
      (hx : x ∈ D.topologicalClosure) : 0 ≤ f x := by
    exact closure_minimal (t := {y | 0 ≤ f y}) (fun y hy => hf y hy)
      (isClosed_le continuous_const (IsModuleTopology.continuous_of_linearMap f)) hx
  apply le_antisymm
  · intro x hx
    rw [PointedCone.mem_lineal]
    constructor
    · by_contra hnot
      obtain ⟨f, hf, hneg⟩ := exists_dual_nonneg_lt_of_isClosed hclosed hnot
      have hz : f x = 0 := mem_supportSpace.1 hx f
        ⟨fun y hy => hf y (Submodule.le_topologicalClosure D hy), by simp⟩
      exact hneg.ne hz
    · by_contra hnot
      obtain ⟨f, hf, hneg⟩ := exists_dual_nonneg_lt_of_isClosed hclosed hnot
      have hz : f x = 0 := mem_supportSpace.1 hx f
        ⟨fun y hy => hf y (Submodule.le_topologicalClosure D hy), by simp⟩
      rw [map_neg] at hneg
      linarith
  · intro x hx
    rw [PointedCone.mem_lineal] at hx
    apply mem_supportSpace.2
    intro f hf
    have hpos := next hf.1 hx.1
    have hneg := next hf.1 hx.2
    rw [map_neg] at hneg
    linarith

/-- **Support space descends along the quotient by the span of `σ`.** A form on `τ` zero on
`σ` descends because it vanishes on `span σ`; conversely every quotient form pulls back. The two
constructions are inverse for purposes of support-space membership, with no topological input. -/
theorem supportSpace_map_mkQ_bot {τ σ : PointedCone ℝ (realified V)} :
    let N := Submodule.span ℝ (σ : Set (realified V))
    (supportSpace (τ.map N.mkQ) ⊥).comap N.mkQ = supportSpace τ σ := by
  let N := Submodule.span ℝ (σ : Set (realified V))
  let D := τ.map N.mkQ
  change (supportSpace D ⊥).comap N.mkQ = supportSpace τ σ
  have hdesc (φ : supportForms τ σ) :
      N.liftQ φ.1 (by
        apply Submodule.span_le.2
        intro y hy
        exact φ.2.2 y hy) ∈ supportForms D ⊥ := by
    refine ⟨?_, by simp⟩
    intro z hz
    obtain ⟨y, hy, rfl⟩ := hz
    change 0 ≤ φ.1 y
    exact φ.2.1 y hy
  apply le_antisymm
  · intro x hx
    change N.mkQ x ∈ supportSpace D ⊥ at hx
    apply mem_supportSpace.2
    intro φ hφ
    have hf : (N.liftQ φ (by
        apply Submodule.span_le.2
        intro y hy
        exact hφ.2 y hy)) ∈ supportForms D ⊥ := by
      simpa using hdesc ⟨φ, hφ⟩
    have hz := mem_supportSpace.1 hx _ hf
    simpa only [Submodule.mkQ_apply, Submodule.liftQ_apply] using hz
  · intro x hx
    change N.mkQ x ∈ supportSpace D ⊥
    apply mem_supportSpace.2
    intro f hf
    apply mem_supportSpace.1 hx (f.comp N.mkQ)
    refine ⟨?_, ?_⟩
    · intro y hy
      exact hf.1 (N.mkQ y) ⟨y, hy, rfl⟩
    · intro y hy
      change f (N.mkQ y) = 0
      have hzero : N.mkQ y = 0 := (Submodule.Quotient.mk_eq_zero N).mpr
        (Submodule.subset_span hy)
      rw [hzero]
      exact f.map_zero

/-- **The projected-closed-cone form of the support space.** Compose the quotient bridge with the
closed-cone lineality identification. This is the object whose independence the isotropic affine
argument has to establish. -/
theorem supportSpace_map_mkQ_bot_eq_topologicalClosure_lineal [Module.Finite ℚ V]
    {τ σ : PointedCone ℝ (realified V)} :
    let N := Submodule.span ℝ (σ : Set (realified V))
    letI := IsModuleTopology.toContinuousAdd ℝ (realified V ⧸ N)
    (PointedCone.lineal (τ.map N.mkQ).topologicalClosure).comap N.mkQ = supportSpace τ σ := by
  let N := Submodule.span ℝ (σ : Set (realified V))
  letI : ContinuousAdd (realified V ⧸ N) := IsModuleTopology.toContinuousAdd ℝ _
  change (PointedCone.lineal (τ.map N.mkQ).topologicalClosure).comap N.mkQ = supportSpace τ σ
  rw [← supportSpace_map_mkQ_bot, supportSpace_bot_eq_topologicalClosure_lineal]

/-- **Quotienting by a line respects intersections of cones containing its generator.** If
`e ∈ τ` and `e ∈ K`, then `(τ ⊓ K).map mkQ = τ.map mkQ ⊓ K.map mkQ`. One inclusion is
functoriality. For the other, representatives `x ∈ τ` and `y ∈ K` of the same quotient point
satisfy `y - x = λ • e`. If `0 ≤ λ`, replace the `K`-representative by `y + λ • e = x`; if `λ < 0`,
replace the `τ`-representative by `x - λ • e = y`. -/
theorem map_inf_eq_inf_map_of_span_singleton {E : Type*} [AddCommGroup E] [Module ℝ E]
    {e : E} {τ K : PointedCone ℝ E} (heτ : e ∈ τ) (heK : e ∈ K) :
    let N := Submodule.span ℝ ({e} : Set E)
    (τ ⊓ K).map N.mkQ = τ.map N.mkQ ⊓ K.map N.mkQ := by
  let N := Submodule.span ℝ ({e} : Set E)
  change (τ ⊓ K).map N.mkQ = τ.map N.mkQ ⊓ K.map N.mkQ
  apply le_antisymm
  · intro z hz
    obtain ⟨x, hx, rfl⟩ := hz
    exact ⟨⟨x, hx.1, rfl⟩, ⟨x, hx.2, rfl⟩⟩
  · intro z hz
    obtain ⟨x, hx, rfl⟩ := hz.1
    obtain ⟨y, hy, hq⟩ := hz.2
    have hdiff' : x - y ∈ N := by
      simpa only [sub_eq_add_neg, add_comm] using (Submodule.Quotient.eq' N).mp hq
    have hdiff : y - x ∈ N := by simpa only [neg_sub] using N.neg_mem hdiff'
    obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.1 hdiff
    rcases lt_or_ge (0 : ℝ) r with hr0 | hr0
    · have hyτ : y ∈ τ := by
        have hm : x + r • e ∈ τ := τ.add_mem hx (τ.smul_mem hr0.le heτ)
        rw [hr] at hm
        convert hm using 1; abel
      exact ⟨y, ⟨hyτ, hy⟩, hq⟩
    · have hxK : x ∈ K := by
        have hm : y + (-r) • e ∈ K := K.add_mem hy (K.smul_mem (neg_nonneg.mpr hr0) heK)
        rw [neg_smul, hr] at hm
        convert hm using 1; abel
      exact ⟨x, ⟨hx, hxK⟩, rfl⟩

/-- **A face containing the quotienting ray projects to a face.**
LC-09 (2026-11-19): `content:PointedCone.IsFaceOf content:surjective`,
`content:face quotient convex cone nonnegative generator`, and
`content:PointedCone.IsFaceOf content:map` found only injective-map and fan APIs. The proof is
representative-level: a positive multiple of the quotienting ray repairs the two sides of a
conical combination according to the sign of the quotient difference. -/
theorem PointedCone.IsFaceOf.map_mkQ_span_singleton {E : Type*} [AddCommGroup E] [Module ℝ E]
    {e : E} {F C : PointedCone ℝ E} (he : e ∈ F) (hF : F.IsFaceOf C) :
    let N := Submodule.span ℝ ({e} : Set E)
    (F.map N.mkQ).IsFaceOf (C.map N.mkQ) := by
  let N := Submodule.span ℝ ({e} : Set E)
  change (F.map N.mkQ).IsFaceOf (C.map N.mkQ)
  refine ⟨Submodule.map_mono hF.le, ?_⟩
  intro x y a hx hy ha hxy
  obtain ⟨x', hx', rfl⟩ := hx
  obtain ⟨y', hy', rfl⟩ := hy
  obtain ⟨z', hz', hq⟩ := hxy
  have hdiff : a • x' + y' - z' ∈ N := by
    have hqN := (Submodule.Quotient.eq' N).mp hq
    simpa only [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hqN
  obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.1 hdiff
  rcases lt_or_ge (0 : ℝ) r with hr0 | hr0
  · have hzsum : z' + r • e = a • x' + y' := by
      rw [hr]
      abel
    have hcomb : a • x' + y' ∈ F :=
      hzsum ▸ F.add_mem hz' (F.smul_mem hr0.le he)
    exact ⟨x', hF.mem_of_smul_add_mem hx' hy' ha hcomb, rfl⟩
  · have hymem : y' + (-r) • e ∈ C :=
      C.add_mem hy' (C.smul_mem (neg_nonneg.mpr hr0) (hF.le he))
    have hsum : a • x' + (y' + (-r) • e) = z' := by
      calc
        a • x' + (y' + (-r) • e) = (a • x' + y') - r • e := by
          simp only [neg_smul, sub_eq_add_neg, add_assoc]
        _ = z' := by rw [hr]; abel
    exact ⟨x', hF.mem_of_smul_add_mem hx' hymem ha (hsum ▸ hz'), rfl⟩

/-- A projected neighborhood localizes a closure point to the projected intersection. This is the
`mem_closure_iff_nhds` form of `map_inf_eq_inf_map_of_span_singleton`; LC-09
(2026-11-19) found no separate declaration for this consequence. -/
theorem mem_topologicalClosure_map_inf_of_mem_nhds {E : Type*}
    [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    (N : Submodule ℝ E) {e : E} {A K : PointedCone ℝ E}
    (hN : N = Submodule.span ℝ ({e} : Set E))
    (heA : e ∈ A) (heK : e ∈ K) {y : E ⧸ N}
    (hyK : (K.map N.mkQ : Set (E ⧸ N)) ∈ 𝓝 y)
    (hyA : y ∈ closure ((A.map N.mkQ : PointedCone ℝ (E ⧸ N)) : Set (E ⧸ N))) :
    y ∈ closure (((A ⊓ K).map N.mkQ : PointedCone ℝ (E ⧸ N)) : Set (E ⧸ N)) := by
  subst N
  rw [mem_closure_iff_nhds] at hyA ⊢
  intro U hU
  obtain ⟨w, hw, hwA⟩ := hyA (U ∩ (K.map (Submodule.span ℝ ({e} : Set E)).mkQ :
    Set (E ⧸ Submodule.span ℝ ({e} : Set E)))) (Filter.inter_mem hU hyK)
  refine ⟨w, hw.1, ?_⟩
  rw [map_inf_eq_inf_map_of_span_singleton heA heK]
  exact ⟨hwA, hw.2⟩

/-- **Locality of the supporting forms at a point of `σ`.** If `K` is a neighbourhood of
`x ∈ σ`, then the cone `τ` and its trace `τ ⊓ K` have the same forms nonnegative on them and zero
on `σ`. For `y ∈ τ`, the points `x + t • y` lie in `τ` for `t ≥ 0` and in `K` for sufficiently
small positive `t`; the linearity of `φ` and `φ x = 0` turn nonnegativity at those points into
nonnegativity at `y`. -/
theorem supportForms_inf_eq_of_mem_nhds {τ σ K : PointedCone ℝ (realified V)}
    {x : realified V} (hστ : σ ≤ τ) (hxσ : x ∈ σ) (hK : (K : Set (realified V)) ∈ 𝓝 x) :
    supportForms (τ ⊓ K) σ = supportForms τ σ := by
  ext φ
  constructor
  · intro hφ
    rw [mem_supportForms] at hφ ⊢
    refine ⟨fun y hy => ?_, hφ.2⟩
    have hτx : x ∈ τ := hστ hxσ
    have htend : Filter.Tendsto (fun t : ℝ => x + t • y) (𝓝 0) (𝓝 x) := by
      have hcont : Continuous (fun t : ℝ => x + t • y) :=
        continuous_const.add (continuous_id.smul continuous_const)
      simpa only [zero_smul, add_zero] using hcont.tendsto (0 : ℝ)
    have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), x + t • y ∈ (K : Set (realified V)) :=
      mem_nhdsWithin_of_mem_nhds (htend.eventually hK)
    obtain ⟨t, htK, ht⟩ := (hev.and self_mem_nhdsWithin).exists
    have hmem : x + t • y ∈ τ ⊓ K :=
      ⟨τ.add_mem hτx (τ.smul_mem (Set.mem_Ioi.1 ht).le hy), htK⟩
    have hnonneg := hφ.1 (x + t • y) hmem
    rw [map_add, map_smul, hφ.2 x hxσ, smul_eq_mul, zero_add] at hnonneg
    exact nonneg_of_mul_nonneg_right hnonneg (Set.mem_Ioi.1 ht)
  · intro hφ
    rw [mem_supportForms] at hφ ⊢
    exact ⟨fun y hy => hφ.1 y hy.1, hφ.2⟩

/-- **The support space is local at a point of `σ`** (Looijenga's proof of Lemma-Definition 4.5,
p. 19): it does not change when `τ` is intersected with any cone that is a neighbourhood of a
point of `σ`. This is what allows the finite rational traces of Definition 4.2 to be used despite
the members themselves not being finitely generated. -/
theorem supportSpace_inf_eq_of_mem_nhds {τ σ K : PointedCone ℝ (realified V)}
    {x : realified V} (hστ : σ ≤ τ) (hxσ : x ∈ σ) (hK : (K : Set (realified V)) ∈ 𝓝 x) :
    supportSpace (τ ⊓ K) σ = supportSpace τ σ := by
  rw [supportSpace, supportSpace, supportForms_inf_eq_of_mem_nhds hστ hxσ hK]

/-- **Vanishing on a local common trace forces vanishing on the whole cone.** If `x ∈ σ`
and `K` is a neighbourhood of `x`, then a form vanishing on the common trace `A ⊓ B ⊓ K`
vanishes on `σ` whenever `σ ≤ A` and `σ ≤ B`. At `x` and at `x + t • y` for small positive `t`
it takes the same zero value; subtracting the two linear equations gives `t • w y = 0`. -/
theorem forall_mem_cone_eq_zero_of_zero_on_inf_of_mem_nhds
    {σ A B K : PointedCone ℝ (realified V)} {w : (realified V) →ₗ[ℝ] ℝ}
    {x : realified V} (hxσ : x ∈ σ) (hσA : σ ≤ A) (hσB : σ ≤ B)
    (hK : (K : Set (realified V)) ∈ 𝓝 x) (hw : ∀ z ∈ A ⊓ B ⊓ K, w z = 0) :
    ∀ y ∈ σ, w y = 0 := by
  intro y hy
  have hxK : x ∈ K := mem_of_mem_nhds hK
  have hxABK : x ∈ A ⊓ B ⊓ K := ⟨⟨hσA hxσ, hσB hxσ⟩, hxK⟩
  have hwx : w x = 0 := hw x hxABK
  have htend : Filter.Tendsto (fun t : ℝ => x + t • y) (𝓝 0) (𝓝 x) := by
    have hcont : Continuous (fun t : ℝ => x + t • y) :=
      continuous_const.add (continuous_id.smul continuous_const)
    simpa only [zero_smul, add_zero] using hcont.tendsto (0 : ℝ)
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), x + t • y ∈ (K : Set (realified V)) :=
    mem_nhdsWithin_of_mem_nhds (htend.eventually hK)
  obtain ⟨t, htK, ht⟩ := (hev.and self_mem_nhdsWithin).exists
  have hmem : x + t • y ∈ A ⊓ B ⊓ K := by
    refine ⟨⟨A.add_mem (hσA hxσ) (A.smul_mem (Set.mem_Ioi.1 ht).le (hσA hy)),
      B.add_mem (hσB hxσ) (B.smul_mem (Set.mem_Ioi.1 ht).le (hσB hy))⟩, htK⟩
  have hzero := hw (x + t • y) hmem
  rw [map_add, map_smul, hwx, smul_eq_mul, zero_add] at hzero
  exact (mul_eq_zero.1 hzero).resolve_left (Set.mem_Ioi.1 ht).ne'

/-- The members of a decomposition that contain `σ` and meet the open cone `C`:
the cones `τ` over which Looijenga, Lemma-Definition 4.5, p. 19, states the support space. -/
def supportIndex (C : PointedCone ℝ (realified V)) (S : Set (PointedCone ℝ (realified V)))
    (σ : PointedCone ℝ (realified V)) : Type u :=
  {τ : PointedCone ℝ (realified V) // τ ∈ S ∧ σ ≤ τ ∧
    ((τ : Set (realified V)) ∩ (C : Set (realified V))).Nonempty}

/-- The support space of `σ` in a decomposition. Looijenga's Lemma-Definition 4.5, p. 19,
gives `L_σ` as the common value of `supportSpace τ σ` over the members `τ ≥ σ` meeting `C`;
that common value is carried here as their intersection. -/
noncomputable def sigmaSupportSpace (C : PointedCone ℝ (realified V))
    (S : Set (PointedCone ℝ (realified V))) (σ : PointedCone ℝ (realified V)) :
    Submodule ℝ (realified V) :=
  ⨅ (τ : supportIndex C S σ), supportSpace τ.1 σ

/-- The support space of `σ` is contained in the space of every member above it. -/
theorem sigmaSupportSpace_le {C : PointedCone ℝ (realified V)}
    {S : Set (PointedCone ℝ (realified V))} {σ τ : PointedCone ℝ (realified V)}
    (hτ : τ ∈ S) (hστ : σ ≤ τ)
    (hC : ((τ : Set (realified V)) ∩ (C : Set (realified V))).Nonempty) :
    sigmaSupportSpace C S σ ≤ supportSpace τ σ :=
  iInf_le (fun τ : supportIndex C S σ => supportSpace τ.1 σ) ⟨τ, hτ, hστ, hC⟩

/-- The support space of `σ` contains the span of `σ`. -/
theorem span_le_sigmaSupportSpace {C : PointedCone ℝ (realified V)}
    {S : Set (PointedCone ℝ (realified V))} {σ : PointedCone ℝ (realified V)}
    (_τ : supportIndex C S σ) :
    Submodule.span ℝ (σ : Set (realified V)) ≤ sigmaSupportSpace C S σ :=
  le_iInf fun τ' => span_le_supportSpace τ'.2.2.1

/-- **The support space of a cone that meets the open cone is the span of that cone**: the
member `σ` itself is one of the cones over which the intersection is taken, and its space is
`span σ` (Looijenga, Lemma-Definition 4.5, p. 19). -/
theorem sigmaSupportSpace_eq_span_of_meets {C : PointedCone ℝ (realified V)}
    {S : Set (PointedCone ℝ (realified V))} {σ : PointedCone ℝ (realified V)}
    (hσ : σ ∈ S) (hC : ((σ : Set (realified V)) ∩ (C : Set (realified V))).Nonempty) :
    sigmaSupportSpace C S σ = Submodule.span ℝ (σ : Set (realified V)) := by
  refine le_antisymm ?_ (span_le_sigmaSupportSpace ⟨σ, hσ, le_rfl, hC⟩)
  exact (sigmaSupportSpace_le (σ := σ) (τ := σ) hσ le_rfl hC).trans_eq (supportSpace_self σ)


/-! ## Lemma-Definition 4.5: the independence of the support space from `τ`

Looijenga, Lemma-Definition 4.5, p. 19: for `τ ∈ Σ` with `τ ≥ σ` and `τ ∩ C ≠ ∅`, the common zero
set of the real linear forms nonnegative on `τ` and zero on `σ` does not depend on `τ`. For the
facial decomposition `Σ(bb)` every member meeting `C` is `C₊` itself
(`eq_of_isFaceOf_of_meets_open_sheet`: a face of `C₊` containing a point of the open cone is all of
`C₊`, for an *arbitrary* point of `C`, not only a rational one), so the independence is
immediate there (`supportSpace_eq_of_meets_openSheet`). The source's argument for a general `Σ`,
where `σ` spans an isotropic half line and the proof runs through the projection `π_I` on
`I^⊥/I` (p. 19), is carried in the form and in the cone, and not through its affine model: see the
section "The connectivity of a locally finite decomposition through common faces" below.

The step that replaces the rational case: a nonnegative combination of rational points of the
closed sheet that is timelike has a sub-combination that is timelike
(`exists_pos_pair_sum`), found by cutting one term at a time off the finite sum with the
two-term quadratic expansion. -/

section SupportSpaceIndependence

variable [Module.Finite ℚ V] {Q : QuadraticForm ℝ (realified V)} {t : realified V}

theorem pos_associated_of_mem_closedSheet (hpos : sigPos Q = 1) (ht : 0 < Q t) {x : realified V}
    (hQx : 0 < Q x) (hxt : 0 ≤ (associated Q) x t) : 0 < (associated Q) x t := by
  rcases lt_or_eq_of_le hxt with h | h
  · exact h
  · exfalso
    have hle := mul_self_le_associated_sq (Q := Q) hpos ht x
    rw [← h] at hle
    nlinarith

/-- **A nonnegative combination of closed-sheet vectors with nonnegative pairwise pairings has a
positive value of `Q` only if one of the vectors has, or two of them pair positively**: the
quadratic expansion of a two-term sum cuts one term at a time off a finite sum. -/
theorem exists_pos_pair_sum (hpos : sigPos Q = 1) (ht : 0 < Q t) {ι : Type*}
    {s : Finset ι} {c : ι → ℝ} {a : ι → realified V}
    (hc : ∀ i ∈ s, 0 ≤ c i)
    (hsheet : ∀ i ∈ s, a i ∈ closedSheet Q hpos ht)
    (hpair : ∀ i ∈ s, ∀ j ∈ s, 0 ≤ (associated Q) (a i) (a j))
    (hpos' : 0 < Q (∑ i ∈ s, c i • a i)) :
    (∃ i ∈ s, 0 < Q (a i)) ∨
      (∃ i ∈ s, ∃ j ∈ s, i ≠ j ∧ 0 < (associated Q) (a i) (a j)) := by
  classical
  induction s using Finset.induction with
  | empty => simp at hpos'
  | insert x s hx ih =>
    rw [Finset.sum_insert hx] at hpos'
    set S : realified V := ∑ i ∈ s, c i • a i with hS
    have hxmem : x ∈ insert x s := Finset.mem_insert_self x s
    have hxsheet : a x ∈ closedSheet Q hpos ht := hsheet x hxmem
    have hSsheet : S ∈ closedSheet Q hpos ht := by
      refine Submodule.sum_mem _ fun i hi => ?_
      exact PointedCone.smul_mem _ (hc i (Finset.mem_insert_of_mem hi))
        (hsheet i (Finset.mem_insert_of_mem hi))
    have hxS : 0 ≤ (associated Q) (a x) S := by
      rw [hS, map_sum]
      refine Finset.sum_nonneg fun i hi => ?_
      rw [map_smul, smul_eq_mul]
      exact mul_nonneg (hc i (Finset.mem_insert_of_mem hi))
        (hpair x hxmem i (Finset.mem_insert_of_mem hi))
    have hexp : Q (c x • a x + S)
        = (c x) ^ 2 * Q (a x) + 2 * (c x) * ((associated Q) (a x) S) + Q S := by
      have h := quadratic_expand Q (c x) 1 (a x) S
      simpa using h
    rw [hexp] at hpos'
    have h1 : 0 ≤ (c x) ^ 2 * Q (a x) := mul_nonneg (sq_nonneg _) hxsheet.1
    have h2 : 0 ≤ 2 * (c x) * ((associated Q) (a x) S) :=
      mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) (hc x hxmem)) hxS
    have h3 : 0 ≤ Q S := hSsheet.1
    rcases lt_or_ge (0:ℝ) ((c x) ^ 2 * Q (a x)) with h | h
    · refine Or.inl ⟨x, hxmem, ?_⟩
      nlinarith [sq_nonneg (c x)]
    · rcases lt_or_ge (0:ℝ) (2 * (c x) * ((associated Q) (a x) S)) with h2' | h2'
      · have hBS : (associated Q) (a x) S = ∑ i ∈ s, c i * (associated Q) (a x) (a i) := by
          rw [hS, map_sum]
          exact Finset.sum_congr rfl fun i _ => by rw [map_smul, smul_eq_mul]
        rw [hBS] at h2'
        have hterms : ∀ i ∈ s, 0 ≤ c i * (associated Q) (a x) (a i) := fun i hi =>
          mul_nonneg (hc i (Finset.mem_insert_of_mem hi))
            (hpair x hxmem i (Finset.mem_insert_of_mem hi))
        have hcx2 : (0:ℝ) ≤ 2 * c x :=
          mul_nonneg (by norm_num : (0:ℝ) ≤ 2) (hc x hxmem)
        have hsumpos : 0 < ∑ i ∈ s, c i * (associated Q) (a x) (a i) := by
          rcases lt_or_ge (0:ℝ) (∑ i ∈ s, c i * (associated Q) (a x) (a i)) with hh | hh
          · exact hh
          · exfalso
            have hle : 2 * c x * (∑ i ∈ s, c i * (associated Q) (a x) (a i)) ≤ 0 :=
              mul_nonpos_of_nonneg_of_nonpos hcx2 hh
            linarith
        have hex : ∃ i ∈ s, 0 < c i * (associated Q) (a x) (a i) := by
          by_contra hcon
          push Not at hcon
          have hle := Finset.sum_nonpos hcon
          linarith
        obtain ⟨i, hi, hipos⟩ := hex
        refine Or.inr ⟨x, hxmem, i, Finset.mem_insert_of_mem hi, ?_, ?_⟩
        · intro hxi
          rw [← hxi] at hi
          exact hx hi
        · rcases mul_pos_iff.1 hipos with ⟨-, hh⟩ | ⟨hh, -⟩
          · exact hh
          · exact absurd hh (not_lt.2 (hc i (Finset.mem_insert_of_mem hi)))
      · have h := ih (fun i hi => hc i (Finset.mem_insert_of_mem hi))
          (fun i hi => hsheet i (Finset.mem_insert_of_mem hi))
          (fun i hi j hj => hpair i (Finset.mem_insert_of_mem hi) j
            (Finset.mem_insert_of_mem hj)) (by nlinarith)
        rcases h with ⟨i, hi, hpos⟩ | ⟨i, hi, j, hj, hne, hpos⟩
        · exact Or.inl ⟨i, Finset.mem_insert_of_mem hi, hpos⟩
        · exact Or.inr ⟨i, Finset.mem_insert_of_mem hi, j, Finset.mem_insert_of_mem hj, hne, hpos⟩

/-- **A face of `C₊` that meets the open cone `C` is `C₊` itself** (Looijenga, p. 19, the proof of
Lemma-Definition 4.5, for an arbitrary point of `C` and not only a rational one): the face is
spanned by the rational points of the closed sheet lying in it, a nonnegative combination of those
that is timelike has a sub-combination that is timelike, and a face containing a rational point of
the open sheet is all of `C₊` (`eq_of_isFaceOf_of_mem_pos_closedSheet`). -/
theorem eq_of_isFaceOf_of_meets_open_sheet (hpos : sigPos Q = 1)
    {t : realified V} (ht : 0 < Q t)
    (hcl : ∀ v : V, rationalPoint v ∈ (closedSheet Q hpos ht).closure →
      0 ≤ Q (rationalPoint v) ∧ 0 ≤ (associated Q) (rationalPoint v) t)
    {F : PointedCone ℝ (realified V)}
    (hF : F.IsFaceOf (rationalClosure (closedSheet Q hpos ht)))
    (hne : ((F : Set (realified V)) ∩ (positiveCone.upper Q t : Set (realified V))).Nonempty) :
    F = rationalClosure (closedSheet Q hpos ht) := by
  classical
  obtain ⟨u, huF, huC⟩ := hne
  obtain ⟨huQ, huB⟩ := huC
  have hFhull : F = PointedCone.hull ℝ (rationalBoundary (closedSheet Q hpos ht) ∩
      (F : Set (realified V))) :=
    hF.eq_hull_inter_of_eq_hull (rationalClosure_eq_hull _)
  rw [hFhull] at huF
  obtain ⟨n, f, g, hgsum⟩ := Submodule.mem_span_set'.1 huF
  choose v hv using fun i => (g i).2.1.1
  set a : Fin n → realified V := fun i => ((g i) : realified V) with hadef
  have hav : ∀ i, a i = rationalPoint (v i) := fun i => (hv i).2.symm
  have hsheetClosed : ∀ i, a i ∈ closedSheet Q hpos ht := by
    intro i
    have hclos : a i ∈ (closedSheet Q hpos ht).closure := (g i).2.1.2
    rw [hav i] at hclos ⊢
    exact hcl (v i) hclos
  have haF : ∀ i, a i ∈ F := fun i => (g i).2.2
  set c : Fin n → ℝ := fun i => ((f i : Nonneg ℝ) : ℝ) with hcdef
  have hc : ∀ i, 0 ≤ c i := fun i => (f i).2
  have hpair : ∀ i j, 0 ≤ (associated Q) (a i) (a j) := fun i j =>
    nonneg_associated_of_mem_closedSheet hpos ht (hsheetClosed i).1 (hsheetClosed i).2
      (hsheetClosed j).1 (hsheetClosed j).2
  have hae : ∀ i, a i = ((g i) : realified V) := fun i => rfl
  have hsum : ∑ i, c i • a i = u := by
    rw [← hgsum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [show a i = ((g i) : realified V) from rfl]
    exact Nonneg.coe_smul _ _
  have hpossum : 0 < Q (∑ i, c i • a i) := by
    rw [hsum]
    exact huQ
  rcases exists_pos_pair_sum (Q := Q) hpos ht (s := Finset.univ) (fun i _ => hc i)
    (fun i _ => hsheetClosed i) (fun i _ j _ => hpair i j) hpossum with
    ⟨i, -, hiQ⟩ | ⟨i, -, j, -, hij, hijB⟩
  · have hub : 0 < (associated Q) (a i) t :=
      pos_associated_of_mem_closedSheet hpos ht hiQ (hsheetClosed i).2
    exact eq_of_isFaceOf_of_mem_pos_closedSheet (Q := Q) hpos ht hcl
      (u := v i) (by rw [← hav i]; exact hiQ) (by rw [← hav i]; exact hub) hF
      (by rw [← hav i]; exact haF i)
  · have hsummem : a i + a j ∈ F := F.add_mem (haF i) (haF j)
    have hQsum : 0 < Q (a i + a j) := by
      have hexp := quadratic_expand Q 1 1 (a i) (a j)
      simp only [one_smul, one_pow, one_mul] at hexp
      rw [hexp]
      nlinarith [(hsheetClosed i).1, (hsheetClosed j).1, hijB]
    have hBsum : 0 ≤ (associated Q) (a i + a j) t := by
      rw [map_add, LinearMap.add_apply]
      linarith [(hsheetClosed i).2, (hsheetClosed j).2]
    have hub : 0 < (associated Q) (a i + a j) t :=
      pos_associated_of_mem_closedSheet hpos ht hQsum hBsum
    have hrat : a i + a j = rationalPoint (v i + v j) := by
      rw [hav i, hav j, map_add]
    exact eq_of_isFaceOf_of_mem_pos_closedSheet (Q := Q) hpos ht hcl
      (u := v i + v j) (by rw [← hrat]; exact hQsum) (by rw [← hrat]; exact hub) hF
      (by rw [← hrat]; exact hsummem)

/-- **Lemma-Definition 4.5's independence of `τ` for the facial decomposition** (Looijenga, p. 19):
the support space of `σ` is the same for every member `τ ≥ σ` of `Σ(bb)` that meets the open cone,
because such a `τ` is `C₊` itself. -/
theorem supportSpace_eq_of_meets_openSheet (hpos : sigPos Q = 1)
    {t : realified V} (ht : 0 < Q t)
    (hcl : ∀ v : V, rationalPoint v ∈ (closedSheet Q hpos ht).closure →
      0 ≤ Q (rationalPoint v) ∧ 0 ≤ (associated Q) (rationalPoint v) t)
    {σ τ τ' : PointedCone ℝ (realified V)}
    (hτ : τ ∈ facialDecomposition (rationalClosure (closedSheet Q hpos ht)))
    (hτC : ((τ : Set (realified V)) ∩ (positiveCone.upper Q t : Set (realified V))).Nonempty)
    (hτ' : τ' ∈ facialDecomposition (rationalClosure (closedSheet Q hpos ht)))
    (hτ'C : ((τ' : Set (realified V)) ∩ (positiveCone.upper Q t : Set (realified V))).Nonempty) :
    supportSpace τ σ = supportSpace τ' σ := by
  rw [eq_of_isFaceOf_of_meets_open_sheet (Q := Q) hpos ht hcl hτ hτC,
    eq_of_isFaceOf_of_meets_open_sheet (Q := Q) hpos ht hcl hτ' hτ'C]


end SupportSpaceIndependence

/-! ## Lemma-Definition 4.5, the isotropic case: the projection by the line `I`

Looijenga, the proof of Lemma-Definition 4.5, p. 19 (text version
`.tmp-sources/looijenga-math0201218v2.md:521`): "So let us assume that `σ` spans an isotropic
line `I`. We observe that the image of `C` under the projection `π_I : L → L/I` is a real
half-space bounded by `(I^⊥/I)(ℝ)`. The image of `C₊` under this projection is the union of
that half-space plus the origin; we prefer to think of this image as a cone over a real affine
space `A_I(ℝ)` over `(I ⊗ I^⊥/I)(ℝ)`."

This section carries that first observation: the functional `x ↦ e · x` of an isotropic vector
kills the line `ℝ e` (`e · e = 0`), so it descends to a functional `β` on `L(ℝ)/I`, and the
open sheet `C` maps *onto* the open half-space `{u | 0 < β u}`. The affine space `A_I(ℝ)` is an
affine space over `I^⊥/I`, whose form is the business of
`LeanCategories/Lattices/Valued/IsotropicQuotientSignature.lean` (its `isotropicQuotientForm`
is the quadratic form on that subquotient, not the functional `β` here). The half-space is the
space `A_I(ℝ)` that the rest of the source's argument decomposes into polyhedra; the
decomposition itself — the cones of `Σ` above `σ` projected to polyhedra, their minimal members,
and the translation space `U` whose preimage is `L_σ` — is not carried. What that decomposition
yields, the independence of `L_σ` from the member, is carried in the form and the cone in the
section "The connectivity of a locally finite decomposition through common faces" below, whose
`σ` is not assumed to span an isotropic half line.

The proof of the image statement is in two halves. A point of the open sheet pairs positively
with every nonzero point of the closed sheet (`associated_pos_of_mem_upper_of_mem_closedSheet`),
which is `associated_pos_of_mem_upper` when the second point is timelike and otherwise a limit
along `t` together with `eq_zero_of_perp_of_quadratic_eq_zero`; that gives the inclusion
`π_I(C) ⊆ {0 < β}`. For the reverse inclusion, `Q` and `x ↦ x · t` are both unbounded above
along `y + a • e` (because `e` is isotropic and pairs positively with `t`), so every class with
`0 < β` has a timelike representative. -/

section IsotropicProjection

variable {Q : QuadraticForm ℝ (realified V)} {t e : realified V}

/-- **`σ` spans an isotropic half line** (Looijenga, Lemma-Definition 4.5, p. 19): it is the ray
through a nonzero isotropic vector. This is the case in which the support space of `σ` is not
the span of `σ`, and the one the proof of Lemma-Definition 4.5 is about. -/
def IsIsotropicHalfLine (Q : QuadraticForm ℝ (realified V))
    (σ : PointedCone ℝ (realified V)) : Prop :=
  ∃ e : realified V, e ≠ 0 ∧ Q e = 0 ∧ σ = PointedCone.hull ℝ ({e} : Set (realified V))

/-- The generator of an isotropic half line lies on it. -/
theorem IsIsotropicHalfLine.subset (hσ : IsIsotropicHalfLine Q σ) :
    ∃ e : realified V, e ≠ 0 ∧ Q e = 0 ∧ e ∈ σ := by
  obtain ⟨e, he0, he, rfl⟩ := hσ
  exact ⟨e, he0, he, PointedCone.subset_hull (Set.mem_singleton e)⟩

/-- The isotropic line `I` that an isotropic half line spans: the span of the ray is the span of
its generator. -/
theorem IsIsotropicHalfLine.span_eq (hσ : IsIsotropicHalfLine Q σ) :
    ∃ e : realified V, e ≠ 0 ∧ Q e = 0 ∧
      Submodule.span ℝ (σ : Set (realified V)) = Submodule.span ℝ ({e} : Set (realified V)) := by
  obtain ⟨e, he0, he, rfl⟩ := hσ
  refine ⟨e, he0, he, le_antisymm ?_ ?_⟩
  · refine Submodule.span_le.2 fun x hx => ?_
    exact PointedCone.hull_le_span ℝ _ hx
  · refine Submodule.span_le.2 fun x hx => ?_
    exact Submodule.subset_span (PointedCone.subset_hull (Set.mem_singleton_iff.2 hx))

/-- The functional `x ↦ e · x` of an isotropic vector `e` kills the line `ℝ e`, so it descends to
the quotient `L(ℝ)/I`: the functional `β` of the proof of Lemma-Definition 4.5, p. 19. -/
noncomputable def isotropicHalfspaceForm (Q : QuadraticForm ℝ (realified V)) {e : realified V}
    (he : Q e = 0) :
    (realified V ⧸ Submodule.span ℝ ({e} : Set (realified V))) →ₗ[ℝ] ℝ :=
  Submodule.liftQ (p := Submodule.span ℝ ({e} : Set (realified V))) ((associated Q) e) (by
    rw [Submodule.span_singleton_le_iff_mem, LinearMap.mem_ker, associated_self_apply]
    exact he)

/-- The functional of the quotient at a class is the pairing with `e` at a representative. -/
theorem isotropicHalfspaceForm_mkQ (Q : QuadraticForm ℝ (realified V)) {e : realified V}
    (he : Q e = 0) (x : realified V) :
    isotropicHalfspaceForm Q he ((Submodule.span ℝ ({e} : Set (realified V))).mkQ x)
      = (associated Q) e x := by
  rw [isotropicHalfspaceForm, Submodule.mkQ_apply, Submodule.liftQ_apply]

variable [Module.Finite ℚ V]

/-- **A timelike point of the open sheet pairs positively with every nonzero point of the closed
sheet.** The timelike case is `associated_pos_of_mem_upper`; the isotropic one is a limit along
the positive vector `t`, and a vanishing pairing would make the point perpendicular to a
timelike vector with `Q = 0`, hence zero. -/
theorem associated_pos_of_mem_upper_of_mem_closedSheet (Q : QuadraticForm ℝ (realified V))
    (hpos : sigPos Q = 1) (hnd : Q.Nondegenerate) {t x y : realified V} (ht : 0 < Q t)
    (hx : x ∈ positiveCone.upper Q t) (hy : y ∈ closedSheet Q hpos ht) (hy0 : y ≠ 0) :
    0 < (associated Q) x y := by
  have hQx : 0 < Q x := hx.1
  have hxt : 0 < (associated Q) x t := hx.2
  have hQy : 0 ≤ Q y := hy.1
  have hyt : 0 ≤ (associated Q) y t := hy.2
  have hyt' : 0 < (associated Q) y t := by
    rcases lt_or_eq_of_le hyt with h | h
    · exact h
    · exfalso
      rcases lt_or_eq_of_le hQy with hQ | hQ
      · have hkey := mul_self_le_associated_sq (Q := Q) hpos ht y
        rw [← h] at hkey
        nlinarith
      · exact hy0 (eq_zero_of_perp_of_quadratic_eq_zero hpos hnd ht h.symm hQ.symm)
  rcases lt_or_eq_of_le hQy with hQ | hQ
  · exact associated_pos_of_mem_upper Q hpos ht hx ⟨hQ, hyt'⟩
  · by_cases hB : 0 ≤ (associated Q) x y
    · rcases lt_or_eq_of_le hB with h | h
      · exact h
      · exfalso
        have hyx : (associated Q) y x = 0 := by rw [associated_comm]; exact h.symm
        exact hy0 (eq_zero_of_perp_of_quadratic_eq_zero hpos hnd hQx hyx hQ.symm)
    · push Not at hB
      set eps : ℝ := -(associated Q) x y / (2 * (associated Q) x t) with heps
      have hepspos : 0 < eps := by
        rw [heps]
        exact div_pos (by linarith) (by linarith)
      have hmem : y + eps • t ∈ positiveCone.upper Q t := by
        refine ⟨?_, ?_⟩
        · rw [show y + eps • t = (1 : ℝ) • y + eps • t by rw [one_smul]]
          rw [quadratic_expand, hQ]
          nlinarith [mul_pos hepspos hyt', mul_pos (mul_pos hepspos hepspos) ht]
        · have h1 : (associated Q) (y + eps • t) t
              = (associated Q) y t + eps * (associated Q) t t := by
            rw [associated_comm (Q := Q) (y + eps • t) t, map_add, map_smul, smul_eq_mul,
              associated_comm (Q := Q) y t]
          rw [h1, associated_self_apply]
          nlinarith [mul_pos hepspos ht]
      have hpos' := associated_pos_of_mem_upper Q hpos ht hx hmem
      have h2 : (associated Q) x (y + eps • t)
          = (associated Q) x y + eps * (associated Q) x t := by
        simp only [map_add, map_smul, smul_eq_mul]
      rw [h2] at hpos'
      have h3 : eps * (associated Q) x t = -(associated Q) x y / 2 := by
        rw [heps]; field_simp
      rw [h3] at hpos'
      linarith

/-- **The image of the open cone under `π_I` is a real half-space**: Looijenga's observation in
the proof of Lemma-Definition 4.5, p. 19, that the image of `C` under `π_I : L → L/I` is the
half-space bounded by `(I^⊥/I)(ℝ)` — here the half-space `{u | 0 < e · u}` of the quotient by
the isotropic line `ℝ e`. -/
theorem image_mkQ_upper_eq (Q : QuadraticForm ℝ (realified V)) (hpos : sigPos Q = 1)
    (hnd : Q.Nondegenerate) {t e : realified V} (ht : 0 < Q t) (he0 : e ≠ 0) (he : Q e = 0)
    (het : 0 ≤ (associated Q) e t) :
    (Submodule.span ℝ ({e} : Set (realified V))).mkQ '' (positiveCone.upper Q t) =
      {u | 0 < isotropicHalfspaceForm Q he u} := by
  ext u
  constructor
  · rintro ⟨x, hx, rfl⟩
    show 0 < isotropicHalfspaceForm Q he ((Submodule.span ℝ ({e} : Set (realified V))).mkQ x)
    rw [isotropicHalfspaceForm_mkQ, associated_comm]
    exact associated_pos_of_mem_upper_of_mem_closedSheet Q hpos hnd ht hx ⟨he.ge, het⟩ he0
  · rintro hu
    obtain ⟨y, hy⟩ := Submodule.mkQ_surjective (Submodule.span ℝ ({e} : Set (realified V))) u
    have hBy : 0 < (associated Q) y e := by
      have h1 : 0 < isotropicHalfspaceForm Q he
          ((Submodule.span ℝ ({e} : Set (realified V))).mkQ y) := by
        rw [hy]; exact hu
      rwa [isotropicHalfspaceForm_mkQ, associated_comm] at h1
    have het' : 0 < (associated Q) e t := by
      rcases lt_or_eq_of_le het with h | h
      · exact h
      · exact absurd (eq_zero_of_perp_of_quadratic_eq_zero hpos hnd ht h.symm he) he0
    -- a shift along `e` far enough out on both sides
    obtain ⟨N₁, hN₁⟩ := exists_nat_gt (-(Q y) / (2 * (associated Q) y e))
    obtain ⟨N₂, hN₂⟩ := exists_nat_gt (-((associated Q) y t) / (associated Q) e t)
    set a : ℝ := ((max N₁ N₂ : ℕ) : ℝ) with ha
    have hNa1 : (N₁ : ℝ) ≤ a := by
      rw [ha]; exact_mod_cast le_max_left N₁ N₂
    have hNa2 : (N₂ : ℝ) ≤ a := by
      rw [ha]; exact_mod_cast le_max_right N₁ N₂
    have ha1 : -(Q y) / (2 * (associated Q) y e) < a := lt_of_lt_of_le hN₁ hNa1
    have ha2 : -((associated Q) y t) / (associated Q) e t < a := lt_of_lt_of_le hN₂ hNa2
    have haQ : 0 < Q y + 2 * a * (associated Q) y e := by
      have h1 : -(Q y) < a * (2 * (associated Q) y e) := by
        rw [div_lt_iff₀ (show (0 : ℝ) < 2 * (associated Q) y e by positivity)] at ha1
        linarith
      linarith
    have hat : 0 < (associated Q) y t + a * (associated Q) e t := by
      have h1 : -((associated Q) y t) < a * (associated Q) e t := by
        rw [div_lt_iff₀ het'] at ha2
        linarith
      linarith
    refine ⟨y + a • e, ⟨?_, ?_⟩, ?_⟩
    · rw [show y + a • e = (1 : ℝ) • y + a • e by rw [one_smul]]
      rw [quadratic_expand, he]
      nlinarith [haQ]
    · have h2 : (associated Q) (y + a • e) t
          = (associated Q) y t + a * (associated Q) e t := by
        rw [associated_comm (Q := Q) (y + a • e) t, map_add, map_smul, smul_eq_mul,
          associated_comm (Q := Q) y t, ← associated_comm (Q := Q) t e]
      rw [h2]
      exact hat
    · have hzero : (Submodule.span ℝ ({e} : Set (realified V))).mkQ e = 0 := by
        rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
        exact Submodule.subset_span (Set.mem_singleton e)
      rw [map_add, map_smul, hzero, smul_zero, add_zero]
      exact hy

/-- **The image of `C₊` under `π_I` lies in the closed half-space**: the "plus the origin" of
Looijenga's description (the proof of Lemma-Definition 4.5, p. 19). `C₊` is spanned by the
rational points of the closure of `C`, where the pairing with `e` is nonnegative by the
continuity input `hbe` — the counterpart, for this pairing, of the hypothesis `hcl` of the
hyperbolic section. -/
theorem image_mkQ_rationalClosure_subset (Q : QuadraticForm ℝ (realified V)) (hpos : sigPos Q = 1)
    {t e : realified V} (ht : 0 < Q t) (he : Q e = 0)
    (hbe : ∀ v : V, rationalPoint v ∈ (closedSheet Q hpos ht).closure →
      0 ≤ (associated Q) e (rationalPoint v)) :
    (Submodule.span ℝ ({e} : Set (realified V))).mkQ ''
        (rationalClosure (closedSheet Q hpos ht) : Set (realified V))
      ⊆ {u | 0 ≤ isotropicHalfspaceForm Q he u} := by
  rintro _ ⟨x, hx, rfl⟩
  rw [rationalClosure_eq_hull] at hx
  induction hx using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨⟨v, -, rfl⟩, hvcl⟩ := hz
    show 0 ≤ isotropicHalfspaceForm Q he ((Submodule.span ℝ ({e} : Set (realified V))).mkQ
      (rationalPoint v))
    rw [isotropicHalfspaceForm_mkQ]
    exact hbe v hvcl
  | zero =>
    show 0 ≤ isotropicHalfspaceForm Q he
      ((Submodule.span ℝ ({e} : Set (realified V))).mkQ 0)
    rw [map_zero, map_zero]
  | add u w _ _ hu hw =>
    show 0 ≤ isotropicHalfspaceForm Q he
      ((Submodule.span ℝ ({e} : Set (realified V))).mkQ (u + w))
    have hu' : 0 ≤ isotropicHalfspaceForm Q he
        ((Submodule.span ℝ ({e} : Set (realified V))).mkQ u) := by simpa using hu
    have hw' : 0 ≤ isotropicHalfspaceForm Q he
        ((Submodule.span ℝ ({e} : Set (realified V))).mkQ w) := by simpa using hw
    have hmap : isotropicHalfspaceForm Q he
          ((Submodule.span ℝ ({e} : Set (realified V))).mkQ u
            + (Submodule.span ℝ ({e} : Set (realified V))).mkQ w)
        = isotropicHalfspaceForm Q he ((Submodule.span ℝ ({e} : Set (realified V))).mkQ u)
          + isotropicHalfspaceForm Q he ((Submodule.span ℝ ({e} : Set (realified V))).mkQ w) :=
      map_add _ _ _
    have hsplit : (Submodule.span ℝ ({e} : Set (realified V))).mkQ (u + w)
        = (Submodule.span ℝ ({e} : Set (realified V))).mkQ u
          + (Submodule.span ℝ ({e} : Set (realified V))).mkQ w := map_add _ _ _
    rw [hsplit, hmap]
    exact add_nonneg hu' hw'
  | smul c u _ hu =>
    show 0 ≤ isotropicHalfspaceForm Q he
      ((Submodule.span ℝ ({e} : Set (realified V))).mkQ (c • u))
    rw [show c • u = c.1 • u from rfl, map_smul, map_smul, smul_eq_mul]
    exact mul_nonneg c.2 (by simpa using hu)

/-- **A cone of `C₊` projects into the closed half-space**: "any `τ ∈ Σ` with `σ < τ` maps under
`π_I` to a (possibly degenerate) convex cone in `π_I(C₊)`" (Looijenga, the proof of
Lemma-Definition 4.5, p. 19). -/
theorem image_mkQ_subset_of_le_rationalClosure (Q : QuadraticForm ℝ (realified V))
    (hpos : sigPos Q = 1) {t e : realified V} (ht : 0 < Q t) (he : Q e = 0)
    (hbe : ∀ v : V, rationalPoint v ∈ (closedSheet Q hpos ht).closure →
      0 ≤ (associated Q) e (rationalPoint v))
    {τ : PointedCone ℝ (realified V)} (hτ : τ ≤ rationalClosure (closedSheet Q hpos ht)) :
    (Submodule.span ℝ ({e} : Set (realified V))).mkQ '' (τ : Set (realified V))
      ⊆ {u | 0 ≤ isotropicHalfspaceForm Q he u} :=
  Set.Subset.trans (Set.image_mono hτ)
    (image_mkQ_rationalClosure_subset Q hpos ht he hbe)

end IsotropicProjection

/-! ## Lemma-Definition 4.5, the general case: the independence of `L_σ` from `τ`

Looijenga, Lemma-Definition 4.5, p. 19 (text version
`.tmp-sources/looijenga-math0201218v2.md:519`), and its proof (line 521): for `σ ∈ Σ` and any
`τ ∈ Σ` with `τ ≥ σ` and `τ ∩ C ≠ ∅`, the common zero set of the real linear forms that are
nonnegative on `τ` and zero on `σ` does not depend on `τ`; the source calls the common value the
`Σ`-support space `L_σ`.

The case the source's proof is about is `σ` spanning an isotropic line `I`, and what it consumes
there is: the projection `π_I : L → L/I` (carried above, `image_mkQ_upper_eq` and
`image_mkQ_subset_of_le_rationalClosure`), the polyhedra that the cones `τ > σ` determine in the
affine space `A_I(ℝ)`, the minimal member of that decomposition, and the translation space `U` of
that member, whose preimage is `L_σ`. Carried here is the algebraic content of that argument, in
the form and the cone, for a general `Σ`:

* `supportSpace_eq_of_span_supportForms_eq`: the support space depends only on the linear span of
  the forms that define it, so it is unchanged by any operation on `τ` that preserves that span.
* `supportSpace_eq_of_face`: **the face step**, and the heart of the matter. If `F` is a face of
  `τ` and `w` is a form nonnegative on `τ` and zero on `σ` that exposes `F` — more precisely, if
  every form nonnegative on `F` and zero on `σ` becomes nonnegative on `τ` after adding a
  multiple of `w` (the *domination* hypothesis, the shape in which "the translation space of the
  adjacent members contains that of this one" appears as an algebraic statement) — then
  `L_τ = L_F`. A form nonnegative on the face and its multiple are both nonnegative on the cone,
  and the form is their difference: the two spans agree.
* `supportSpace_eq_of_common_face`: **the independence from `τ`**, for two members `τ`, `τ'`
  whose common face `τ ⊓ τ'` is exposed in each with domination: `L_τ = L_{τ ⊓ τ'} = L_{τ'}`.
  This is the source's induction over the decomposition, one face at a time.
* `exists_add_smul_of_fg`, `supportSpace_eq_of_face_of_fg`, `supportSpace_eq_of_common_face_of_fg`:
  domination is discharged for a finitely generated cone, which is what a rational cone of `Σ`
  is. For `τ` generated by a finite `T` whose generators on which `w` vanishes lie in `F`, the
  multiple is the sum of the multiples the finitely many generators need (`0 ≤ w` on `τ` makes
  the sum dominate each term), and nonnegativity on the generators propagates to the cone
  generated by them (`halfspaceCone`, the ported Minkowski–Weyl half-space). So for a
  decomposition of `C₊` into finitely generated cones whose pairwise intersections are faces
  exposed by forms of the decomposition, the independence is unconditional in the incidence data.
* `sigmaSupportSpace_eq_supportSpace`: hence the intersection `sigmaSupportSpace` carried in this
  file is the common value, which is the assertion of Lemma-Definition 4.5.

The face step compares two members that are *adjacent*, meeting in a common face; Lemma-Definition
4.5 compares any two members above `σ`. The step between the two is not a matter of forms but of
incidence, and it is carried in the section "The connectivity of a locally finite decomposition
through common faces" below: the members meeting a convex cone `C` are joined by a chain of members
in which consecutive members meet in a point of `C` (`reflTransGen_inf_nonempty_of_convex`), the
support space is constant along such a chain (`supportSpace_eq_of_reflTransGen`), and hence the
independence holds for every pair of members meeting `C` (`supportSpace_eq_of_locallyFinite`,
`sigmaSupportSpace_eq_supportSpace_of_locallyFinite`).

## What is not carried, and why

* The forms that cut the common face of two adjacent members out of each are not produced. They are
  the hypothesis `hexp` of `supportSpace_eq_of_locallyFinite` and `Dominates` is the datum; the
  domination half is free for a polyhedral member (`dominates_of_fg`), the exposure half is not.
  The source's proof passes instead through the polyhedra `{z | (1, z) ∈ π_I τ}` of its affine
  space `A_I(ℝ)`, a minimal member among those meeting `C`, and the translation space of that
  member, from which it reads `L_σ`; that affine model is not reconstructed here, and the
  connectivity it stands for is. What is reconstructed of the source's proof is the section "The
  two descriptions of `L_σ`": its "clear" case, as the two theorems
  `supportSpace_eq_span_of_ker_eq` and `sigmaSupportSpace_eq_span_of_forall_ker_eq` — for members
  whose span is the kernel of a form nonnegative on them, the support space is `⟨σ⟩` and does not
  depend on the member at all, with no cutting form `hexp` anywhere — and, in the isotropic case,
  the projection step `L_σ ⊆ I^⊥` (`supportSpace_le_ker_associated_of_isotropic`,
  `sigmaSupportSpace_le_ker_associated_of_isotropic`), which with `supportSpace_le_span` gives the
  source's description `L_σ ⊆ I^⊥ ∩ ⋂_{τ > σ} ⟨τ⟩` as an upper bound. The reverse inclusion is
  exactly what the affine model supplies — a minimal member of the induced decomposition of
  `A_I(ℝ)` is an affine subspace, the decomposition is invariant under its translation space `U`,
  and `L_σ` is the space over `U` — and that is the part of the isotropic case still not carried.
  For the cells of `Σ(H)` of Example 4.3 (b) the cutting form of two adjacent cells is the form of
  a sign condition separating them, which is where the hypothesis is met in the example the source
  is about. The module docstring records two checks by hand of the shape: on the single
  `ℚ`-hyperplane through `σ` in signature `(1, 3)`, where the polyhedra are two half-spaces and
  their boundary, the three members above `σ` that meet `C` have one support space, and it is
  `I^⊥ ∩ H`, the value the source's description gives; and on two `ℚ`-hyperplanes in signature
  `(1, 3)`, where the four cells, the two walls and the corner cone all have support space
  `I^⊥ ∩ H₁ ∩ H₂ = I`, again the source's value.
* **The isotropic item of the list after the proof of Lemma-Definition 4.5 is carried** — the
  source's "so the support spaces of `Σ(bb)` are `V`, `{0}` and the hyperplanes orthogonal to a
  `ℚ`-isotropic line" (p. 19). For `σ` the ray through an isotropic `e` of the
  closed sheet, the support space relative to the sheet is `I^⊥`, both inclusions
  (`supportSpace_closedSheet_hull_eq_ker`, in the section "The support space of an isotropic half
  line in the facial decomposition"). The upper bound is `supportSpace_le_ker_associated_of_isotropic`;
  the lower one is the sheet's self-duality,
  `quadratic_nonneg_of_forall_mem_closedSheet_nonneg`, together with
  `exists_smul_of_associated_eq_zero_of_mem_closedSheet_self` (a form of the sheet vanishing on `e`
  is a multiple of `e`). Still not carried: `V` for `C₊` itself and `{0}`, and the same
  identification for a general `Σ`.
* **`C ⊆ C₊` is carried** (`subset_rationalClosure`, for a finite-dimensional `L`), and with it the
  cover hypothesis `hcover`: `exists_mem_of_mem_of_cover_rationalClosure` turns a cover of `C₊`
  into one of `C`, and `supportSpace_eq_of_locallyFinite_of_cover_rationalClosure` and
  `sigmaSupportSpace_eq_supportSpace_of_locallyFinite_of_cover_rationalClosure` are the two
  theorems above with that hypothesis discharged. The step is the simplex: a point of the open cone
  is the centroid of a simplex whose vertices are in `C`, and each vertex is replaced by a rational
  point near it, the barycentric coordinates being continuous. It needs `L` finite dimensional — a
  convex cone with empty interior dense in its closure has `int (closure C) ⊄ C` — and it is run in
  the coordinate space `Fin n → ℝ` along `realified V ≃L[ℝ] (Fin n → ℝ)`, because the two
  Mathlib lemmas it rests on, `IsOpen.affineSpan_eq_top` and
  `Convex.interior_nonempty_iff_affineSpan_eq_top`, are stated for sets in a normed space, while
  `L(ℝ)` here carries the module topology. The transport is `Module.finBasis` together with
  `IsModuleTopology.continuous_of_linearMap`; every linear map out of a finite-dimensional module
  with the module topology is continuous, so the basis equivalence is a `ContinuousLinearEquiv`.
  (`Convex.interior_closure_eq_interior_of_nonempty_interior`, the third of them, is *not*
  restricted to normed spaces: its section assumes only `IsTopologicalAddGroup` and
  `ContinuousSMul`.)
* Also not carried, and this is *not* a hypothesis of Definition 4.2 that could be discharged from
  it: the cutting form `w` of `hexp`. Definition 4.2 (line 481) calls a cone *locally rational in
  `C₊`* when "its intersection with every rational subcone of `C₊` is rational", and rational means
  spanned by a **finite** subset of `L(ℚ)` (Definition 4.1, line 459); so the traces of a member on
  rational subcones are finitely generated, and the members themselves are not. Every face of a
  finitely generated cone is exposed, and the corpus has that (`Mathlib`'s
  `Geometry/Convex/Cone/Face`, TauCeti `Geometry/Convex/Cone/Face/Exposed.lean`, and
  `Analysis/Convex/Polyhedron/Face.lean` for polyhedra), so for a decomposition into finitely
  generated cones the cutting form and, with `exists_add_smul_of_fg`, its domination would be
  available; but the members of a decomposition of the round cone `C₊` of Example 4.3 are not
  finitely generated, `C₊` itself is not, and `exists_add_smul_of_fg` does not apply to them. The
  cutting form therefore comes, in the source, from the same affine model as the translation space
  `U`; it is not a consequence of the decomposition axioms.
-/

/-! ## Remaining isotropic obligation after the locality and quotient steps

The following status supersedes the older provisional wording in this document. The interior
case is now `supportSpace_eq_of_mem_open_of_locallyRational`, with no `hexp`, using
`supportSpace_inf_eq_of_mem_nhds`, the rational neighbourhood from
`exists_rationalCone_mem_nhds_subset_of_ne_zero`, and the exposed common faces of its finite
rational traces. The zero-cone case is `supportSpace_bot_of_isClosed_of_salient`. For the
quotient by `span σ`, `supportSpace_map_mkQ_bot_eq_topologicalClosure_lineal` identifies the
remaining isotropic object with projected closed-cone lineality. The projected adjacency and
chain steps are now proved: `lineal_topologicalClosure_map_le_of_hull_singleton` transfers every
lineality direction across one adjacent pair, and
`lineal_topologicalClosure_map_eq_of_reflTransGen_of_hull_singleton` propagates the equality along
an isotropic common-face chain. `map_inf_eq_inf_map_of_span_singleton` supplies projection of
intersections.

The exact conclusion still owed for an isotropic member of a locally rational decomposition is
the following statement (written here as a handoff specification, not asserted as a proved
declaration). The handoff at `aca6d70a1b` was not well-typed: `positiveCone.upper` is a set and
omits zero, whereas `rationalClosure` takes a pointed cone retaining zero. The corrected carrier
is `rationalClosure (closedSheet Q hpos ht)`, with the source's hyperbolic hypotheses made explicit.

```
theorem supportSpace_eq_of_isotropicHalfLine_of_locallyRational
    [Module.Finite ℚ V]
    {Q : QuadraticForm ℝ (realified V)} {t : realified V}
    (hpos : sigPos Q = 1) (hnd : Q.Nondegenerate) {ht : 0 < Q t}
    {S : Set (PointedCone ℝ (realified V))}
    (hS : IsLocallyRationalDecomposition (rationalClosure (closedSheet Q hpos ht)) S)
    {σ τ τ' : PointedCone ℝ (realified V)}
    (hσ : IsIsotropicHalfLine Q σ)
    (hστ : σ ≤ τ) (hστ' : σ ≤ τ')
    (hτ : τ ∈ S) (hτ' : τ' ∈ S)
    (hτC : ((τ : Set (realified V)) ∩
      (positiveCone.upper Q t : Set (realified V))).Nonempty)
    (hτ'C : ((τ' : Set (realified V)) ∩
      (positiveCone.upper Q t : Set (realified V))).Nonempty) :
    supportSpace τ σ = supportSpace τ' σ
```

The proof still stops at **lineality of the projected closures through the projected half-space**
along the existing common-face chain. The following inputs are now proved and must be retained
for the next attempt:

* finite generation is preserved by linear images (`PointedCone.FG.map`);
* in the finite-dimensional module topology, finitely generated cones are closed
  (`PointedCone.FG.isClosed_of_moduleTopology`);
* a face containing the isotropic generator projects to a face
  (`PointedCone.IsFaceOf.map_mkQ_span_singleton`);
* a projected neighborhood localizes closure membership to its intersection with a cone
  (`mem_topologicalClosure_map_inf_of_mem_nhds`);
* the upper sheet is open by direct finite-dimensional computation
  (`isOpen_positiveCone_upper_of_moduleTopology`), and the set-level chain theorem is
  `reflTransGen_inf_nonempty_of_convex_set`.

The affine/recession step itself is now carried, without asserting that closure commutes with
faces. The isotropic ray is a face of its carrier
(`IsIsotropicHalfLine.isFaceOf_rationalClosure`) and is rational on locally rational traces
(`IsIsotropicHalfLine.isRationalCone_of_le_of_mem`). For `z` in a common projected cell and `x`
in one closure's lineality, the isotropic functional is nonnegative on both `x` and `-x`, so
`β x = 0` and every `z + r x` lifts to the open sheet. A common rational cone neighbourhood of
lifts of `z`, `z + r x`, and `z - r x` is supplied by
`exists_rationalCone_sup_mem_nhds_of_isotropic_three`. Closedness of the finitely generated trace
then lets the common projected face transfer `z + r x` through their midpoint `z`. The limit
lemma `mem_topologicalClosure_of_forall_add_smul_mem` gives both signs of `x` in the other
projected closure.

What remains for the exact statement is the **star-chain input**: between two members above the
same isotropic ray, construct a reflexive-transitive chain in which every node contains that ray
and consecutive intersections meet the upper sheet. This is precisely the relation consumed by
`lineal_topologicalClosure_map_eq_of_reflTransGen_of_hull_singleton`. The older generic chain
`reflTransGen_inf_nonempty_of_convex_set` does not by itself prove this: its intermediate nodes
can lie outside the `σ`-star, and the adjacency theorem intentionally requires the ray at every
node. Once this chain is supplied, `supportSpace_map_mkQ_bot_eq_topologicalClosure_lineal`
finishes the isotropic statement. No `hexp`, no `sorry` and no new axiom is to be introduced.

The earlier recession-cone draft remains unexported at
`.scratch/wt159b-isotropic-draft/RecessionCone.lean`; it was read and does not elaborate. The
`upperZero` wrapper and the pointwise bridge `subset_rationalClosure_of_mem` above supply the
upper-sheet side of the eventual combined theorem: the open upper sheet is in the interior of its
pointed version and lies in the rational closure of the closed sheet.
-/

section SupportSpaceIndependenceGeneral

/-- A form vanishes on the half line `hull ℝ {e}` exactly when it vanishes at `e`: the cone hull
is contained in the linear span and contains `e`. -/
theorem forall_mem_hull_singleton_eq_zero {e : realified V} {φ : (realified V) →ₗ[ℝ] ℝ} :
    (∀ y ∈ PointedCone.hull ℝ ({e} : Set (realified V)), φ y = 0) ↔ φ e = 0 := by
  constructor
  · intro h
    exact h e (PointedCone.subset_hull (Set.mem_singleton e))
  · intro h y hy
    have hle : PointedCone.hull ℝ ({e} : Set (realified V)) ≤
        PointedCone.ofSubmodule (LinearMap.ker φ) := by
      refine le_trans (PointedCone.hull_le_span ℝ _) ?_
      rw [PointedCone.ofSubmodule_le_ofSubmodule, Submodule.span_singleton_le_iff_mem,
        LinearMap.mem_ker]
      exact h
    exact hle hy

/-- A point is in the common zero set of a set of forms exactly when it is in that of their
linear span: the condition is linear in the form. -/
theorem forall_apply_eq_zero_span {S : Set ((realified V) →ₗ[ℝ] ℝ)} {x : realified V} :
    (∀ φ ∈ S, φ x = 0) ↔ ∀ φ ∈ Submodule.span ℝ S, φ x = 0 := by
  constructor
  · intro h φ hφ
    induction hφ using Submodule.span_induction with
    | mem _ hψ => exact h _ hψ
    | zero => simp
    | add _ _ _ _ h1 h2 => rw [LinearMap.add_apply, h1, h2, add_zero]
    | smul c _ _ h1 => rw [LinearMap.smul_apply, smul_eq_mul, h1, mul_zero]
  · exact fun h φ hφ => h φ (Submodule.subset_span hφ)

/-- **The support space depends only on the span of the forms defining it**, so any change of
`τ` that preserves that span — the face step below — preserves the support space (Looijenga,
Lemma-Definition 4.5, p. 19). -/
theorem supportSpace_eq_of_span_supportForms_eq {σ τ τ' : PointedCone ℝ (realified V)}
    (h : Submodule.span ℝ (supportForms τ σ) = Submodule.span ℝ (supportForms τ' σ)) :
    supportSpace τ σ = supportSpace τ' σ := by
  ext x
  rw [mem_supportSpace, mem_supportSpace, forall_apply_eq_zero_span, forall_apply_eq_zero_span, h]

/-- **The face step of Lemma-Definition 4.5** (Looijenga, p. 19; the "adjacent members" step of
its proof): let `F ≤ τ` be cones, `σ ≤ F`, and let `w` be a form nonnegative on `τ` and zero on
`σ` that *dominates* `F` in `τ` — every form nonnegative on `F` and zero on `σ` is made
nonnegative on `τ` by adding a multiple of `w`. Then the support spaces of `τ` and of `F` agree.

A form `φ` nonnegative on `F` and zero on `σ` and its multiple `φ + c • w` are both nonnegative on
`τ`, so the span of the forms of `τ` is the span of those of `F` from above, and the reverse
inclusion is the inclusion `F ≤ τ`. -/
theorem supportSpace_eq_of_face {σ F τ : PointedCone ℝ (realified V)} (hFτ : F ≤ τ)
    {w : (realified V) →ₗ[ℝ] ℝ} (hwτ : ∀ y ∈ τ, 0 ≤ w y) (hwσ : ∀ y ∈ σ, w y = 0)
    (hdom : ∀ φ : (realified V) →ₗ[ℝ] ℝ, (∀ y ∈ F, 0 ≤ φ y) → (∀ y ∈ σ, φ y = 0) →
      ∃ c : ℝ, ∀ y ∈ τ, 0 ≤ (φ + c • w) y) :
    supportSpace τ σ = supportSpace F σ := by
  refine supportSpace_eq_of_span_supportForms_eq ?_
  refine le_antisymm ?_ ?_
  · rw [Submodule.span_le]
    intro φ hφ
    rw [mem_supportForms] at hφ
    exact Submodule.subset_span (mem_supportForms.2 ⟨fun y hy => hφ.1 y (hFτ hy), hφ.2⟩)
  · rw [Submodule.span_le]
    intro φ hφ
    rw [mem_supportForms] at hφ
    obtain ⟨c, hc⟩ := hdom φ hφ.1 hφ.2
    have hmem : φ + c • w ∈ Submodule.span ℝ (supportForms τ σ) :=
      Submodule.subset_span (mem_supportForms.2 ⟨hc, by
        intro y hy
        rw [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, hφ.2 y hy, hwσ y hy,
          mul_zero, add_zero]⟩)
    have hw : w ∈ Submodule.span ℝ (supportForms τ σ) :=
      Submodule.subset_span (mem_supportForms.2 ⟨hwτ, hwσ⟩)
    have hsub : (φ + c • w) - c • w = φ := by abel
    rw [← hsub]
    exact Submodule.sub_mem _ hmem (Submodule.smul_mem _ c hw)

/-- **Lemma-Definition 4.5: the support space does not depend on the member above `σ`**
(Looijenga, p. 19). For two cones `τ`, `τ'` containing `σ` whose common face `τ ⊓ τ'` is exposed
in each by a form nonnegative on the member and zero on `σ`, with domination, the support spaces
of `τ` and of `τ'` are the same: both are that of the common face. -/
theorem supportSpace_eq_of_common_face {σ τ τ' : PointedCone ℝ (realified V)}
    {w : (realified V) →ₗ[ℝ] ℝ} (hwτ : ∀ y ∈ τ, 0 ≤ w y) (hwσ : ∀ y ∈ σ, w y = 0)
    (hdom : ∀ φ : (realified V) →ₗ[ℝ] ℝ, (∀ y ∈ τ ⊓ τ', 0 ≤ φ y) → (∀ y ∈ σ, φ y = 0) →
      ∃ c : ℝ, ∀ y ∈ τ, 0 ≤ (φ + c • w) y)
    {w' : (realified V) →ₗ[ℝ] ℝ} (hwτ' : ∀ y ∈ τ', 0 ≤ w' y) (hwσ' : ∀ y ∈ σ, w' y = 0)
    (hdom' : ∀ φ : (realified V) →ₗ[ℝ] ℝ, (∀ y ∈ τ ⊓ τ', 0 ≤ φ y) → (∀ y ∈ σ, φ y = 0) →
      ∃ c : ℝ, ∀ y ∈ τ', 0 ≤ (φ + c • w') y) :
    supportSpace τ σ = supportSpace τ' σ :=
  (supportSpace_eq_of_face inf_le_left hwτ hwσ hdom).trans
    (supportSpace_eq_of_face inf_le_right hwτ' hwσ' hdom').symm

/-- **Lemma-Definition 4.5 for `σ` a half line, in the form the source states it** (p. 19): the
domination hypotheses at the generator `e` of `σ = hull ℝ {e}`. The isotropic case of the source
is the one in which `Q e = 0`; the argument is indifferent to it, and no isotropy is used. -/
theorem supportSpace_eq_of_common_face_halfLine {σ τ τ' : PointedCone ℝ (realified V)}
    {e : realified V} (hσ : σ = PointedCone.hull ℝ ({e} : Set (realified V)))
    {w : (realified V) →ₗ[ℝ] ℝ} (hwτ : ∀ y ∈ τ, 0 ≤ w y) (hwe : w e = 0)
    (hdom : ∀ φ : (realified V) →ₗ[ℝ] ℝ, (∀ y ∈ τ ⊓ τ', 0 ≤ φ y) → φ e = 0 →
      ∃ c : ℝ, ∀ y ∈ τ, 0 ≤ (φ + c • w) y)
    {w' : (realified V) →ₗ[ℝ] ℝ} (hwτ' : ∀ y ∈ τ', 0 ≤ w' y) (hwe' : w' e = 0)
    (hdom' : ∀ φ : (realified V) →ₗ[ℝ] ℝ, (∀ y ∈ τ ⊓ τ', 0 ≤ φ y) → φ e = 0 →
      ∃ c : ℝ, ∀ y ∈ τ', 0 ≤ (φ + c • w') y) :
    supportSpace τ σ = supportSpace τ' σ := by
  have hwσ : ∀ y ∈ σ, w y = 0 := by
    rw [hσ]; exact forall_mem_hull_singleton_eq_zero.2 hwe
  have hwσ' : ∀ y ∈ σ, w' y = 0 := by
    rw [hσ]; exact forall_mem_hull_singleton_eq_zero.2 hwe'
  exact supportSpace_eq_of_common_face hwτ hwσ
    (fun φ h1 h2 => hdom φ h1 (forall_mem_hull_singleton_eq_zero.1 (hσ ▸ h2))) hwτ' hwσ'
    (fun φ h1 h2 => hdom' φ h1 (forall_mem_hull_singleton_eq_zero.1 (hσ ▸ h2)))

/-- **Domination at the generators of a finitely generated cone**, which is where the domination
hypothesis of `supportSpace_eq_of_face` comes from for a polyhedral member: if `τ` is generated by
a finite `T`, `w` is nonnegative on `τ` and vanishes on `F`, and `φ` is nonnegative on `F`, then
some multiple of `w` makes `φ` nonnegative on `τ`.

The multiple of the generator `m ∈ T` is any natural number past `-φ m / w m`, of which there is
one because `w m > 0` unless `m ∈ F`; summing them works because `0 ≤ w` on `τ`. -/
theorem exists_add_smul_of_fg {T : Finset (realified V)} {F τ : PointedCone ℝ (realified V)}
    {w φ : (realified V) →ₗ[ℝ] ℝ}
    (hwτ : ∀ y ∈ τ, 0 ≤ w y)
    (hτT : τ ≤ PointedCone.hull ℝ ((T : Set (realified V))))
    (hTτ : ∀ m ∈ T, m ∈ τ)
    (hF : ∀ m ∈ T, w m = 0 → m ∈ F)
    (hφF : ∀ y ∈ F, 0 ≤ φ y) :
    ∃ c : ℝ, ∀ y ∈ τ, 0 ≤ (φ + c • w) y := by
  classical
  have hex : ∀ m : realified V, ∃ c : ℝ, m ∈ T → 0 ≤ φ m + c * w m := by
    intro m
    by_cases hm : m ∈ T
    · by_cases h : w m = 0
      · exact ⟨0, fun _ => by rw [h, mul_zero, add_zero]; exact hφF m (hF m hm h)⟩
      · have hpos : 0 < w m := lt_of_le_of_ne (hwτ m (hTτ m hm)) (Ne.symm h)
        obtain ⟨N, hN⟩ := exists_nat_gt (-(φ m) / w m)
        exact ⟨(N : ℝ), fun _ => by
          have h1 : -(φ m) / w m < (N : ℝ) := hN
          rw [div_lt_iff₀ hpos] at h1
          linarith⟩
    · exact ⟨0, fun h => absurd h hm⟩
  choose b hb using hex
  refine ⟨∑ m ∈ T, max (b m) 0, fun y hy => ?_⟩
  have hgen : ∀ m ∈ T, 0 ≤ (φ + (∑ m ∈ T, max (b m) 0) • w) m := by
    intro m hm
    rw [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
    have hle : b m ≤ ∑ m ∈ T, max (b m) 0 :=
      le_trans (le_max_left _ _) (Finset.single_le_sum (fun i _ => le_max_right _ _) hm)
    have hw₀ : 0 ≤ w m := hwτ m (hTτ m hm)
    nlinarith [hb m hm]
  have hle : PointedCone.hull ℝ ((T : Set (realified V))) ≤
      halfspaceCone (φ + (∑ m ∈ T, max (b m) 0) • w) := by
    rw [PointedCone.hull]
    exact Submodule.span_le.2 (fun x hx => mem_halfspaceCone.2 (hgen x (by simpa using hx)))
  exact hle (hτT hy)

/-- **The face step for a finitely generated cone**, with the domination hypothesis discharged:
the polyhedral case of `supportSpace_eq_of_face`, in which nothing is assumed about the members
beyond the incidence data (Looijenga, p. 19, for a rational cone). -/
theorem supportSpace_eq_of_face_of_fg {σ F : PointedCone ℝ (realified V)}
    (T : Finset (realified V))
    {w : (realified V) →ₗ[ℝ] ℝ}
    (hwτ : ∀ y ∈ PointedCone.hull ℝ ((T : Set (realified V))), 0 ≤ w y)
    (hwσ : ∀ y ∈ σ, w y = 0)
    (hF : ∀ m ∈ T, w m = 0 → m ∈ F) (hFτ : F ≤ PointedCone.hull ℝ ((T : Set (realified V)))) :
    supportSpace (PointedCone.hull ℝ ((T : Set (realified V)))) σ = supportSpace F σ := by
  refine supportSpace_eq_of_face hFτ hwτ hwσ ?_
  intro φ hφF hφσ
  exact exists_add_smul_of_fg hwτ le_rfl (fun m hm => PointedCone.subset_hull (by simpa using hm))
    hF hφF

/-- **Lemma-Definition 4.5 for a decomposition into finitely generated cones** (Looijenga, p. 19,
for the rational cones of Definition 4.1): if two members of `Σ` above `σ` are finitely generated
and their common intersection is cut out of each by a form of the member that is nonnegative on
it and zero on `σ`, the support spaces of the two members agree. Nothing is assumed about the
domination of the forms: the generators supply it. -/
theorem supportSpace_eq_of_common_face_of_fg {σ τ τ' : PointedCone ℝ (realified V)}
    (T T' : Finset (realified V))
    (hτ : τ = PointedCone.hull ℝ ((T : Set (realified V))))
    (hτ' : τ' = PointedCone.hull ℝ ((T' : Set (realified V))))
    {w : (realified V) →ₗ[ℝ] ℝ} (hwτ : ∀ y ∈ τ, 0 ≤ w y) (hwσ : ∀ y ∈ σ, w y = 0)
    {w' : (realified V) →ₗ[ℝ] ℝ} (hwτ' : ∀ y ∈ τ', 0 ≤ w' y) (hwσ' : ∀ y ∈ σ, w' y = 0)
    (hF : τ ⊓ τ' = τ ⊓ PointedCone.ofSubmodule (LinearMap.ker w))
    (hF' : τ ⊓ τ' = τ' ⊓ PointedCone.ofSubmodule (LinearMap.ker w')) :
    supportSpace τ σ = supportSpace τ' σ := by
  subst hτ
  subst hτ'
  have h1 : supportSpace (PointedCone.hull ℝ ((T : Set (realified V)))) σ =
      supportSpace (PointedCone.hull ℝ ((T : Set (realified V)))
        ⊓ PointedCone.ofSubmodule (LinearMap.ker w)) σ :=
    supportSpace_eq_of_face_of_fg T hwτ hwσ (fun m hm h => ?_) inf_le_left
  have h2 : supportSpace (PointedCone.hull ℝ ((T' : Set (realified V)))) σ =
      supportSpace (PointedCone.hull ℝ ((T' : Set (realified V)))
        ⊓ PointedCone.ofSubmodule (LinearMap.ker w')) σ :=
    supportSpace_eq_of_face_of_fg T' hwτ' hwσ' (fun m hm h => ?_) inf_le_left
  · rw [h1, h2, ← hF, ← hF']
  · exact ⟨PointedCone.subset_hull (by simpa using hm), by simpa [LinearMap.mem_ker] using h⟩
  · exact ⟨PointedCone.subset_hull (by simpa using hm), by simpa [LinearMap.mem_ker] using h⟩

/-- **Support-space independence on a rational neighbourhood, with no exposure hypothesis.**
Definition 4.2 makes the traces `a ⊓ K`, `b ⊓ K` members of a finite rational cone system.
Their common face is exposed in each trace by `exists_nonneg_linear_inf_ker`. The previous
lemma lifts the exposing forms' zero condition back to all of `σ`; the domination half is free
from finite generation. Locality then replaces the two traces by the original members. -/
theorem supportSpace_eq_of_rational_neighborhood {Cplus : PointedCone ℝ (realified V)}
    {S : Set (PointedCone ℝ (realified V))} (hS : IsLocallyRationalDecomposition Cplus S)
    {σ a b K : PointedCone ℝ (realified V)} (ha : a ∈ S) (hb : b ∈ S)
    (hσa : σ ≤ a) (hσb : σ ≤ b) (hKrat : IsRationalCone K) (hKle : K ≤ Cplus)
    {x : realified V} (hxσ : x ∈ σ) (hK : (K : Set (realified V)) ∈ 𝓝 x) :
    supportSpace a σ = supportSpace b σ := by
  classical
  let R := hS.restriction K hKrat hKle
  let A := a ⊓ K
  let B := b ⊓ K
  have hA : A ∈ faceClosure (restrictionTo S K) :=
    mem_faceClosure.2 ⟨A, mem_restrictionTo.2 ⟨a, ha, rfl⟩, PointedCone.IsFaceOf.refl A⟩
  have hB : B ∈ faceClosure (restrictionTo S K) :=
    mem_faceClosure.2 ⟨B, mem_restrictionTo.2 ⟨b, hb, rfl⟩, PointedCone.IsFaceOf.refl B⟩
  obtain ⟨s, hs⟩ := R.isRational A hA
  obtain ⟨t, ht⟩ := R.isRational B hB
  let T := s.image rationalPoint
  let T' := t.image rationalPoint
  have hAT : A = PointedCone.hull ℝ ((T : Set (realified V))) := by
    simpa [T] using hs
  have hBT : B = PointedCone.hull ℝ ((T' : Set (realified V))) := by
    simpa [T'] using ht
  have hAFG : A.FG := ⟨T, hAT.symm⟩
  have hBFG : B.FG := ⟨T', hBT.symm⟩
  have hFA : (A ⊓ B).IsFaceOf A := R.inf_isFaceOf_left hA hB
  have hFB : (A ⊓ B).IsFaceOf B := R.inf_isFaceOf_right hA hB
  obtain ⟨w, hwA, hFw⟩ :=
    PointedCone.IsFaceOf.exists_nonneg_linear_inf_ker hFA hAFG
  obtain ⟨w', hwB, hFw'⟩ :=
    PointedCone.IsFaceOf.exists_nonneg_linear_inf_ker hFB hBFG
  have hcomm : (a ⊓ K) ⊓ (b ⊓ K) = a ⊓ b ⊓ K := by
    ext z
    change ((z ∈ a ∧ z ∈ K) ∧ z ∈ b ∧ z ∈ K) ↔ (z ∈ a ∧ z ∈ b) ∧ z ∈ K
    aesop
  have hwσ : ∀ y ∈ σ, w y = 0 := by
    apply forall_mem_cone_eq_zero_of_zero_on_inf_of_mem_nhds hxσ hσa hσb hK
    intro z hz
    have hzker : z ∈ A ⊓ PointedCone.ofSubmodule (LinearMap.ker w) := by
      rw [hFw]
      exact hcomm.symm ▸ hz
    exact hzker.2
  have hwσ' : ∀ y ∈ σ, w' y = 0 := by
    apply forall_mem_cone_eq_zero_of_zero_on_inf_of_mem_nhds hxσ hσa hσb hK
    intro z hz
    have hzker : z ∈ B ⊓ PointedCone.ofSubmodule (LinearMap.ker w') := by
      rw [hFw']
      exact hcomm.symm ▸ hz
    exact hzker.2
  have hAB : supportSpace A σ = supportSpace B σ :=
    supportSpace_eq_of_common_face_of_fg T T' hAT hBT hwA hwσ hwB hwσ' hFw.symm hFw'.symm
  have hlocalA : supportSpace A σ = supportSpace a σ := by
    dsimp [A]
    exact supportSpace_inf_eq_of_mem_nhds hσa hxσ hK
  have hlocalB : supportSpace B σ = supportSpace b σ := by
    dsimp [B]
    exact supportSpace_inf_eq_of_mem_nhds hσb hxσ hK
  exact hlocalA.symm.trans (hAB.trans hlocalB)

/-- **Lemma-Definition 4.5 where `σ` meets the open cone, without `hexp`.** A nonzero point
`x ∈ σ ∩ C` supplies the rational neighbourhood of `exists_rationalCone_mem_nhds_subset_of_ne_zero`.
The fact that an open nondegenerate cone cannot contain zero is carried as the explicit condition
`hC0`; in the hyperbolic setting it follows directly from positivity of the quadratic form. -/
theorem supportSpace_eq_of_mem_open_of_locallyRational {C : PointedCone ℝ (realified V)}
    [Module.Finite ℚ V] (hCopen : IsOpen (C : Set (realified V)))
    {S : Set (PointedCone ℝ (realified V))} (hS : IsLocallyRationalDecomposition (rationalClosure C) S)
    (hC0 : (0 : realified V) ∉ (C : Set (realified V)))
    {σ a b : PointedCone ℝ (realified V)} (ha : a ∈ S) (hb : b ∈ S)
    (hσa : σ ≤ a) (hσb : σ ≤ b)
    (hσC : ((σ : Set (realified V)) ∩ (C : Set (realified V))).Nonempty) :
    supportSpace a σ = supportSpace b σ := by
  obtain ⟨x, hxσ, hxC⟩ := hσC
  have hx0 : x ≠ 0 := by
    intro h
    exact hC0 (h ▸ hxC)
  obtain ⟨K, hKrat, hKn, hKleC⟩ :=
    exists_rationalCone_mem_nhds_subset_of_ne_zero hCopen hxC hx0
  have hKle : K ≤ rationalClosure C := hKleC.trans (subset_rationalClosure C hCopen)
  exact supportSpace_eq_of_rational_neighborhood hS ha hb hσa hσb hKrat hKle hxσ hKn

/-- **The `Σ`-support space of Lemma-Definition 4.5 is the common value**: if the support space of
every member of `Σ` that lies above `σ` and meets `C` agrees with one of them, the intersection
over them — the `sigmaSupportSpace` carried in this file — is that value. -/
theorem sigmaSupportSpace_eq_of_forall_eq {C : PointedCone ℝ (realified V)}
    {S : Set (PointedCone ℝ (realified V))} {σ : PointedCone ℝ (realified V)}
    (τ₀ : supportIndex C S σ) {L : Submodule ℝ (realified V)}
    (h : ∀ τ : supportIndex C S σ, supportSpace τ.1 σ = L) :
    sigmaSupportSpace C S σ = L := by
  rw [sigmaSupportSpace]
  exact le_antisymm ((iInf_le _ τ₀).trans (h τ₀).le) (le_iInf fun τ => (h τ).ge)

/-- **Lemma-Definition 4.5, the `Σ`-support space**: the support space of a member of `Σ` above
`σ` meeting `C` is the `Σ`-support space `L_σ`, once the independence from the member is known
(`supportSpace_eq_of_common_face`). -/
theorem sigmaSupportSpace_eq_supportSpace {C : PointedCone ℝ (realified V)}
    {S : Set (PointedCone ℝ (realified V))} {σ : PointedCone ℝ (realified V)}
    (τ₀ : supportIndex C S σ)
    (h : ∀ τ : supportIndex C S σ, supportSpace τ.1 σ = supportSpace τ₀.1 σ) :
    sigmaSupportSpace C S σ = supportSpace τ₀.1 σ :=
  sigmaSupportSpace_eq_of_forall_eq τ₀ h

end SupportSpaceIndependenceGeneral


/-! ## The connectivity of a locally finite decomposition through common faces

Looijenga's proof of Lemma-Definition 4.5 (p. 19, text version
`.tmp-sources/looijenga-math0201218v2.md:521`) does not compare two arbitrary members `τ, τ'`
above `σ`. For `σ` spanning an isotropic line `I` it projects to the affine space `A_I(ℝ)`,
decomposes that into the polyhedra `{z | (1, z) ∈ π_I τ}`, takes a minimal member of that
decomposition and its translation space `U`, and reads `L_σ` off `U`; for every other `σ` it says
the assertion is clear. Both routes consume the same step, and it is the one the face step
`supportSpace_eq_of_face` above leaves open: the step from *adjacent* members — two members
meeting in a common face — to all members. The members above `σ` that meet `C` have to be joined
by a chain in which consecutive members meet in a common face cut out of each by a form.

This section proves that step, in the form and in the cone, with no coordinates.

* `reflTransGen_inter_nonempty_of_isPreconnected` is the topological fact underneath, and the
  reason the decomposition has to be *locally finite*: a preconnected set covered by finitely many
  closed sets is chained through the intersections of those sets. It is the standard clopen
  argument. The union `U` of the sets reachable from a starting one is closed, a finite union of
  closed sets; it is open in the covered set `s`, because `s ∖ U` is the union of the remaining
  closed sets, again by the cover; so `U` is a nonempty clopen subset of `s` and is all of `s`,
  since a preconnected set has no nonempty proper clopen subset
  (`isPreconnected_iff_subset_of_disjoint_closed`). Convexity of the members is *not* used in this
  step. Closedness is, and local finiteness supplies finiteness.
* `reflTransGen_inf_nonempty_of_convex` applies it to the members of a decomposition covering a
  convex cone `C` that meet `C`: any two of them are joined by a chain of members in which
  consecutive members meet in a point of `C`. The segment `[x, y]` between a point of `C` in one
  member and a point of `C` in the other is compact, so the local finiteness of `Σ` leaves
  finitely many members meeting it (`LocallyFinite.finite_nonempty_inter_compact`); each of those
  members cuts an interval out of the segment, and the intervals cover the segment because `C` is
  convex. This is the route the source takes in the case that is "otherwise", through the local
  finiteness of `Σ` near a point of `σ` meeting `C`.
* `Dominates` is the incidence datum at one member and `supportSpace_eq_of_dominates` is the face
  step read through it: `w` is nonnegative on `τ` and zero on `σ`, and every form nonnegative on
  the common face `τ ⊓ τ'` and zero on `σ` becomes nonnegative on `τ` after adding a multiple of
  `w`. That is the source's "the translation space of the adjacent members contains that of this
  one", as a statement about forms. For a polyhedral member it is free
  (`exists_dominates_of_fg`).
* `supportSpace_eq_of_locallyFinite` joins the two: the support space of `σ` is the same for every
  member above `σ` meeting `C`. With `sigmaSupportSpace_eq_supportSpace` that gives the support
  space `L_σ` of Lemma-Definition 4.5 as the value at any one member
  (`sigmaSupportSpace_eq_supportSpace_of_locallyFinite`).

What this section still takes as a hypothesis is the existence of the cutting forms `w` and `w'`
for a pair of members meeting `C` (the `hexp` of the last two theorems) — the source obtains them
from the affine model, and for the cells of `Σ(H)` of Example 4.3 (b) they are the forms of the
two sign conditions that separate the cells. Also a hypothesis is that the members cover `C`
itself, not only `C₊`. -/

section ConnectivityCore

variable {X : Type*} [TopologicalSpace X]

/-- **A preconnected set covered by finitely many closed sets is chained through their
intersections.** For any two members meeting `s`, there is a finite chain of members between them
in which consecutive members meet in a point of `s`.

The set `U` of members reachable from `i₀` and the set `V` of the others are both finite unions of
closed sets, so `s ⊆ U ∪ V` is a cover by two closed sets; they are disjoint on `s`, since a point
of `s` in `J a ∩ J b` with `a` reachable makes `b` reachable; and `U` meets `s`, so a preconnected
`s` lies in `U`. -/
theorem reflTransGen_inter_nonempty_of_isPreconnected {ι : Type*} [Finite ι] {s : Set X}
    (J : ι → Set X) (hs : IsPreconnected s) (hclosed : ∀ i, IsClosed (J i))
    (hcover : ∀ x ∈ s, ∃ i, x ∈ J i) {i₀ : ι} (h₀ : (J i₀ ∩ s).Nonempty) {i : ι}
    (hi : (J i ∩ s).Nonempty) :
    Relation.ReflTransGen (fun a b => (J a ∩ J b ∩ s).Nonempty) i₀ i := by
  classical
  set r : ι → ι → Prop := fun a b => (J a ∩ J b ∩ s).Nonempty with hr
  set cls : Set ι := {j | Relation.ReflTransGen r i₀ j} with hcls
  have hclsfin : cls.Finite := Set.toFinite cls
  have hcomplfin : clsᶜ.Finite := Set.toFinite clsᶜ
  set U : Set X := ⋃ j ∈ cls, J j with hU
  set V : Set X := ⋃ j ∈ clsᶜ, J j with hV
  have hUc : IsClosed U := hclsfin.isClosed_biUnion fun j _ => hclosed j
  have hVc : IsClosed V := hcomplfin.isClosed_biUnion fun j _ => hclosed j
  have hsub : s ⊆ U ∪ V := by
    intro x hx
    obtain ⟨j, hxj⟩ := hcover x hx
    by_cases h : j ∈ cls
    · exact Or.inl (Set.mem_iUnion.2 ⟨j, Set.mem_iUnion.2 ⟨h, hxj⟩⟩)
    · exact Or.inr (Set.mem_iUnion.2 ⟨j, Set.mem_iUnion.2 ⟨h, hxj⟩⟩)
  have hdisj : s ∩ (U ∩ V) = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro x ⟨hxs, hxU, hxV⟩
    obtain ⟨a, ha'⟩ := Set.mem_iUnion.1 hxU
    obtain ⟨hacls, hxa⟩ := Set.mem_iUnion.1 ha'
    obtain ⟨b, hb'⟩ := Set.mem_iUnion.1 hxV
    obtain ⟨hbcls, hxb⟩ := Set.mem_iUnion.1 hb'
    exact hbcls (hacls.tail ⟨x, ⟨hxa, hxb⟩, hxs⟩)
  rcases (isPreconnected_iff_subset_of_disjoint_closed.1 hs) U V hUc hVc hsub hdisj
    with h | h
  · obtain ⟨x, hxJ, hxs⟩ := hi
    obtain ⟨j, hj'⟩ := Set.mem_iUnion.1 (h hxs)
    obtain ⟨hjcls, hxj⟩ := Set.mem_iUnion.1 hj'
    exact hjcls.tail ⟨x, ⟨hxj, hxJ⟩, hxs⟩
  · exfalso
    obtain ⟨x, hxJ, hxs⟩ := h₀
    obtain ⟨j, hj'⟩ := Set.mem_iUnion.1 (h hxs)
    obtain ⟨hjcls, hxj⟩ := Set.mem_iUnion.1 hj'
    exact hjcls (Relation.ReflTransGen.single ⟨x, ⟨hxJ, hxj⟩, hxs⟩)

/-- A relation is carried along a map that sends each of its steps to a step of the target
relation. -/
theorem reflTransGen_map_of_step {α β : Type*} {r : α → α → Prop} {s : β → β → Prop} (f : α → β)
    (h : ∀ a b, r a b → s (f a) (f b)) {a b : α} (hab : Relation.ReflTransGen r a b) :
    Relation.ReflTransGen s (f a) (f b) := by
  induction hab with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact ih.tail (h _ _ hbc)

end ConnectivityCore

section ConeConnectivity

/-- The parametrized segment `t ↦ x + t • (y - x)`. -/
noncomputable def segParam (x y : realified V) : ℝ → realified V := fun t => x + t • (y - x)

/-- The closed segment `[x, y]`, as the image of `Icc 0 1` under `segParam`. -/
noncomputable def seg (x y : realified V) : Set (realified V) :=
  segParam x y '' Set.Icc (0 : ℝ) 1

theorem continuous_segParam (x y : realified V) : Continuous (segParam x y) :=
  continuous_const.add (continuous_id.smul continuous_const)

theorem isCompact_seg (x y : realified V) : IsCompact (seg x y) :=
  isCompact_Icc.image (continuous_segParam x y)

theorem segParam_zero (x y : realified V) : segParam x y 0 = x := by simp [segParam]

theorem segParam_one (x y : realified V) : segParam x y 1 = y := by simp [segParam]

/-- The segment between two points of a convex cone stays in the cone. -/
theorem segParam_mem_of_convex {C : PointedCone ℝ (realified V)}
    (hconv : Convex ℝ (C : Set (realified V))) {x y : realified V} (hx : x ∈ C) (hy : y ∈ C)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) : segParam x y t ∈ C := by
  have h : segParam x y t = (1 - t) • x + t • y := by
    rw [segParam, smul_sub, sub_smul, one_smul]
    abel
  rw [h]
  exact hconv hx hy (by linarith [ht.2]) ht.1 (by ring)

/-- **The incidence datum of a decomposition at one member.** `w` is a form nonnegative on `τ`
and zero on `σ` — the form that cuts the face `F` out of `τ` — and it *dominates* `τ` over `F`:
every form nonnegative on `F` and zero on `σ` becomes nonnegative on `τ` after adding a multiple of
`w`. This is Looijenga's "the translation space of the adjacent members contains that of this one"
(the proof of Lemma-Definition 4.5, p. 19), as a statement about forms. -/
def Dominates (σ τ F : PointedCone ℝ (realified V)) (w : (realified V) →ₗ[ℝ] ℝ) : Prop :=
  (∀ y ∈ τ, 0 ≤ w y) ∧ (∀ y ∈ σ, w y = 0) ∧
    ∀ φ : (realified V) →ₗ[ℝ] ℝ, (∀ y ∈ F, 0 ≤ φ y) → (∀ y ∈ σ, φ y = 0) →
      ∃ c : ℝ, ∀ y ∈ τ, 0 ≤ (φ + c • w) y

/-- **Two members whose common face is cut out of each by such a form have the same support space
over `σ`** — the face step `supportSpace_eq_of_face`, read through `Dominates`. -/
theorem supportSpace_eq_of_dominates {σ a b : PointedCone ℝ (realified V)}
    {w w' : (realified V) →ₗ[ℝ] ℝ} (ha : Dominates σ a (a ⊓ b) w)
    (hb : Dominates σ b (a ⊓ b) w') : supportSpace a σ = supportSpace b σ :=
  supportSpace_eq_of_common_face ha.1 ha.2.1 ha.2.2 hb.1 hb.2.1 hb.2.2

/-- **The domination half of `Dominates` is free for a finitely generated member**: if `τ` is
generated by a finite `T` and the generators on which the cutting form `w` vanishes lie in the
face `F`, then `w` dominates `τ` over `F` (`exists_add_smul_of_fg`). What a polyhedral member of a
decomposition still owes is that its common face with another member *is* the zero set of a form
nonnegative on it. -/
theorem dominates_of_fg {σ τ F : PointedCone ℝ (realified V)} (T : Finset (realified V))
    (hτ : τ = PointedCone.hull ℝ ((T : Set (realified V)))) {w : (realified V) →ₗ[ℝ] ℝ}
    (hwτ : ∀ y ∈ τ, 0 ≤ w y) (hwσ : ∀ y ∈ σ, w y = 0)
    (hF : ∀ m ∈ T, w m = 0 → m ∈ F) : Dominates σ τ F w :=
  ⟨hwτ, hwσ, fun φ hφ hφσ =>
    exists_add_smul_of_fg hwτ (le_of_eq hτ)
      (fun m hm => hτ.symm ▸ PointedCone.subset_hull (by simpa using hm)) hF hφ⟩

/-- **The members of a locally finite decomposition covering a convex cone `C`, that meet `C`, are
connected through their common intersections**: any two of them are joined by a chain of members in
which consecutive members meet in a point of `C` (Looijenga, the proof of Lemma-Definition 4.5,
p. 19). -/
theorem reflTransGen_inf_nonempty_of_convex {C : PointedCone ℝ (realified V)}
    {S : Set (PointedCone ℝ (realified V))}
    (hconv : Convex ℝ (C : Set (realified V)))
    (hclosed : ∀ τ ∈ S, IsClosed ((τ : PointedCone ℝ (realified V)) : Set (realified V)))
    (hcover : ∀ z ∈ C, ∃ τ ∈ S, z ∈ τ)
    (hloc : LocallyFinite fun τ : {τ : PointedCone ℝ (realified V) // τ ∈ S} =>
      ((τ.1 : PointedCone ℝ (realified V)) : Set (realified V)))
    {x y : realified V} (hx : x ∈ C) (hy : y ∈ C)
    {τ τ' : PointedCone ℝ (realified V)} (hτ : τ ∈ S) (hτ' : τ' ∈ S)
    (hxτ : x ∈ τ) (hyτ' : y ∈ τ') :
    Relation.ReflTransGen (fun a b => a ∈ S ∧ b ∈ S ∧
      (((a ⊓ b : PointedCone ℝ (realified V)) : Set (realified V)) ∩
        (C : Set (realified V))).Nonempty) τ τ' := by
  classical
  set ι := {i : {τ : PointedCone ℝ (realified V) // τ ∈ S} //
    (((i.1 : PointedCone ℝ (realified V)) : Set (realified V)) ∩ seg x y).Nonempty} with hιdef
  have hιfin : Finite ι := (hloc.finite_nonempty_inter_compact (isCompact_seg x y)).to_subtype
  let J : ι → Set ℝ := fun j => Set.Icc (0 : ℝ) 1 ∩ segParam x y ⁻¹'
    ((j.1.1 : PointedCone ℝ (realified V)) : Set (realified V))
  have hJclosed : ∀ j : ι, IsClosed (J j) := fun j =>
    isClosed_Icc.inter ((hclosed j.1.1 j.1.2).preimage (continuous_segParam x y))
  have hJcover : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∃ j : ι, t ∈ J j := by
    intro t ht
    have htC : segParam x y t ∈ C := segParam_mem_of_convex hconv hx hy ht
    obtain ⟨τ₀, hτ₀S, hτ₀⟩ := hcover _ htC
    exact ⟨⟨⟨τ₀, hτ₀S⟩, ⟨segParam x y t, hτ₀, ⟨t, ht, rfl⟩⟩⟩, ht, hτ₀⟩
  have hxseg : x ∈ seg x y := ⟨0, ⟨le_refl 0, zero_le_one⟩, segParam_zero x y⟩
  have hyseg : y ∈ seg x y := ⟨1, ⟨zero_le_one, le_refl 1⟩, segParam_one x y⟩
  let i₀ : ι := ⟨⟨τ, hτ⟩, ⟨x, hxτ, hxseg⟩⟩
  let i₁ : ι := ⟨⟨τ', hτ'⟩, ⟨y, hyτ', hyseg⟩⟩
  have h0 : (J i₀ ∩ Set.Icc (0 : ℝ) 1).Nonempty :=
    ⟨0, ⟨⟨⟨le_refl 0, zero_le_one⟩, by
        change segParam x y 0 ∈ ((i₀.1.1 : PointedCone ℝ (realified V)) : Set (realified V))
        rw [segParam_zero]
        exact hxτ⟩, ⟨le_refl 0, zero_le_one⟩⟩⟩
  have h1 : (J i₁ ∩ Set.Icc (0 : ℝ) 1).Nonempty :=
    ⟨1, ⟨⟨⟨zero_le_one, le_refl 1⟩, by
        change segParam x y 1 ∈ ((i₁.1.1 : PointedCone ℝ (realified V)) : Set (realified V))
        rw [segParam_one]
        exact hyτ'⟩, ⟨zero_le_one, le_refl 1⟩⟩⟩
  have hchain := reflTransGen_inter_nonempty_of_isPreconnected J isPreconnected_Icc hJclosed
    hJcover h0 h1
  let rcone : PointedCone ℝ (realified V) → PointedCone ℝ (realified V) → Prop :=
    fun a b => a ∈ S ∧ b ∈ S ∧ (((a ⊓ b : PointedCone ℝ (realified V)) : Set (realified V)) ∩
      (C : Set (realified V))).Nonempty
  have hstep : ∀ a b : ι, (J a ∩ J b ∩ Set.Icc (0 : ℝ) 1).Nonempty → rcone a.1.1 b.1.1 := by
    rintro a b ⟨t, ⟨hta, htb⟩, htI⟩
    exact ⟨a.1.2, b.1.2, ⟨segParam x y t,
      ⟨Submodule.mem_inf.2 ⟨hta.2, htb.2⟩, segParam_mem_of_convex hconv hx hy htI⟩⟩⟩
  exact reflTransGen_map_of_step (fun i : ι => i.1.1) hstep hchain

/-- Set-carrier form of `reflTransGen_inf_nonempty_of_convex`. Only convexity and closedness of
`C` enter the chain argument; a pointed-cone witness is unnecessary. LC-09 (2026-11-19):
`content:reflTransGen_inf_nonempty_of_convex` found no second owner, and
`content:finite closed cover preconnected chain` found a finite closed-cover overlap graph with
the same connectivity content. The implementation below reuses the proof immediately above. -/
theorem reflTransGen_inf_nonempty_of_convex_set {C : Set (realified V)}
    {S : Set (PointedCone ℝ (realified V))}
    (hconv : Convex ℝ C)
    (hclosed : ∀ τ ∈ S, IsClosed ((τ : PointedCone ℝ (realified V)) : Set (realified V)))
    (hcover : ∀ z ∈ C, ∃ τ ∈ S, z ∈ τ)
    (hloc : LocallyFinite fun τ : {τ : PointedCone ℝ (realified V) // τ ∈ S} =>
      ((τ.1 : PointedCone ℝ (realified V)) : Set (realified V)))
    {x y : realified V} (hx : x ∈ C) (hy : y ∈ C)
    {τ τ' : PointedCone ℝ (realified V)} (hτ : τ ∈ S) (hτ' : τ' ∈ S)
    (hxτ : x ∈ τ) (hyτ' : y ∈ τ') :
    Relation.ReflTransGen (fun a b => a ∈ S ∧ b ∈ S ∧
      (((a ⊓ b : PointedCone ℝ (realified V)) : Set (realified V)) ∩ C).Nonempty) τ τ' := by
  classical
  have hseg : ∀ t ∈ Set.Icc (0 : ℝ) 1, segParam x y t ∈ C := by
    intro t ht
    have h : segParam x y t = (1 - t) • x + t • y := by
      rw [segParam, smul_sub, sub_smul, one_smul]
      abel
    rw [h]
    exact hconv hx hy (by linarith [ht.2]) ht.1 (by ring)
  set ι := {i : {τ : PointedCone ℝ (realified V) // τ ∈ S} //
    (((i.1 : PointedCone ℝ (realified V)) : Set (realified V)) ∩ seg x y).Nonempty} with hιdef
  have hιfin : Finite ι := (hloc.finite_nonempty_inter_compact (isCompact_seg x y)).to_subtype
  let J : ι → Set ℝ := fun j => Set.Icc (0 : ℝ) 1 ∩ segParam x y ⁻¹'
    ((j.1.1 : PointedCone ℝ (realified V)) : Set (realified V))
  have hJclosed : ∀ j : ι, IsClosed (J j) := fun j =>
    isClosed_Icc.inter ((hclosed j.1.1 j.1.2).preimage (continuous_segParam x y))
  have hJcover : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∃ j : ι, t ∈ J j := by
    intro t ht
    obtain ⟨τ₀, hτ₀S, hτ₀⟩ := hcover _ (hseg t ht)
    exact ⟨⟨⟨τ₀, hτ₀S⟩, ⟨segParam x y t, hτ₀, ⟨t, ht, rfl⟩⟩⟩, ht, hτ₀⟩
  have hxseg : x ∈ seg x y := ⟨0, ⟨le_refl 0, zero_le_one⟩, segParam_zero x y⟩
  have hyseg : y ∈ seg x y := ⟨1, ⟨zero_le_one, le_refl 1⟩, segParam_one x y⟩
  let i₀ : ι := ⟨⟨τ, hτ⟩, ⟨x, hxτ, hxseg⟩⟩
  let i₁ : ι := ⟨⟨τ', hτ'⟩, ⟨y, hyτ', hyseg⟩⟩
  have h0 : (J i₀ ∩ Set.Icc (0 : ℝ) 1).Nonempty :=
    ⟨0, ⟨⟨⟨le_refl 0, zero_le_one⟩, by
        change segParam x y 0 ∈ ((i₀.1.1 : PointedCone ℝ (realified V)) : Set (realified V))
        rw [segParam_zero]
        exact hxτ⟩, ⟨le_refl 0, zero_le_one⟩⟩⟩
  have h1 : (J i₁ ∩ Set.Icc (0 : ℝ) 1).Nonempty :=
    ⟨1, ⟨⟨⟨zero_le_one, le_refl 1⟩, by
        change segParam x y 1 ∈ ((i₁.1.1 : PointedCone ℝ (realified V)) : Set (realified V))
        rw [segParam_one]
        exact hyτ'⟩, ⟨zero_le_one, le_refl 1⟩⟩⟩
  have hchain := reflTransGen_inter_nonempty_of_isPreconnected J isPreconnected_Icc hJclosed
    hJcover h0 h1
  let rcone : PointedCone ℝ (realified V) → PointedCone ℝ (realified V) → Prop :=
    fun a b => a ∈ S ∧ b ∈ S ∧
      (((a ⊓ b : PointedCone ℝ (realified V)) : Set (realified V)) ∩ C).Nonempty
  have hstep : ∀ a b : ι, (J a ∩ J b ∩ Set.Icc (0 : ℝ) 1).Nonempty → rcone a.1.1 b.1.1 := by
    rintro a b ⟨t, ⟨hta, htb⟩, htI⟩
    exact ⟨a.1.2, b.1.2, ⟨segParam x y t,
      ⟨Submodule.mem_inf.2 ⟨hta.2, htb.2⟩, hseg t htI⟩⟩⟩
  exact reflTransGen_map_of_step (fun i : ι => i.1.1) hstep hchain

end ConeConnectivity

section SupportSpaceIndependenceLocallyFinite

/-- A step of the chains of `reflTransGen_inf_nonempty_of_convex`: two members of `S` whose
intersection meets `C`. -/
def ChainRel {E : Type*} [AddCommGroup E] [Module ℝ E]
    (C : PointedCone ℝ E) (S : Set (PointedCone ℝ E)) (a b : PointedCone ℝ E) : Prop :=
  a ∈ S ∧ b ∈ S ∧ (((a ⊓ b : PointedCone ℝ E) : Set E) ∩ (C : Set E)).Nonempty

/-- **Lineality is constant along a chain of common faces.** At each step the common face takes
part in `PointedCone.IsFaceOf.lineal_congr`; induction carries the equality to the endpoints.
This is the incidence part of Looijenga's affine translation-space induction. -/
theorem lineal_eq_of_reflTransGen {E : Type*} [AddCommGroup E] [Module ℝ E]
    {C : PointedCone ℝ E} {S : Set (PointedCone ℝ E)} {τ τ' : PointedCone ℝ E}
    (h : Relation.ReflTransGen (ChainRel C S) τ τ')
    (hface : ∀ a b : PointedCone ℝ E, ChainRel C S a b →
      (a ⊓ b).IsFaceOf a ∧ (a ⊓ b).IsFaceOf b) :
    PointedCone.lineal τ = PointedCone.lineal τ' := by
  induction h with
  | refl => rfl
  | tail _ hbc ih =>
      obtain ⟨ha, hb⟩ := hface _ _ hbc
      exact ih.trans (ha.lineal_congr.symm.trans hb.lineal_congr)

/-- **Along a chain in which consecutive members meet in a common face cut out of each by a form,
the support space over `σ` does not change.** -/
theorem supportSpace_eq_of_reflTransGen {C : PointedCone ℝ (realified V)}
    {S : Set (PointedCone ℝ (realified V))} {σ : PointedCone ℝ (realified V)}
    {τ τ' : PointedCone ℝ (realified V)} (h : Relation.ReflTransGen (ChainRel C S) τ τ')
    (hface : ∀ a b : PointedCone ℝ (realified V), ChainRel C S a b →
      supportSpace a σ = supportSpace b σ) :
    supportSpace τ σ = supportSpace τ' σ := by
  induction h with
  | refl => rfl
  | tail _ hbc ih => exact ih.trans (hface _ _ hbc)

/-- **Lemma-Definition 4.5: the support space of `σ` does not depend on the member `τ` above it**
(Looijenga, p. 19). The members above `σ` that meet the convex cone `C` are joined by a chain of
members of the decomposition (`reflTransGen_inf_nonempty_of_convex`), and along that chain
consecutive members meet in a common face on which the support space does not change
(`supportSpace_eq_of_dominates`). Nothing is assumed about the members beyond being closed and
locally finite, covering `C`, and the cutting forms at each pair; no coordinates are used. -/
theorem supportSpace_eq_of_locallyFinite {C : PointedCone ℝ (realified V)}
    {S : Set (PointedCone ℝ (realified V))} {σ : PointedCone ℝ (realified V)}
    (hconv : Convex ℝ (C : Set (realified V)))
    (hclosed : ∀ τ ∈ S, IsClosed ((τ : PointedCone ℝ (realified V)) : Set (realified V)))
    (hcover : ∀ z ∈ C, ∃ τ ∈ S, z ∈ τ)
    (hloc : LocallyFinite fun τ : {τ : PointedCone ℝ (realified V) // τ ∈ S} =>
      ((τ.1 : PointedCone ℝ (realified V)) : Set (realified V)))
    (hexp : ∀ a b : PointedCone ℝ (realified V), a ∈ S → b ∈ S →
      (((a ⊓ b : PointedCone ℝ (realified V)) : Set (realified V)) ∩
        (C : Set (realified V))).Nonempty →
      ∃ w w' : (realified V) →ₗ[ℝ] ℝ, Dominates σ a (a ⊓ b) w ∧ Dominates σ b (a ⊓ b) w')
    {τ τ' : PointedCone ℝ (realified V)} (hτ : τ ∈ S) (hτ' : τ' ∈ S)
    (hτC : (((τ : PointedCone ℝ (realified V)) : Set (realified V)) ∩
      (C : Set (realified V))).Nonempty)
    (hτ'C : (((τ' : PointedCone ℝ (realified V)) : Set (realified V)) ∩
      (C : Set (realified V))).Nonempty) :
    supportSpace τ σ = supportSpace τ' σ := by
  obtain ⟨x, hxτ, hxC⟩ := hτC
  obtain ⟨y, hyτ', hyC⟩ := hτ'C
  refine supportSpace_eq_of_reflTransGen
    (reflTransGen_inf_nonempty_of_convex hconv hclosed hcover hloc hxC hyC hτ hτ' hxτ hyτ') ?_
  rintro a b ⟨ha, hb, hab⟩
  obtain ⟨w, w', hw, hw'⟩ := hexp a b ha hb hab
  exact supportSpace_eq_of_dominates hw hw'

/-- **Lemma-Definition 4.5, the `Σ`-support space of a locally finite decomposition**: the
intersection of the support spaces of the members above `σ` — the `sigmaSupportSpace` carried in
this file — is the support space of any one of them, which is the independence from `τ` that the
source asserts. -/
theorem sigmaSupportSpace_eq_supportSpace_of_locallyFinite {C : PointedCone ℝ (realified V)}
    {S : Set (PointedCone ℝ (realified V))} {σ : PointedCone ℝ (realified V)}
    (hconv : Convex ℝ (C : Set (realified V)))
    (hclosed : ∀ τ ∈ S, IsClosed ((τ : PointedCone ℝ (realified V)) : Set (realified V)))
    (hcover : ∀ z ∈ C, ∃ τ ∈ S, z ∈ τ)
    (hloc : LocallyFinite fun τ : {τ : PointedCone ℝ (realified V) // τ ∈ S} =>
      ((τ.1 : PointedCone ℝ (realified V)) : Set (realified V)))
    (hexp : ∀ a b : PointedCone ℝ (realified V), a ∈ S → b ∈ S →
      (((a ⊓ b : PointedCone ℝ (realified V)) : Set (realified V)) ∩
        (C : Set (realified V))).Nonempty →
      ∃ w w' : (realified V) →ₗ[ℝ] ℝ, Dominates σ a (a ⊓ b) w ∧ Dominates σ b (a ⊓ b) w')
    (τ₀ : supportIndex C S σ) :
    sigmaSupportSpace C S σ = supportSpace τ₀.1 σ :=
  sigmaSupportSpace_eq_supportSpace τ₀ fun τ =>
    supportSpace_eq_of_locallyFinite hconv hclosed hcover hloc hexp τ.2.1 τ₀.2.1 τ.2.2.2 τ₀.2.2.2

/-- **Lemma-Definition 4.5, the independence of `L_σ` from `τ`, with the cover taken from the
decomposition itself** (Looijenga, p. 19): the members cover the rational closure `C₊`, and
`C ⊆ C₊` (`subset_rationalClosure`) supplies the cover hypothesis of
`supportSpace_eq_of_locallyFinite`. -/
theorem supportSpace_eq_of_locallyFinite_of_cover_rationalClosure
    {C : PointedCone ℝ (realified V)} {S : Set (PointedCone ℝ (realified V))}
    {σ : PointedCone ℝ (realified V)} [Module.Finite ℚ V]
    (hconv : Convex ℝ (C : Set (realified V)))
    (hclosed : ∀ τ ∈ S, IsClosed ((τ : PointedCone ℝ (realified V)) : Set (realified V)))
    (hCopen : IsOpen (C : Set (realified V)))
    (hCplus : ∀ z ∈ rationalClosure C, ∃ τ ∈ S, z ∈ τ)
    (hloc : LocallyFinite fun τ : {τ : PointedCone ℝ (realified V) // τ ∈ S} =>
      ((τ.1 : PointedCone ℝ (realified V)) : Set (realified V)))
    (hexp : ∀ a b : PointedCone ℝ (realified V), a ∈ S → b ∈ S →
      (((a ⊓ b : PointedCone ℝ (realified V)) : Set (realified V)) ∩
        (C : Set (realified V))).Nonempty →
      ∃ w w' : (realified V) →ₗ[ℝ] ℝ, Dominates σ a (a ⊓ b) w ∧ Dominates σ b (a ⊓ b) w')
    {τ τ' : PointedCone ℝ (realified V)} (hτ : τ ∈ S) (hτ' : τ' ∈ S)
    (hτC : (((τ : PointedCone ℝ (realified V)) : Set (realified V)) ∩
      (C : Set (realified V))).Nonempty)
    (hτ'C : (((τ' : PointedCone ℝ (realified V)) : Set (realified V)) ∩
      (C : Set (realified V))).Nonempty) :
    supportSpace τ σ = supportSpace τ' σ :=
  supportSpace_eq_of_locallyFinite hconv hclosed
    (exists_mem_of_mem_of_cover_rationalClosure hCopen hCplus) hloc hexp hτ hτ' hτC hτ'C

/-- **Lemma-Definition 4.5, `L_σ` from the members covering `C₊`** — the previous theorem as the
support space of `σ` in the decomposition. -/
theorem sigmaSupportSpace_eq_supportSpace_of_locallyFinite_of_cover_rationalClosure
    {C : PointedCone ℝ (realified V)} {S : Set (PointedCone ℝ (realified V))}
    {σ : PointedCone ℝ (realified V)} [Module.Finite ℚ V]
    (hconv : Convex ℝ (C : Set (realified V)))
    (hclosed : ∀ τ ∈ S, IsClosed ((τ : PointedCone ℝ (realified V)) : Set (realified V)))
    (hCopen : IsOpen (C : Set (realified V)))
    (hCplus : ∀ z ∈ rationalClosure C, ∃ τ ∈ S, z ∈ τ)
    (hloc : LocallyFinite fun τ : {τ : PointedCone ℝ (realified V) // τ ∈ S} =>
      ((τ.1 : PointedCone ℝ (realified V)) : Set (realified V)))
    (hexp : ∀ a b : PointedCone ℝ (realified V), a ∈ S → b ∈ S →
      (((a ⊓ b : PointedCone ℝ (realified V)) : Set (realified V)) ∩
        (C : Set (realified V))).Nonempty →
      ∃ w w' : (realified V) →ₗ[ℝ] ℝ, Dominates σ a (a ⊓ b) w ∧ Dominates σ b (a ⊓ b) w')
    (τ₀ : supportIndex C S σ) :
    sigmaSupportSpace C S σ = supportSpace τ₀.1 σ :=
  sigmaSupportSpace_eq_supportSpace τ₀ fun τ =>
    supportSpace_eq_of_locallyFinite_of_cover_rationalClosure hconv hclosed hCopen hCplus hloc
      hexp τ.2.1 τ₀.2.1 τ.2.2.2 τ₀.2.2.2

end SupportSpaceIndependenceLocallyFinite

/-! ## The two descriptions of `L_σ` in the source's proof of Lemma-Definition 4.5

Looijenga's proof (p. 19; text version `.tmp-sources/looijenga-math0201218v2.md:521`) has two
cases, and neither of them is the cutting form `hexp` of the section above:

* `σ` is not an isotropic half line. The source says the assertion is "clear" here; what it is
  clear *from* is the description that follows, `L_σ = ⟨σ⟩_ℂ`. If the span of `σ` is cut out by a
  single form `λ` that is nonnegative on `τ`, then a form nonnegative on `τ` and zero on `σ`
  vanishes on `⟨σ⟩`, hence is a multiple of `λ`, and the common zero set of those multiples is
  `⟨σ⟩`: `supportSpace_eq_span_of_ker_eq`. This is the case of the members and walls of the
  arrangement of Example 4.3 (b), where the form of a sign condition cuts the wall out of the
  cells on either side of it, and of the facial decomposition.
* `σ` spans an isotropic line `I`. The source projects along `I`: the image of `C` under
  `L → L/I` is a half-space, `C₊` maps to the union of that half-space with the origin, and the
  members above `σ` become polyhedra in an affine space `A_I(ℝ)` over `(I ⊗ I^⊥/I)(ℝ)`. The form
  `y ↦ e · y` for `e` spanning `I` is nonnegative on the closed sheet (`closedSheet`, and the
  Cauchy–Schwarz inequality of `nonneg_associated_of_quadratic_eq_zero_of_mem_closedSheet`) and
  vanishes on `σ` because `e` is isotropic, which is the projection step: `L_σ ⊆ I^⊥`,
  `supportSpace_le_ker_associated_of_isotropic`. What the source then reads off the affine model
  — that a minimal member of the induced decomposition of `A_I(ℝ)` is an affine subspace, that the
  whole decomposition is invariant under its translation space `U`, and that `L_σ` is the space
  over `U` — is not reconstructed; see "What is not carried" in the module docstring. -/

section SupportSpaceDescriptions

/-- **The source's "clear" case of Lemma-Definition 4.5**: if the span of `σ` is the kernel of a
form nonnegative on `τ`, every form nonnegative on `τ` and zero on `σ` is a multiple of it, so the
common zero set is `⟨σ⟩` — the `Σ`-support space does not depend on `τ` here at all. -/
theorem supportSpace_eq_span_of_ker_eq {σ τ : PointedCone ℝ (realified V)}
    {lam : (realified V) →ₗ[ℝ] ℝ} (hστ : σ ≤ τ) (hlamτ : ∀ x ∈ τ, 0 ≤ lam x)
    (hker : Submodule.span ℝ (σ : Set (realified V)) = LinearMap.ker lam) :
    supportSpace τ σ = Submodule.span ℝ (σ : Set (realified V)) := by
  refine le_antisymm ?_ (span_le_supportSpace hστ)
  have hσ : ∀ y ∈ σ, lam y = 0 := by
    intro y hy
    have hy' : y ∈ LinearMap.ker lam := hker ▸ Submodule.subset_span hy
    simpa using hy'
  intro x hx
  have hφ : lam ∈ supportForms τ σ := ⟨hlamτ, hσ⟩
  have hxlam : x ∈ LinearMap.ker lam := mem_supportSpace.1 hx lam hφ
  rwa [← hker] at hxlam

/-- **Lemma-Definition 4.5 for the members cut out of the ambient space by a nonnegative form**:
if every member `τ` above `σ` meeting `C` has `⟨σ⟩` as the kernel of a form nonnegative on `τ`,
then the `Σ`-support space of `σ` is `⟨σ⟩`. This is the independence from `τ` that the lemma
asserts, and it needs neither the cutting forms `hexp` at pairs of members nor the cover of `C`. -/
theorem sigmaSupportSpace_eq_span_of_forall_ker_eq {C : PointedCone ℝ (realified V)}
    {S : Set (PointedCone ℝ (realified V))} {σ : PointedCone ℝ (realified V)}
    (τ₀ : supportIndex C S σ)
    (h : ∀ τ : supportIndex C S σ, ∃ lam : (realified V) →ₗ[ℝ] ℝ,
      (∀ x ∈ τ.1, 0 ≤ lam x) ∧
      Submodule.span ℝ (σ : Set (realified V)) = LinearMap.ker lam) :
    sigmaSupportSpace C S σ = Submodule.span ℝ (σ : Set (realified V)) := by
  refine sigmaSupportSpace_eq_of_forall_eq τ₀ fun τ => ?_
  obtain ⟨lam, hlamτ, hker⟩ := h τ
  exact supportSpace_eq_span_of_ker_eq τ.2.2.1 hlamτ hker

/-- **The projection step of the source's proof of Lemma-Definition 4.5 in the isotropic case**:
`σ` spans an isotropic line `I = ℝe` and the members lie in the closed sheet of the form. The form
`y ↦ e · y` is nonnegative on `τ` — `e` is isotropic and in the sheet, and the sheet is
self-dual, which is `nonneg_associated_of_quadratic_eq_zero_of_mem_closedSheet` — and it vanishes
on `σ` because `e` is isotropic, so every point of `L_σ` is orthogonal to `e`: `L_σ ⊆ I^⊥`, the
image of the first projection `L → L/I` of the source's affine model. -/
theorem supportSpace_le_ker_associated_of_isotropic {Q : QuadraticForm ℝ (realified V)}
    [Module.Finite ℚ V] (hpos : sigPos Q = 1) {t : realified V} (ht : 0 < Q t)
    {e : realified V} (he : Q e = 0) (het : 0 ≤ (associated Q) e t)
    {σ τ : PointedCone ℝ (realified V)}
    (hσ : σ = PointedCone.hull ℝ ({e} : Set (realified V)))
    (hτ : τ ≤ closedSheet Q hpos ht) :
    supportSpace τ σ ≤ LinearMap.ker (associated Q e) := by
  have hσe : ∀ y ∈ σ, (associated Q e) y = 0 := by
    intro y hy
    rw [hσ] at hy
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1
      (PointedCone.hull_le_span ℝ _ hy : y ∈ Submodule.span ℝ ({e} : Set (realified V)))
    rw [map_smul, smul_eq_mul, associated_self_apply, he, mul_zero]
  intro x hx
  have hφ : (associated Q e) ∈ supportForms τ σ := by
    refine ⟨fun y hy => ?_, hσe⟩
    exact nonneg_associated_of_quadratic_eq_zero_of_mem_closedSheet hpos ht he het (hτ hy)
  simpa using mem_supportSpace.1 hx (associated Q e) hφ

/-- **`L_σ ⊆ I^⊥` for the `Σ`-support space of an isotropic half line**, the τ-independent form of
`supportSpace_le_ker_associated_of_isotropic`: together with `supportSpace_le_span` this is the
source's description of `L_σ` in the isotropic case, as an upper bound. -/
theorem sigmaSupportSpace_le_ker_associated_of_isotropic {Q : QuadraticForm ℝ (realified V)}
    [Module.Finite ℚ V] (hpos : sigPos Q = 1) {t : realified V} (ht : 0 < Q t)
    {e : realified V} (he : Q e = 0) (het : 0 ≤ (associated Q) e t)
    {C σ : PointedCone ℝ (realified V)} {S : Set (PointedCone ℝ (realified V))}
    (τ₀ : supportIndex C S σ)
    (hσ : σ = PointedCone.hull ℝ ({e} : Set (realified V)))
    (hτ : ∀ τ : supportIndex C S σ, τ.1 ≤ closedSheet Q hpos ht) :
    sigmaSupportSpace C S σ ≤ LinearMap.ker (associated Q e) :=
  (sigmaSupportSpace_le τ₀.2.1 τ₀.2.2.1 τ₀.2.2.2).trans
    (supportSpace_le_ker_associated_of_isotropic hpos ht he het hσ (hτ τ₀))

end SupportSpaceDescriptions



/-! ## The decomposition attached to an arrangement of hyperplanes

Looijenga, Example 4.3 (b), pp. 17-18: a collection `H` of hyperplanes through the origin
that meet `C` cuts `C₊` into the closures of the components of `C₊` minus their union, the
decomposition `Σ(H)`. The cones of `Σ(H)` are the *weak sign cells* of the linear forms
defining the hyperplanes — not a construction of this file: it is the ported sign-cell machine
of `LeanCategories.Analysis.Convex.SignCell` (the LC-09 hit TauCeti
`Analysis/Convex/Polyhedron/SignCell/{Basic,Interior}.lean`, from Mei at `a79c5717`). What is
written here is the glue: the cells of a family of linear forms, the sign pattern of a point,
and the decomposition of `C₊`.

The forms are taken as continuous linear forms: in Looijenga's setting `L` is finite
dimensional, where every linear form is continuous, and the ported `weakSignCellCone` is stated
for continuous rows. -/

section Arrangement

open LeanCategories.Analysis.Convex

variable {ι : Type*} (φ : ι → (realified V) →L[ℝ] ℝ)

/-- The closed cell of a sign pattern: the weak sign cell of the family of linear forms, whose
locus is that of the pattern (Looijenga, Example 4.3 (b), pp. 17-18). -/
noncomputable def arrangementCone (s : ι → SignType) : PointedCone ℝ (realified V) :=
  weakSignCellCone φ s

theorem mem_arrangementCone {s : ι → SignType} {x : realified V} :
    x ∈ arrangementCone φ s ↔ ∀ i, match s i with
      | .zero => φ i x = 0
      | .neg => φ i x ≤ 0
      | .pos => 0 ≤ φ i x := by
  rw [arrangementCone]
  show x ∈ (weakSignCell (fun i => (φ i).toContinuousAffineMap) s : Set (realified V)) ↔ _
  rw [mem_weakSignCell]
  refine forall_congr' fun i => ?_
  cases s i <;> simp

/-- The sign pattern realized by a point. -/
noncomputable def signPattern (x : realified V) : ι → SignType :=
  fun i => SignType.sign (φ i x)

theorem mem_arrangementCone_signPattern (x : realified V) :
    x ∈ arrangementCone φ (signPattern φ x) := by
  rw [mem_arrangementCone]
  intro i
  have hs : signPattern φ x i = SignType.sign (φ i x) := rfl
  rw [hs]
  cases h : SignType.sign (φ i x) with
  | zero => simpa using sign_eq_zero_iff.1 h
  | neg => simpa using le_of_lt (sign_eq_neg_one_iff.1 h)
  | pos => simpa using le_of_lt (sign_eq_one_iff.1 h)

/-- **The decomposition `Σ(H)` of `C₊` attached to a family of forms**: the closed cells
intersected with the rational closure (Looijenga, Example 4.3 (b), pp. 17-18). -/
noncomputable def arrangementDecomposition (Cplus : PointedCone ℝ (realified V)) :
    Set (PointedCone ℝ (realified V)) :=
  {σ | ∃ s : ι → SignType, σ = arrangementCone φ s ⊓ Cplus}

theorem union_arrangementDecomposition (Cplus : PointedCone ℝ (realified V)) :
    (⋃ σ ∈ arrangementDecomposition φ Cplus, (σ : Set (realified V)))
      = (Cplus : Set (realified V)) := by
  refine Set.eq_of_subset_of_subset ?_ ?_
  · refine Set.iUnion_subset fun σ => Set.iUnion_subset fun hσ => ?_
    obtain ⟨s, rfl⟩ := hσ
    exact inf_le_right
  · intro x hx
    refine Set.mem_iUnion.2 ⟨arrangementCone φ (signPattern φ x) ⊓ Cplus,
      Set.mem_iUnion.2 ⟨⟨signPattern φ x, rfl⟩, ?_⟩⟩
    exact ⟨mem_arrangementCone_signPattern φ x, hx⟩

/-- Membership in a cell of `Σ(H)` is a specialization of the cell's sign pattern, so the cells
are exactly the weak sign cells of the ported machine. -/
theorem mem_arrangementCone_iff_specializes {s : ι → SignType} {x : realified V} :
    x ∈ arrangementCone φ s ↔
      ∀ i, SignType.sign (φ i x) = 0 ∨ SignType.sign (φ i x) = s i := by
  rw [arrangementCone]
  show x ∈ (weakSignCell (fun i => (φ i).toContinuousAffineMap) s : Set (realified V)) ↔ _
  rw [mem_weakSignCell_iff_specializes]
  exact Iff.rfl

/-- Two cells of the arrangement meet in the cell of their common sign pattern: the traces are
again weak sign cells (`weakSignCell_inter` of the port). -/
theorem arrangementCone_inf (s s' : ι → SignType) :
    arrangementCone φ s ⊓ arrangementCone φ s' = arrangementCone φ (commonSignPattern s s') := by
  refine SetLike.ext fun x => ?_
  rw [arrangementCone, arrangementCone, arrangementCone]
  change x ∈ (weakSignCell (fun i => (φ i).toContinuousAffineMap) s : Set (realified V)) ∧
      x ∈ (weakSignCell (fun i => (φ i).toContinuousAffineMap) s' : Set (realified V)) ↔
    x ∈ (weakSignCell (fun i => (φ i).toContinuousAffineMap) (commonSignPattern s s') :
      Set (realified V))
  rw [← Set.mem_inter_iff, weakSignCell_inter]

end Arrangement

/-! ## Example 4.3 (b): the cells of `Σ(H)` are rational, and `Σ(H)` is a locally rational
decomposition

Looijenga, Example 4.3 (b), pp. 17-18: a `Γ`-finite collection `H` of `ℚ`-hyperplanes of `L`
meeting `C` is locally finite on `C` and decomposes `C₊` into the locally rational decomposition
`Σ(H)`. The cells are the weak sign cells of the linear forms (the ported sign-cell machine);
what this section adds is that a cell cut out of a rational cone by finitely many *rational*
sign conditions is a rational cone (`isRationalCone_arrangementCone_inf`, by Fourier–Motzkin
elimination one form at a time, `isRationalCone_inf_halfspace`), that the cells are faces of one
another along the common sign pattern (`isFaceOf_arrangementCone_commonSignPattern`), and hence
that `Σ(H)` is a locally rational decomposition (`arrangementDecomposition_isLocallyRational`).

`Γ`-finiteness enters only through the hypothesis `CutsFinitelyOnRational`: of the hyperplanes
of `H`, only finitely many cut any rational subcone of `C₊` (Definition 4.2's quantifier; the
definition's docstring records why the quantifier cannot be over all rational cones). That is not
the source's local finiteness of `H` on `C` (whose ground is the properness of the action of `Γ`,
Setting 4.4, p. 18), and the module docstring's section on Example 4.3 (b) records what deriving
it from `Γ`'s arithmeticity needs — finitely many normal values, and the counting lemma for one
value — and that neither is carried here: the finiteness of the traces on a rational cone is proved
below from `CutsFinitelyOnRational`, not from `Γ`. -/

section ArrangementRational

open LeanCategories.Analysis.Convex

variable {ι : Type*} {φ : ι → (realified V) →L[ℝ] ℝ}

/-- The cone of a single sign condition on a linear form. -/
noncomputable def signCone (ψ : (realified V) →ₗ[ℝ] ℝ) (s : SignType) :
    PointedCone ℝ (realified V) :=
  match s with
  | .zero => halfspaceCone ψ ⊓ halfspaceCone (-ψ)
  | .neg => halfspaceCone (-ψ)
  | .pos => halfspaceCone ψ

theorem mem_signCone {ψ : (realified V) →ₗ[ℝ] ℝ} {s : SignType} {x : realified V} :
    x ∈ signCone ψ s ↔ match s with
      | .zero => ψ x = 0
      | .neg => ψ x ≤ 0
      | .pos => 0 ≤ ψ x := by
  cases s with
  | zero =>
    simp only [signCone, Submodule.mem_inf, mem_halfspaceCone, LinearMap.neg_apply]
    constructor
    · rintro ⟨h1, h2⟩
      linarith
    · intro h
      exact ⟨by linarith, by linarith⟩
  | neg => simp [signCone, LinearMap.neg_apply]
  | pos => simp [signCone]

/-- **The cone of a rational cone inside one rational sign condition is rational.** -/
theorem isRationalCone_inf_signCone {P : PointedCone ℝ (realified V)} (hP : IsRationalCone P)
    {ψ : (realified V) →ₗ[ℝ] ℝ} (hψ : IsRationalForm ψ) (s : SignType) :
    IsRationalCone (P ⊓ signCone ψ s) := by
  cases s with
  | zero =>
    have h2 : IsRationalCone ((P ⊓ halfspaceCone ψ) ⊓ halfspaceCone (-ψ)) :=
      isRationalCone_inf_halfspace (isRationalCone_inf_halfspace hP hψ) hψ.neg
    rwa [signCone, ← inf_assoc]
  | neg => exact isRationalCone_inf_halfspace hP hψ.neg
  | pos => exact isRationalCone_inf_halfspace hP hψ

theorem mem_finsetInf {t : Finset ι} {f : ι → PointedCone ℝ (realified V)} {x : realified V} :
    x ∈ t.inf f ↔ ∀ i ∈ t, x ∈ f i := by
  classical
  induction t using Finset.induction with
  | empty => simp
  | insert a t ha ih =>
    rw [Finset.inf_insert, Submodule.mem_inf, ih]
    constructor
    · rintro ⟨h1, h2⟩ i hi
      rcases Finset.mem_insert.1 hi with rfl | hi'
      · exact h1
      · exact h2 i hi'
    · intro h
      exact ⟨h a (Finset.mem_insert_self a t), fun i hi => h i (Finset.mem_insert_of_mem hi)⟩

/-- The sign conditions of a finite set of forms, as a cone. -/
noncomputable def signConeInf (t : Finset ι) (s : ι → SignType) :
    PointedCone ℝ (realified V) :=
  t.inf fun i => signCone (φ i).toLinearMap (s i)

/-- **A rational cone cut out by finitely many rational sign conditions is rational.** -/
theorem isRationalCone_inf_signConeInf (hφ : ∀ i, IsRationalForm (φ i).toLinearMap)
    (s : ι → SignType) (t : Finset ι) (P : PointedCone ℝ (realified V)) (hP : IsRationalCone P) :
    IsRationalCone (P ⊓ signConeInf (φ := φ) t s) := by
  classical
  induction t using Finset.induction generalizing P with
  | empty =>
    have h : P ⊓ signConeInf (φ := φ) (∅ : Finset ι) s = P := by
      rw [show signConeInf (φ := φ) (∅ : Finset ι) s = ⊤ from Finset.inf_empty, inf_top_eq]
    rw [h]
    exact hP
  | insert a t ha ih =>
    rw [signConeInf, Finset.inf_insert, ← inf_assoc]
    exact ih _ (isRationalCone_inf_signCone hP (hφ a) (s a))

theorem mem_arrangementCone_iff_signCone {s : ι → SignType} {x : realified V} :
    x ∈ arrangementCone φ s ↔ ∀ i, x ∈ signCone (φ i).toLinearMap (s i) := by
  rw [mem_arrangementCone]
  refine forall_congr' fun i => ?_
  rw [mem_signCone]
  cases s i <;> simp

theorem commonSignPattern_comm (s s' : ι → SignType) :
    commonSignPattern s s' = commonSignPattern s' s := by
  funext i
  rw [commonSignPattern_apply, commonSignPattern_apply]
  by_cases hh : s i = s' i
  · rw [ite_eq_left hh, ite_eq_left hh.symm, hh]
  · rw [ite_eq_right hh, ite_eq_right (Ne.symm hh)]

/-- **A cell of the arrangement is a face of a cell whose pattern refines it.** -/
theorem isFaceOf_arrangementCone_commonSignPattern (s s' : ι → SignType) :
    (arrangementCone φ (commonSignPattern s s')).IsFaceOf (arrangementCone φ s) where
  le := by
    intro x hx
    rw [mem_arrangementCone_iff_signCone] at hx ⊢
    intro i
    have hxi := hx i
    by_cases h : s i = s' i
    · rw [commonSignPattern_apply, ite_eq_left h] at hxi
      exact hxi
    · rw [commonSignPattern_apply, ite_eq_right h] at hxi
      have hzero : ((φ i).toLinearMap) x = 0 := by
        simpa using mem_signCone.1 hxi
      cases hs : s i
      all_goals simp [mem_signCone, hzero]
  mem_of_smul_add_mem := by
    intro x y a hx hy ha hxy
    rw [mem_arrangementCone_iff_signCone] at hx hy hxy ⊢
    intro i
    rw [commonSignPattern_apply]
    split_ifs with h
    · exact hx i
    · rw [mem_signCone]
      have hsum : ((φ i).toLinearMap) (a • x + y) = 0 := by
        have h' := hxy i
        rw [commonSignPattern_apply, ite_eq_right h] at h'
        simpa using mem_signCone.1 h'
      rw [map_add, map_smul, smul_eq_mul] at hsum
      cases hs : s i with
      | zero => simpa [hs] using mem_signCone.1 (hx i)
      | pos =>
        have h1 := mem_signCone.1 (by simpa [hs] using hx i)
        have h2 := mem_signCone.1 (by simpa [hs] using hy i)
        nlinarith
      | neg =>
        have h1 := mem_signCone.1 (by simpa [hs] using hx i)
        have h2 := mem_signCone.1 (by simpa [hs] using hy i)
        nlinarith

/-- A face of a face is a face of the larger cone. -/
theorem isFaceOf_of_le_of_isFaceOf {A B C : PointedCone ℝ (realified V)}
    (hAB : A ≤ B) (hA : A.IsFaceOf C) (hB : B.IsFaceOf C) : A.IsFaceOf B where
  le := hAB
  mem_of_smul_add_mem := by
    intro x y a hx hy ha hxy
    exact hA.mem_of_smul_add_mem (hB.le hx) (hB.le hy) ha hxy

/-- Cutting a face out of a cone and then intersecting with a subcone. -/
theorem isFaceOf_inf_right {F C P : PointedCone ℝ (realified V)} (hF : F.IsFaceOf C) :
    (F ⊓ P).IsFaceOf (C ⊓ P) where
  le := inf_le_inf hF.le le_rfl
  mem_of_smul_add_mem := by
    intro x y a hx hy ha hxy
    exact ⟨hF.mem_of_smul_add_mem hx.1 hy.1 ha hxy.1, hx.2⟩

/-- A real linear form *cuts* a cone when it takes both signs on it: the hyperplane `ker ψ` passes
through the cone and leaves points of it on both sides. This is what Looijenga's Example 4.3 (b),
p. 18, means by a `ℚ`-hyperplane that *meets* `C` — `.tmp-sources/looijenga-math0201218v2.md:487`
("a collection of Q-hyperplanes of L which meet C"). -/
def CutsOn (ψ : (realified V) →ₗ[ℝ] ℝ) (P : PointedCone ℝ (realified V)) : Prop :=
  (∃ x ∈ P, 0 < ψ x) ∧ ∃ y ∈ P, ψ y < 0

/-- **The hypothesis of Example 4.3 (b), as the finiteness argument of this section consumes it**:
of the hyperplanes `H`, only finitely many cut any given **rational subcone of `C₊`**.

The restriction to subcones of `C₊` is the source's: Looijenga, Definition 4.2, p. 17
(`.tmp-sources/looijenga-math0201218v2.md:483`), asks of a locally rational decomposition of `C₊`
that "the restriction to every rational subcone of `C₊` is a rational cone system", and nowhere of
cones outside `C₊`. The wider quantifier is not a hypothesis that Example 4.3 (b) can supply, and it
is *false* in that setting, arithmetic `Γ` included: a `ℚ`-hyperplane meets `C` exactly when its
normal is spacelike (`neg_quadratic_of_associated_eq_zero`), and a rational cone outside `C₊` is cut
by every normal of one negative value. Take `L = ℚ³` with the form `2 x₁ x₂ - x₃²` of signature
`(1, 2)` and `Λ = ℤ³`: `T(x) = (x₁ + 2 x₂ + 2 x₃, x₂, x₃ + 2 x₂)` is an integral isometry of
infinite order — `Tᵀ G T = G` for the Gram matrix `G` of the form, and `T - 1` is nilpotent — so
`Γ = O(Λ)`, an arithmetic subgroup of `O(L(ℚ))`, has the infinite orbit of `ℓ = (1, -1, 0)`. Each of
its members has `ℓ · ℓ = -2 < 0`, so each hyperplane meets `C`; and each member cuts the rational
cone `{(0, y, z)} = cone {e₂, e₃}`, on which the form of `ℓ` is `ℓ₁ y - ℓ₃ z`, which takes both
signs as soon as `(ℓ₁, ℓ₃) ≠ (0, 0)` — and `ℓ₁ = 0` would force `ℓ₃² = 2`. That cone is outside
`C₊`, where `Σ(H)` decomposes nothing, and the count of cutting normals is infinite on it. So the
finiteness of the normals' values, which is all step (i) of the arithmetic argument gives, does not
make the unrestricted statement true. (A check by hand — three lines with the Gram matrix; the
family of `(x, y) ↦ x - (n+1)y` in the module docstring is the same check without the lattice.)

This replaces the earlier reading, which asked that all but finitely many of the forms *vanish* on
every rational cone — a property no infinite `H` has in the setting of Example 4.3, since an open
piece of `C` is contained in a rational cone and no form that meets `C` vanishes on an open set. A
form that meets `C` is not one-signed on the cones it does not cut: it is nonnegative or nonpositive
on them, and then its sign condition is a face condition (`isFaceOf_inf_reducePattern`). That is
what makes the traces finite below. -/
def CutsFinitelyOnRational (Cplus : PointedCone ℝ (realified V))
    (φ : ι → (realified V) →L[ℝ] ℝ) : Prop :=
  ∀ P : PointedCone ℝ (realified V), IsRationalCone P → P ≤ Cplus →
    {i : ι | CutsOn (φ i).toLinearMap P}.Finite

/-- A form that does not cut a cone is one-signed on it. -/
theorem le_or_le_of_not_cutsOn {ψ : (realified V) →ₗ[ℝ] ℝ} {P : PointedCone ℝ (realified V)}
    (h : ¬ CutsOn ψ P) : (∀ x ∈ P, ψ x ≤ 0) ∨ ∀ x ∈ P, 0 ≤ ψ x := by
  rw [CutsOn, not_and_or, not_exists, not_exists] at h
  rcases h with h | h
  · refine Or.inl fun x hx => ?_
    by_contra hlt
    exact h x ⟨hx, not_le.1 hlt⟩
  · refine Or.inr fun x hx => ?_
    by_contra hlt
    exact h x ⟨hx, not_le.1 hlt⟩

/-- The sign of a form on `P` that imposes nothing on it: `pos` for a form that is nonnegative on
`P`, `neg` for one that is nonpositive on it. -/
noncomputable def weakPattern (φ : ι → (realified V) →L[ℝ] ℝ) (P : PointedCone ℝ (realified V)) :
    ι → SignType :=
  haveI := Classical.propDecidable
  fun i => if ∀ x ∈ P, (0 : ℝ) ≤ φ i x then SignType.pos else SignType.neg

theorem weakPattern_spec {P : PointedCone ℝ (realified V)} {i : ι}
    (h : ¬ CutsOn (φ i).toLinearMap P) :
    (weakPattern φ P i = SignType.pos ∧ ∀ x ∈ P, (0 : ℝ) ≤ φ i x) ∨
      (weakPattern φ P i = SignType.neg ∧ ∀ x ∈ P, φ i x ≤ 0) := by
  classical
  by_cases hpos : ∀ x ∈ P, (0 : ℝ) ≤ φ i x
  · exact Or.inl ⟨by rw [weakPattern, ite_eq_left hpos], hpos⟩
  · rcases le_or_le_of_not_cutsOn h with hneg | hpos'
    · exact Or.inr ⟨by rw [weakPattern, ite_eq_right hpos], hneg⟩
    · exact absurd hpos' hpos

/-- The weak sign of a form that does not cut `P` holds at every point of `P`. -/
theorem mem_signCone_weakPattern {P : PointedCone ℝ (realified V)} {i : ι}
    (h : ¬ CutsOn (φ i).toLinearMap P) {x : realified V} (hx : x ∈ P) :
    x ∈ signCone (φ i).toLinearMap (weakPattern φ P i) := by
  rcases weakPattern_spec (φ := φ) h with ⟨hw, hpos⟩ | ⟨hw, hneg⟩
  · rw [hw]; exact mem_signCone.2 (hpos x hx)
  · rw [hw]; exact mem_signCone.2 (hneg x hx)

/-- The *reduced* pattern of `s` on `P` relative to a finite set `t` of forms: `s` on `t`, the weak
sign elsewhere. A cell of the arrangement is a face of the cell of its reduced pattern
(`isFaceOf_inf_reducePattern`), and the reduced patterns are finitely many
(`range_reducePattern_finite`). -/
noncomputable def reducePattern (φ : ι → (realified V) →L[ℝ] ℝ)
    (P : PointedCone ℝ (realified V)) (t : Finset ι) (s : ι → SignType) : ι → SignType :=
  haveI := Classical.propDecidable
  fun i => if i ∈ t then s i else weakPattern φ P i

/-- **A sign condition that holds on all of `P` can be dropped from the cell**: on `P`, the cell of
`s` is the cell of the forms of `t` alone. -/
theorem arrangementCone_inf_eq_signConeInf_of_mem {P : PointedCone ℝ (realified V)}
    {s : ι → SignType} {t : Finset ι}
    (h : ∀ i ∉ t, ∀ x ∈ P, x ∈ signCone (φ i).toLinearMap (s i)) :
    arrangementCone φ s ⊓ P = signConeInf (φ := φ) t s ⊓ P := by
  refine le_antisymm ?_ ?_
  · intro x hx
    rw [Submodule.mem_inf] at hx ⊢
    refine ⟨mem_finsetInf.2 fun i _ => ?_, hx.2⟩
    rw [mem_arrangementCone_iff_signCone] at hx
    exact hx.1 i
  · intro x hx
    rw [Submodule.mem_inf] at hx ⊢
    refine ⟨?_, hx.2⟩
    rw [mem_arrangementCone_iff_signCone]
    intro i
    by_cases hi : i ∈ t
    · exact mem_finsetInf.1 hx.1 i hi
    · exact h i hi x hx.2

/-- The special case in which the forms outside `t` vanish on `P`. -/
theorem arrangementCone_inf_eq_signConeInf {P : PointedCone ℝ (realified V)}
    {s : ι → SignType} {t : Finset ι} (hzero : ∀ i ∉ t, ∀ x ∈ P, φ i x = 0) :
    arrangementCone φ s ⊓ P = signConeInf (φ := φ) t s ⊓ P :=
  arrangementCone_inf_eq_signConeInf_of_mem fun i hi x hx => by
    have h0 : φ i x = 0 := hzero i hi x hx
    cases s i <;> simp [mem_signCone, h0]

/-- In a cone on which a form is nonnegative, its sign cone is a face: a positive combination of
points of the cone that lands in `signCone ψ s` has both terms in it. -/
theorem mem_signCone_of_smul_add_mem {ψ : (realified V) →ₗ[ℝ] ℝ} {s : SignType}
    {x y : realified V} {a : ℝ} (ha : 0 < a) (hx : 0 ≤ ψ x) (hy : 0 ≤ ψ y)
    (h : a • x + y ∈ signCone ψ s) : x ∈ signCone ψ s := by
  have hsum : ψ (a • x + y) = a * ψ x + ψ y := by
    rw [map_add, map_smul, smul_eq_mul]
  cases s with
  | zero =>
    simp only [mem_signCone] at h ⊢
    rw [hsum] at h
    nlinarith
  | neg =>
    simp only [mem_signCone] at h ⊢
    rw [hsum] at h
    nlinarith
  | pos => simp only [mem_signCone] at h ⊢; exact hx

/-- The same for a form that is nonpositive on the cone. -/
theorem mem_signCone_of_smul_add_mem_of_nonpos {ψ : (realified V) →ₗ[ℝ] ℝ} {s : SignType}
    {x y : realified V} {a : ℝ} (ha : 0 < a) (hx : ψ x ≤ 0) (hy : ψ y ≤ 0)
    (h : a • x + y ∈ signCone ψ s) : x ∈ signCone ψ s := by
  have hsum : ψ (a • x + y) = a * ψ x + ψ y := by
    rw [map_add, map_smul, smul_eq_mul]
  cases s with
  | zero =>
    simp only [mem_signCone] at h ⊢
    rw [hsum] at h
    nlinarith
  | neg => simp only [mem_signCone] at h ⊢; exact hx
  | pos =>
    simp only [mem_signCone] at h ⊢
    rw [hsum] at h
    nlinarith

/-- **A cell of `Σ(H)` is a face of the cell of its reduced pattern.** This is the step the earlier
reading could not make: a form that does not cut `P` is one-signed on it, so its sign condition is
the identity or the vanishing of that form, and the vanishing set of a nonnegative form is a face
of `P` (`mem_signCone_of_smul_add_mem`). -/
theorem isFaceOf_inf_reducePattern {P : PointedCone ℝ (realified V)} {t : Finset ι}
    {s : ι → SignType} (h : ∀ i ∉ t, ¬ CutsOn (φ i).toLinearMap P) :
    (arrangementCone φ s ⊓ P).IsFaceOf (arrangementCone φ (reducePattern φ P t s) ⊓ P) where
  le := by
    intro x hx
    obtain ⟨hxc, hxP⟩ := Submodule.mem_inf.1 hx
    refine Submodule.mem_inf.2 ⟨?_, hxP⟩
    rw [mem_arrangementCone_iff_signCone] at hxc ⊢
    intro i
    by_cases hi : i ∈ t
    · have hwit : reducePattern φ P t s i = s i := by simp [reducePattern, hi]
      rw [hwit]
      exact hxc i
    · have hw : reducePattern φ P t s i = weakPattern φ P i := by simp [reducePattern, hi]
      rw [hw]
      exact mem_signCone_weakPattern (φ := φ) (h i hi) hxP
  mem_of_smul_add_mem := by
    intro x y a hx hy ha hxy
    obtain ⟨hxc, hxP⟩ := Submodule.mem_inf.1 hx
    obtain ⟨hyc, hyP⟩ := Submodule.mem_inf.1 hy
    obtain ⟨hxyc, _⟩ := Submodule.mem_inf.1 hxy
    refine Submodule.mem_inf.2 ⟨?_, hxP⟩
    rw [mem_arrangementCone_iff_signCone] at hxc hyc hxyc ⊢
    intro i
    have hxi := hxc i
    have hyi := hyc i
    have hxyi := hxyc i
    by_cases hi : i ∈ t
    · have hwit : reducePattern φ P t s i = s i := by simp [reducePattern, hi]
      rw [hwit] at hxi
      exact hxi
    · have hw : reducePattern φ P t s i = weakPattern φ P i := by simp [reducePattern, hi]
      rw [hw] at hxi hyi
      rcases weakPattern_spec (φ := φ) (h i hi) with ⟨hpe, hpos⟩ | ⟨hpe, hneg⟩
      · rw [hpe] at hxi hyi
        exact mem_signCone_of_smul_add_mem (ψ := (φ i).toLinearMap) ha (hpos x hxP)
          (hpos y hyP) hxyi
      · rw [hpe] at hxi hyi
        exact mem_signCone_of_smul_add_mem_of_nonpos (ψ := (φ i).toLinearMap) ha
          (hneg x hxP) (hneg y hyP) hxyi

/-- **Finitely many reduced patterns**: the reduced pattern of `s` depends only on `s` on `t`. -/
theorem range_reducePattern_finite (P : PointedCone ℝ (realified V)) (t : Finset ι) :
    (Set.range (reducePattern φ P t)).Finite := by
  classical
  refine Set.Finite.subset (Set.finite_range (fun f : (↥t) → SignType =>
    fun i => if hi : i ∈ t then f ⟨i, hi⟩ else weakPattern φ P i)) ?_
  rintro w ⟨s, rfl⟩
  exact ⟨fun j => s j.1, by
    funext i
    by_cases hi : i ∈ t <;> simp [reducePattern, hi]⟩

/-- **The trace of a cell of `Σ(H)` on a rational subcone is a rational cone** (Looijenga,
Example 4.3 (b), p. 18): the trace is a face of the cell of the finitely many forms that cut the
cone, and that cell is a rational cone cut out by finitely many rational sign conditions. -/
theorem isRationalCone_arrangementCone_inf {Cplus : PointedCone ℝ (realified V)}
    (hφ : ∀ i, IsRationalForm (φ i).toLinearMap) (hcut : CutsFinitelyOnRational Cplus φ)
    (s : ι → SignType)
    (P : PointedCone ℝ (realified V)) (hP : IsRationalCone P) (hPle : P ≤ Cplus) :
    IsRationalCone (arrangementCone φ s ⊓ P) := by
  classical
  have hPf := hcut P hP hPle
  have hnt : ∀ i ∉ hPf.toFinset, ¬ CutsOn (φ i).toLinearMap P := by
    intro i hi hc
    exact hi (by rw [Set.Finite.mem_toFinset]; exact hc)
  have hface := isFaceOf_inf_reducePattern (φ := φ) (P := P) (t := hPf.toFinset) (s := s) hnt
  have hcell : IsRationalCone (arrangementCone φ (reducePattern φ P hPf.toFinset s) ⊓ P) := by
    have hweq : arrangementCone φ (reducePattern φ P hPf.toFinset s) ⊓ P
        = signConeInf (φ := φ) hPf.toFinset (reducePattern φ P hPf.toFinset s) ⊓ P :=
      arrangementCone_inf_eq_signConeInf_of_mem fun i hi x hx => by
        rw [show reducePattern φ P hPf.toFinset s i = weakPattern φ P i from by
          simp [reducePattern, hi]]
        exact mem_signCone_weakPattern (hnt i hi) hx
    rw [hweq, inf_comm]
    exact isRationalCone_inf_signConeInf hφ _ _ P hP
  exact hcell.of_isFaceOf hface

/-- **The cells of `Σ(H)` are locally rational in `C₊`** (Looijenga, Example 4.3 (b), p. 18). -/
theorem isLocallyRationalCone_arrangementCone (Cplus : PointedCone ℝ (realified V))
    (hφ : ∀ i, IsRationalForm (φ i).toLinearMap)
    (hcut : CutsFinitelyOnRational Cplus φ) (s : ι → SignType) :
    IsLocallyRationalCone Cplus (arrangementCone φ s ⊓ Cplus) := by
  intro P hP hPle
  rw [inf_assoc, inf_eq_right.2 hPle, inf_comm]
  rw [inf_comm]
  exact isRationalCone_arrangementCone_inf hφ hcut s P hP hPle

/-- **`Σ(H)` is a locally rational decomposition of `C₊`** (Looijenga, Example 4.3 (b),
pp. 17-18), from the hypothesis that only finitely many of the hyperplanes cut any rational subcone
of `C₊`:
the cells of the arrangement of such a family `H` decompose `C₊`, each cell is locally rational, and
the faces of the traces on a rational subcone form a rational cone system.

The finiteness of that system is where the hypothesis is used: on a rational cone `P`, every cell
trace is a face of the cell of its reduced pattern (`isFaceOf_inf_reducePattern`), whose pattern is
one of finitely many (`range_reducePattern_finite`), and a rational cone has finitely many faces
(`finite_faces_of_isRationalCone`). With the *vanishing* reading of the earlier hypothesis the same
conclusion followed from `activeForms`; the cost of the corrected reading is that the traces are no
longer traces of the cells of finitely many forms but faces of them, which is why the finiteness
runs through `faceClosure` twice. -/
theorem arrangementDecomposition_isLocallyRational {Cplus : PointedCone ℝ (realified V)}
    (hsal : (Cplus : ConvexCone ℝ (realified V)).Salient)
    (hφ : ∀ i, IsRationalForm (φ i).toLinearMap) (hcut : CutsFinitelyOnRational Cplus φ) :
    IsLocallyRationalDecomposition Cplus (arrangementDecomposition φ Cplus) where
  union_eq := union_arrangementDecomposition φ Cplus
  isLocallyRational σ hσ := by
    obtain ⟨s, rfl⟩ := hσ
    exact isLocallyRationalCone_arrangementCone Cplus hφ hcut s
  restriction P hP hPle := by
    classical
    have hPf := hcut P hP hPle
    set t := hPf.toFinset with ht
    have hnt : ∀ i ∉ t, ¬ CutsOn (φ i).toLinearMap P := by
      intro i hi hc
      rw [ht] at hi
      exact hi (by rw [Set.Finite.mem_toFinset]; exact hc)
    have htrace' : ∀ τ, τ ∈ restrictionTo (arrangementDecomposition φ Cplus) P ↔
        ∃ s : ι → SignType, τ = arrangementCone φ s ⊓ P := by
      intro τ
      constructor
      · rintro ⟨σ, ⟨s, rfl⟩, rfl⟩
        exact ⟨s, by rw [inf_assoc, inf_eq_right.2 hPle]⟩
      · rintro ⟨s, rfl⟩
        exact ⟨arrangementCone φ s ⊓ Cplus, ⟨s, rfl⟩,
          by rw [inf_assoc, inf_eq_right.2 hPle]⟩
    have hcell : ∀ (w : ι → SignType), (∀ i ∉ t, w i = weakPattern φ P i) →
        IsRationalCone (arrangementCone φ w ⊓ P) := by
      intro w hw
      have hweq : arrangementCone φ w ⊓ P = signConeInf (φ := φ) t w ⊓ P :=
        arrangementCone_inf_eq_signConeInf_of_mem fun i hi x hx => by
          rw [hw i hi]
          exact mem_signCone_weakPattern (hnt i hi) hx
      rw [hweq, inf_comm]
      exact isRationalCone_inf_signConeInf hφ w t P hP
    have hsub : restrictionTo (arrangementDecomposition φ Cplus) P ⊆
        ⋃ w ∈ Set.range (reducePattern φ P t),
          {τ : PointedCone ℝ (realified V) | τ.IsFaceOf (arrangementCone φ w ⊓ P)} := by
      intro τ hτ
      obtain ⟨s, rfl⟩ := (htrace' τ).1 hτ
      exact Set.mem_iUnion.2 ⟨reducePattern φ P t s, Set.mem_iUnion.2 ⟨⟨s, rfl⟩,
        isFaceOf_inf_reducePattern (φ := φ) (t := t) (s := s) hnt⟩⟩
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · -- finiteness: the faces of the cells of the finitely many reduced patterns
      have hunion : (⋃ w ∈ Set.range (reducePattern φ P t),
          {τ : PointedCone ℝ (realified V) | τ.IsFaceOf (arrangementCone φ w ⊓ P)}).Finite := by
        refine Set.Finite.biUnion (range_reducePattern_finite (φ := φ) P t) ?_
        intro w hw
        obtain ⟨s, rfl⟩ := hw
        exact finite_faces_of_isRationalCone
          (hcell (reducePattern φ P t s) (fun i hi => by simp [reducePattern, hi]))
      refine hunion.subset ?_
      intro F hF
      obtain ⟨τ, hτ, hFτ⟩ := mem_faceClosure.1 hF
      obtain ⟨w, hw⟩ := Set.mem_iUnion.1 (hsub hτ)
      obtain ⟨hwS, hτw⟩ := Set.mem_iUnion.1 hw
      exact Set.mem_iUnion.2 ⟨w, Set.mem_iUnion.2 ⟨hwS, hFτ.trans hτw⟩⟩
    · -- the faces of the traces are salient
      rintro F ⟨τ, hτ, hFτ⟩
      obtain ⟨s, rfl⟩ := (htrace' τ).1 hτ
      exact hsal.anti fun x hx => hPle (hFτ.le hx).2
    · -- the faces of the traces are rational
      rintro F ⟨τ, hτ, hFτ⟩
      obtain ⟨s, rfl⟩ := (htrace' τ).1 hτ
      have hcellrat := hcell (reducePattern φ P t s) (fun i hi => by simp [reducePattern, hi])
      have hface := isFaceOf_inf_reducePattern (φ := φ) (t := t) (s := s) hnt
      exact (hcellrat.of_isFaceOf hface).of_isFaceOf hFτ
    · -- the faces of a trace are faces of the trace
      rintro F G ⟨τ, hτ, hFτ⟩ hGF
      exact mem_faceClosure.2 ⟨τ, hτ, hGF.trans hFτ⟩
    · -- two traces meet along a common face of each
      rintro F G ⟨τ, hτ, hFτ⟩ ⟨τ', hτ', hGτ'⟩
      obtain ⟨s, rfl⟩ := (htrace' _).1 hτ
      obtain ⟨s', rfl⟩ := (htrace' _).1 hτ'
      have hcell : (arrangementCone φ (commonSignPattern s s')).IsFaceOf (arrangementCone φ s) :=
        isFaceOf_arrangementCone_commonSignPattern s s'
      have hcell' :
          (arrangementCone φ (commonSignPattern s s')).IsFaceOf (arrangementCone φ s') := by
        rw [commonSignPattern_comm]
        exact isFaceOf_arrangementCone_commonSignPattern s' s
      have hHX : (arrangementCone φ (commonSignPattern s s') ⊓ P).IsFaceOf
          (arrangementCone φ s ⊓ P) :=
        isFaceOf_inf_right (F := arrangementCone φ (commonSignPattern s s'))
          (C := arrangementCone φ s) (P := P) hcell
      have hHY : (arrangementCone φ (commonSignPattern s s') ⊓ P).IsFaceOf
          (arrangementCone φ s' ⊓ P) :=
        isFaceOf_inf_right (F := arrangementCone φ (commonSignPattern s s'))
          (C := arrangementCone φ s') (P := P) hcell'
      have hXY : (arrangementCone φ s ⊓ P) ⊓ (arrangementCone φ s' ⊓ P)
          = arrangementCone φ (commonSignPattern s s') ⊓ P := by
        rw [inf_assoc, inf_left_comm P, inf_idem, ← inf_assoc, ← arrangementCone_inf]
      have hXY' : (arrangementCone φ s' ⊓ P) ⊓ (arrangementCone φ s ⊓ P)
          = arrangementCone φ (commonSignPattern s s') ⊓ P := by
        rw [inf_comm (arrangementCone φ s' ⊓ P) (arrangementCone φ s ⊓ P), hXY]
      -- `F ⊓ H` is a face of `H` and of `F`
      have hFH' : (F ⊓ (arrangementCone φ (commonSignPattern s s') ⊓ P)).IsFaceOf F :=
        inf_isFaceOf_of_isFaceOf hFτ hHX
      have hFHX : (F ⊓ (arrangementCone φ (commonSignPattern s s') ⊓ P)).IsFaceOf
          (arrangementCone φ s ⊓ P) := hFH'.trans hFτ
      have hFH : (F ⊓ (arrangementCone φ (commonSignPattern s s') ⊓ P)).IsFaceOf
          (arrangementCone φ (commonSignPattern s s') ⊓ P) :=
        isFaceOf_of_le_of_isFaceOf inf_le_right hFHX hHX
      have hGH' : (G ⊓ (arrangementCone φ (commonSignPattern s s') ⊓ P)).IsFaceOf G :=
        inf_isFaceOf_of_isFaceOf hGτ' hHY
      have hGHY : (G ⊓ (arrangementCone φ (commonSignPattern s s') ⊓ P)).IsFaceOf
          (arrangementCone φ s' ⊓ P) := hGH'.trans hGτ'
      have hGH : (G ⊓ (arrangementCone φ (commonSignPattern s s') ⊓ P)).IsFaceOf
          (arrangementCone φ (commonSignPattern s s') ⊓ P) :=
        isFaceOf_of_le_of_isFaceOf inf_le_right hGHY hHY
      -- the intersection of the two traces is the common cell
      have hFGleH : F ⊓ G ≤ arrangementCone φ (commonSignPattern s s') ⊓ P :=
        hXY ▸ le_inf (inf_le_left.trans hFτ.le) (inf_le_right.trans hGτ'.le)
      have hFG : F ⊓ G = (F ⊓ (arrangementCone φ (commonSignPattern s s') ⊓ P)) ⊓
          (G ⊓ (arrangementCone φ (commonSignPattern s s') ⊓ P)) := by
        refine le_antisymm ?_ ?_
        · exact le_inf (le_inf inf_le_left hFGleH) (le_inf inf_le_right hFGleH)
        · exact le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left)
      rw [hFG]
      exact (inf_isFaceOf_of_isFaceOf hFH hGH).trans hFH'
end ArrangementRational

/-! ## The counting lemma over `ℚ`: integrality in place of compactness

The finiteness step of Example 4.3 (b), in the form the module docstring's (ii) describes.
`realified V` carries no `ProperSpace` instance, so `ZSpan.setFinite_inter` is not available at it,
but nothing in the counting lemma is analytic: a rational form cuts a rational cone exactly when its
values on the cone's *rational generators* take both signs (`cutsOn_iff_generators`), so it is
linear algebra over `ℚ`, and its finiteness comes from integrality. On the `ℤ`-span of a `ℚ`-basis a
vector's coordinates are its pairings with a dual family, so bounding the pairings bounds the
coordinates and leaves finitely many lattice points (`finite_span_int_of_pairings_bounded`). -/

section CountingOverRat

/-- **The sign of a rational form on a rational cone is decided by its values on the generators.**
For a rational cone `P = hull (rationalPoint '' s)` and a linear form that is the extension of a
`ℚ`-linear `q`, the form is nonnegative on `P` exactly when `q` is nonnegative on `s`: the cone hull
is the least cone through `s`, and a halfspace cone is a cone. -/
theorem forall_nonneg_of_forall_nonneg_generators (P : PointedCone ℝ (realified V)) {s : Finset V}
    (hP : P = PointedCone.hull ℝ (rationalPoint '' (s : Set V)))
    {φ : (realified V) →ₗ[ℝ] ℝ} {q : V →ₗ[ℚ] ℚ}
    (hq : ∀ v : V, φ (rationalPoint v) = (q v : ℝ)) :
    (∀ x ∈ P, 0 ≤ φ x) ↔ ∀ v ∈ s, 0 ≤ q v := by
  constructor
  · intro h v hv
    have hmem : rationalPoint v ∈ P :=
      hP ▸ PointedCone.subset_hull (Set.mem_image_of_mem _ (by exact_mod_cast hv))
    have := h _ hmem
    rw [hq v] at this
    exact_mod_cast this
  · intro h x hx
    have hle : P ≤ halfspaceCone φ := by
      rw [hP]
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨v, hv, rfl⟩
      rw [SetLike.mem_coe, mem_halfspaceCone, hq v]
      exact_mod_cast h v hv
    have := hle hx
    rwa [mem_halfspaceCone] at this

/-- **Cutting a rational cone is decided on its rational generators**: for a rational cone
`P = hull (rationalPoint '' s)` and a form that is the extension of a `ℚ`-linear `q`, the form takes
both signs on `P` exactly when `q` takes both signs on `s`. This is what makes the counting lemma
linear algebra over `ℚ` rather than analysis on `L(ℝ)`. -/
theorem cutsOn_iff_generators (P : PointedCone ℝ (realified V)) {s : Finset V}
    (hP : P = PointedCone.hull ℝ (rationalPoint '' (s : Set V)))
    {ψ : (realified V) →ₗ[ℝ] ℝ} {q : V →ₗ[ℚ] ℚ}
    (hq : ∀ v : V, ψ (rationalPoint v) = (q v : ℝ)) :
    CutsOn ψ P ↔ (∃ v ∈ s, 0 < q v) ∧ ∃ v ∈ s, q v < 0 := by
  have hpos := forall_nonneg_of_forall_nonneg_generators (V := V) P hP (φ := ψ) (q := q) hq
  have hneg := forall_nonneg_of_forall_nonneg_generators (V := V) P hP (φ := -ψ) (q := -q)
    (fun v => by simp [hq v])
  rw [CutsOn]
  constructor
  · rintro ⟨⟨x, hx, hxpos⟩, ⟨y, hy, hyneg⟩⟩
    refine ⟨?_, ?_⟩
    · by_contra hcon
      push Not at hcon
      have hle : ∀ z ∈ P, ψ z ≤ 0 := by
        have := hneg.mpr (fun v hv => by simpa using hcon v hv)
        simpa using this
      linarith [hle x hx]
    · by_contra hcon
      push Not at hcon
      have hle : ∀ z ∈ P, 0 ≤ ψ z := hpos.mpr hcon
      linarith [hle y hy]
  · rintro ⟨⟨v, hv, hvpos⟩, ⟨w, hw, hwneg⟩⟩
    refine ⟨⟨rationalPoint v, ?_, by rw [hq v]; exact_mod_cast hvpos⟩,
      ⟨rationalPoint w, ?_, by rw [hq w]; exact_mod_cast hwneg⟩⟩
    · exact hP ▸ PointedCone.subset_hull (Set.mem_image_of_mem _ (by exact_mod_cast hv))
    · exact hP ▸ PointedCone.subset_hull (Set.mem_image_of_mem _ (by exact_mod_cast hw))

/-! ## The cut of a `ℚ`-hyperplane: the hyperplane of a line, and the form of its generator

`H` is carried by the `ℚ`-lines of its normals (`orbitFamily`); a member *cuts* a cone when the
cone has points on both sides of the hyperplane that line cuts out (`HyperplaneCuts`). This section
identifies the cut of the hyperplane with the cut of the form `x ↦ ⟨v, x⟩` of a generator `v` of the
line (`hyperplaneCuts_iff_cutsOn`), so that the counting lemma over `ℚ` decides it on the rational
generators of a rational cone (`hyperplaneCuts_iff_generators`, by `cutsOn_iff_generators`). -/

/-- The real form of a rational covector as a continuous linear form: on the module topology every
linear form is continuous (`IsModuleTopology.continuous_of_linearMap`), so no continuity hypothesis
enters. -/
noncomputable def normalForm (Q : QuadraticForm ℝ (realified V)) (v : V) :
    (realified V) →L[ℝ] ℝ :=
  ⟨(associated Q) (rationalPoint v), IsModuleTopology.continuous_of_linearMap _⟩

@[simp] theorem normalForm_apply (Q : QuadraticForm ℝ (realified V)) (v : V)
    (x : realified V) : normalForm Q v x = (associated Q) (rationalPoint v) x := rfl

theorem normalForm_toLinearMap (Q : QuadraticForm ℝ (realified V)) (v : V) :
    (normalForm Q v).toLinearMap = (associated Q) (rationalPoint v) := rfl


/-- The `ℝ`-hyperplane of a `ℚ`-line of normals: the orthogonal complement in `L(ℝ)` of the real
span of the rational points of the line. An element of `orbitFamily` carries a `ℚ`-hyperplane by
its normal line, and this is the hyperplane itself. -/
noncomputable def hyperplaneOf (Q : QuadraticForm ℝ (realified V)) (ℓ : Submodule ℚ V) :
    Submodule ℝ (realified V) :=
  LinearMap.BilinForm.orthogonal (associated Q)
    (Submodule.span ℝ (rationalPoint '' (ℓ : Set V)))

/-- **The hyperplane of a line is the kernel of the form of its generator.** -/
theorem hyperplaneOf_span_singleton (Q : QuadraticForm ℝ (realified V)) {ℓ : Submodule ℚ V}
    {v : V} (hℓ : ℓ = Submodule.span ℚ ({v} : Set V)) :
    hyperplaneOf Q ℓ = LinearMap.ker ((associated Q) (rationalPoint v)) := by
  have hcoe : (Submodule.map (rationalPoint (V := V)) ℓ : Set (realified V))
      = rationalPoint (V := V) '' (ℓ : Set V) := rfl
  have hmap : Submodule.map (rationalPoint (V := V)) ℓ
      = Submodule.span ℚ ({rationalPoint v} : Set (realified V)) := by
    rw [hℓ, Submodule.map_span, Set.image_singleton]
  have hspan : Submodule.span ℝ (rationalPoint (V := V) '' (ℓ : Set V))
      = Submodule.span ℝ ({rationalPoint v} : Set (realified V)) := by
    rw [← hcoe, hmap, Submodule.span_span_of_tower]
  rw [hyperplaneOf, hspan]
  refine le_antisymm ?_ ?_
  · intro x hx
    rw [LinearMap.mem_ker]
    exact (LinearMap.BilinForm.mem_orthogonal_iff.mp hx) (rationalPoint v)
      (Submodule.subset_span rfl)
  · intro x hx
    rw [LinearMap.mem_ker] at hx
    refine LinearMap.BilinForm.mem_orthogonal_iff.mpr ?_
    intro y hy
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hy
    rw [← hc, map_smul, LinearMap.smul_apply, smul_eq_mul, hx, mul_zero]

/-- Two points of `L(ℝ)` lie on *opposite sides* of a hyperplane when neither lies on it and the
segment between them meets it. This is what "the hyperplane separates them" means below, and it
names no linear form, only the hyperplane. -/
def OppositeSides (H : Submodule ℝ (realified V)) (x y : realified V) : Prop :=
  x ∉ H ∧ y ∉ H ∧ ∃ t : ℝ, 0 < t ∧ t < 1 ∧ t • x + (1 - t) • y ∈ H

/-- **A `ℚ`-hyperplane cuts a cone**: the cone has two points on opposite sides of it. This is
Looijenga's "meets" for the hyperplanes of `H` in Example 4.3 (b), p. 18
(`.tmp-sources/looijenga-math0201218v2.md:487`), stated for the cone a hyperplane cuts — `CutsOn`
for a form, of which `hyperplaneCuts_iff_cutsOn` below shows this is the form-free version. -/
def HyperplaneCuts (Q : QuadraticForm ℝ (realified V)) (ℓ : Submodule ℚ V)
    (P : PointedCone ℝ (realified V)) : Prop :=
  ∃ x ∈ P, ∃ y ∈ P, OppositeSides (hyperplaneOf Q ℓ) x y

/-- **A hyperplane cuts a cone exactly when the form of its normal does**: for `ℓ = ℚ v` the
hyperplane is the kernel of `x ↦ ⟨v, x⟩` (`hyperplaneOf_span_singleton`), and both notions of
cutting say that the form takes both signs on the cone. -/
theorem hyperplaneCuts_iff_cutsOn (Q : QuadraticForm ℝ (realified V)) {ℓ : Submodule ℚ V}
    {v : V} (hℓ : ℓ = Submodule.span ℚ ({v} : Set V)) (P : PointedCone ℝ (realified V)) :
    HyperplaneCuts Q ℓ P ↔ CutsOn ((associated Q) (rationalPoint v)) P := by
  unfold HyperplaneCuts OppositeSides
  rw [hyperplaneOf_span_singleton Q hℓ]
  constructor
  · rintro ⟨x, hxP, y, hyP, hxH, hyH, t, ht0, ht1, hmem⟩
    rw [LinearMap.mem_ker] at hmem
    rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul] at hmem
    have hx0 : ((associated Q) (rationalPoint v)) x ≠ 0 := fun h => hxH (LinearMap.mem_ker.mpr h)
    have hy0 : ((associated Q) (rationalPoint v)) y ≠ 0 := fun h => hyH (LinearMap.mem_ker.mpr h)
    rcases lt_or_gt_of_ne hx0 with hxneg | hxpos
    · refine ⟨⟨y, hyP, ?_⟩, ⟨x, hxP, hxneg⟩⟩
      nlinarith
    · refine ⟨⟨x, hxP, hxpos⟩, ⟨y, hyP, ?_⟩⟩
      nlinarith
  · rintro ⟨⟨x, hxP, hxpos⟩, ⟨y, hyP, hyneg⟩⟩
    have hx0 : ((associated Q) (rationalPoint v)) x ≠ 0 := ne_of_gt hxpos
    have hy0 : ((associated Q) (rationalPoint v)) y ≠ 0 := ne_of_lt hyneg
    refine ⟨x, hxP, y, hyP, ?_, ?_, (-((associated Q) (rationalPoint v)) y) /
      (((associated Q) (rationalPoint v)) x - ((associated Q) (rationalPoint v)) y),
      ?_, ?_, ?_⟩
    · exact fun h => hx0 (LinearMap.mem_ker.mp h)
    · exact fun h => hy0 (LinearMap.mem_ker.mp h)
    · have hpos : 0 < ((associated Q) (rationalPoint v)) x -
          ((associated Q) (rationalPoint v)) y := by linarith
      exact div_pos (by linarith) hpos
    · have hpos : 0 < ((associated Q) (rationalPoint v)) x -
          ((associated Q) (rationalPoint v)) y := by linarith
      rw [div_lt_one hpos]
      linarith
    · rw [LinearMap.mem_ker, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
      have hne : ((associated Q) (rationalPoint v)) x
          - ((associated Q) (rationalPoint v)) y ≠ 0 := by
        intro h0
        linarith
      field_simp
      ring

/-- **Cutting is decided on the cone's rational generators**: for a rational cone
`P = hull (rationalPoint '' s)` and the form of a normal `v`, the hyperplane of `ℓ = ℚ v` cuts `P`
exactly when the ℚ-linear form `w ↦ ⟨v, w⟩` takes both signs on `s`. -/
theorem hyperplaneCuts_iff_generators (Q : QuadraticForm ℝ (realified V)) {ℓ : Submodule ℚ V}
    {v : V} (hℓ : ℓ = Submodule.span ℚ ({v} : Set V))
    {P : PointedCone ℝ (realified V)} {s : Finset V}
    (hP : P = PointedCone.hull ℝ (rationalPoint '' (s : Set V)))
    {BQ : LinearMap.BilinForm ℚ V}
    (hBQ : ∀ u w : V, (associated Q) (rationalPoint u) (rationalPoint w) = (BQ u w : ℝ)) :
    HyperplaneCuts Q ℓ P ↔ (∃ a ∈ s, 0 < BQ v a) ∧ ∃ b ∈ s, BQ v b < 0 := by
  rw [hyperplaneCuts_iff_cutsOn Q hℓ P]
  exact cutsOn_iff_generators P hP (q := BQ v) (fun w => hBQ v w)

/-! ## The bound per pair of generators: the three cases of the counting lemma

The counting lemma's finiteness is not analytic: on a rational cone `P` of `C₊` a spacelike normal
`ℓ` of fixed value `Q ℓ = -m` that *cuts* `P` takes both signs on the generators of `P`
(`cutsOn_iff_generators`), and the pair of generators on which the two signs are taken bounds `ℓ`
in the two cases that are pure linear algebra over the form, with integrality needed only in the
third. Looijenga, Example 4.3 (b), p. 18, is where the arithmeticity of `Γ` enters: it fixes the
values `ℓ²`, and these bounds then leave finitely many lattices vectors per value.

The three cases, on a pair `a`, `b` of generators with `ℓ · a > 0 > ℓ · b`:

* both timelike (`0 < Q a`, `0 < Q b`): the plane of the pair is hyperbolic, its orthogonal
  complement is negative definite, and the pairing form of the pair bounds both pairings by the Gram
  data alone (`abs_associated_le_of_both_timelike`);
* one isotropic (`Q b = 0`): the relation is a hyperbola, so what is bounded is the *product* of the
  two pairings plus the pairing with the isotropic generator (`abs_associated_le_of_isotropic`);
* both isotropic (`Q a = Q b = 0`): only the product is bounded
  (`abs_associated_mul_le_of_both_isotropic`).

In the last two the product bounds neither pairing by itself, and that is where the lattice enters:
the pairing of `ℓ` with a generator is a nonzero rational whose denominator is bounded, so it is
bounded *away* from `0`, and `abs_le_of_abs_mul_le_of_one_div_le` converts the product bound into a
bound on the other pairing. Over `ℝ` this fails, which is why the statement is not a statement about
`L(ℝ)`: the module docstring's family `ℓ_N = (N, N + 1/N, 0)` is exactly a cut whose pairing with
the isotropic generator goes to `0` while its value stays `-m`.

All statements are general in the form and in the pair: the cone enters only through the sheet
hypotheses `0 ≤ Q a`, `0 ≤ Q b` and `0 < a · b`, which hold for the generators of `C₊`
(`nonneg_associated_of_mem_closedSheet`), and no coordinates of a chosen lattice appear.

## LC-09 search record for these bounds (2026-11-15, #161, fourth unit)

The six queries of this unit, with every hit. `content:hyperbolic plane metric signature`: 20 files,
752 matches, none returned as a file for the pairing bound. `content:negative definite orthogonal
complement positive index`: 48 files, 3254 matches, 1 returned — QudeLeap `QuantumAlg/Util/Matrix/
Trace/Norm.lean`, positive semidefinite matrices and trace norms, unrelated (the statement it was
meant to find, that the orthogonal complement of a positive vector in a form of positive index `1`
is negative semidefinite, is `mul_self_le_associated_sq` in this repository's
`PositiveCone.lean:125`, one line away). `content:reverse Cauchy-Schwarz Lorentzian`: the client's
time limit, no result. `content:spacelike vector pairing bound timelike`: 1 file, 108 matches, the
physlib import list — the `Relativity/Causality` files are light cones, not signature-form pairings.
`content:Gram matrix determinant signature two timelike`: 0 files. `content:isotropic quotient
negative definite`: 11 files, 475 matches, nothing on the quotient's definiteness (that statement
this repository owns at `sigPos_isotropicQuotientForm`, `IsotropicQuotientSignature.lean:513`, and
the isotropy case below does not need it). Nothing to port: the engine and the three cases are
residue, built on Mathlib's `quadratic_expand`-shaped polarization and this repository's
`mul_self_le_associated_sq`.

-/

section PairingBounds

variable [Module.Finite ℚ V]

/-- **The orthogonal complement of a positive vector is negative semidefinite**, in one line from
the key inequality of signature `(1, n)` (`mul_self_le_associated_sq`, `PositiveCone.lean:125`):
`Q w · Q a ≤ (w · a)²`, so a vector orthogonal to a vector of positive value has nonpositive
value. This is what makes the plane spanned by two generators of `C₊` split into a hyperbolic part
and a negative definite part. -/
theorem quadratic_nonpos_of_associated_eq_zero {Q : QuadraticForm ℝ (realified V)}
    (hpos : sigPos Q = 1) {a w : realified V} (ha : 0 < Q a)
    (h : (associated Q) w a = 0) : Q w ≤ 0 := by
  have h1 := mul_self_le_associated_sq (Q := Q) hpos ha w
  rw [h] at h1
  nlinarith

/-- **The quadratic relation at a pair of generators of the sheet.** For `a`, `b` in the closed
sheet (`0 ≤ Q a`, `0 ≤ Q b`, `a · b > 0`) spanning a hyperbolic plane (`a · b² > Q a · Q b`), and a
spacelike `ℓ` (`Q ℓ = -m`), the pairings `x = ℓ · a`, `y = ℓ · b` satisfy

`Q b · x² - 2 (a · b) x y + Q a · y² ≤ m (a · b² - Q a · Q b)`.

That is the pairing form of `Q u ≥ -m`, where `u` is the component of `ℓ` in the plane of the pair:
`u` is the combination of `a`, `b` whose pairings are `x` and `y`, `w = ℓ - u` is orthogonal to
both, hence to `a + b`, whose value is `Q a + 2 (a · b) + Q b > 0`, so `Q w ≤ 0` and
`Q u = Q ℓ - Q w ≥ -m`; and the quadratic form of `u` in terms of `x`, `y` has matrix the inverse
of the Gram matrix of the pair, which is `K = a · b² - Q a · Q b` times the displayed form. Both
steps are division-free in the statement and the case analysis below only uses the displayed
inequality. -/
theorem pairing_quadratic_bound {Q : QuadraticForm ℝ (realified V)} (hpos : sigPos Q = 1)
    {a b l : realified V} {m : ℝ}
    (ha : 0 ≤ Q a) (hb : 0 ≤ Q b) (hab : 0 < (associated Q) a b)
    (hKh : 0 < (associated Q) a b ^ 2 - Q a * Q b) (hQl : Q l = -m) :
    Q b * (associated Q) l a ^ 2
        - 2 * (associated Q) a b * ((associated Q) l a * (associated Q) l b)
        + Q a * (associated Q) l b ^ 2
      ≤ m * ((associated Q) a b ^ 2 - Q a * Q b) := by
  set A : ℝ := Q a with hA
  set B : ℝ := Q b with hB
  set c : ℝ := (associated Q) a b with hc
  set x : ℝ := (associated Q) l a with hx
  set y : ℝ := (associated Q) l b with hy
  set K : ℝ := c ^ 2 - A * B with hK
  have hKpos : 0 < K := by rw [hK]; exact hKh
  set al : ℝ := (c * y - B * x) / K with hal
  set be : ℝ := (c * x - A * y) / K with hbe
  have hKne : K ≠ 0 := hKpos.ne'
  have hKN : c ^ 2 - A * B ≠ 0 := by rw [← hK]; exact hKne
  have hrel1 : A * al + c * be = x := by
    rw [hal, hbe, hK, mul_div_assoc', mul_div_assoc', ← add_div, div_eq_iff hKN]
    ring
  have hrel2 : c * al + B * be = y := by
    rw [hal, hbe, hK, mul_div_assoc', mul_div_assoc', ← add_div, div_eq_iff hKN]
    ring
  set u : realified V := al • a + be • b with hu
  set w : realified V := l - u with hw
  have huA : (associated Q) u a = A * al + c * be := by
    rw [hu, map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply, smul_eq_mul]
    rw [map_smul, LinearMap.smul_apply, smul_eq_mul, associated_self_apply,
      associated_comm (Q := Q) b a]
    rw [← hA, ← hc]
    ring
  have huB : (associated Q) u b = c * al + B * be := by
    rw [hu, map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply, smul_eq_mul]
    rw [map_smul, LinearMap.smul_apply, smul_eq_mul, associated_self_apply]
    rw [← hB, ← hc]
    ring
  have hwa : (associated Q) w a = 0 := by
    rw [hw, map_sub, LinearMap.sub_apply, huA, hrel1, ← hx, sub_self]
  have hwb : (associated Q) w b = 0 := by
    rw [hw, map_sub, LinearMap.sub_apply, huB, hrel2, ← hy, sub_self]
  have hta : 0 < Q (a + b) := by
    rw [show a + b = (1 : ℝ) • a + (1 : ℝ) • b by simp, quadratic_expand]
    rw [← hA, ← hB, ← hc]
    nlinarith
  have htw : (associated Q) w (a + b) = 0 := by
    simp only [map_add, hwa, hwb, add_zero]
  have hQw : Q w ≤ 0 := quadratic_nonpos_of_associated_eq_zero hpos hta htw
  have hQu : -m ≤ Q u := by
    have huw : (associated Q) u w = 0 := by
      rw [hu, map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply, smul_eq_mul,
        map_smul, LinearMap.smul_apply, smul_eq_mul,
        associated_comm (Q := Q) a w, associated_comm (Q := Q) b w, hwa, hwb]
      ring
    have hl : l = u + w := by rw [hw]; abel
    have hexp : Q l = Q u + Q w := by
      conv_lhs => rw [hl]
      rw [show u + w = (1 : ℝ) • u + (1 : ℝ) • w by simp, quadratic_expand, huw]
      ring
    rw [hQl] at hexp
    linarith
  have hQu' : Q u = A * al ^ 2 + 2 * al * be * c + B * be ^ 2 := by
    rw [hu, quadratic_expand]
    rw [← hA, ← hB, ← hc]
    ring
  have hide : B * x ^ 2 - 2 * c * (x * y) + A * y ^ 2
      = -(K * (A * al ^ 2 + 2 * al * be * c + B * be ^ 2)) := by
    rw [← hrel1, ← hrel2, hK]
    ring
  rw [hide, ← hQu']
  nlinarith [hQu, hKpos]

/-- **The bound of the counting lemma, both generators timelike**: the hyperbola
`Q b · x² - 2 (a · b) x y + Q a · y² ≤ m K` of `pairing_quadratic_bound` has all three terms
nonpositive for `x > 0 > y` (because `a · b > 0`), so both pairings of `ℓ` with the pair are
bounded by the Gram data of the pair alone — no integrality, no denominator. -/
theorem abs_associated_le_of_both_timelike {Q : QuadraticForm ℝ (realified V)}
    (hpos : sigPos Q = 1) {a b l : realified V} {m : ℝ}
    (ha : 0 < Q a) (hb : 0 < Q b) (hab : 0 < (associated Q) a b)
    (hK : 0 < (associated Q) a b ^ 2 - Q a * Q b)
    (hQl : Q l = -m) (hx : 0 < (associated Q) l a) (hy : (associated Q) l b < 0) :
    |(associated Q) l a| ≤ Real.sqrt (m * ((associated Q) a b ^ 2 - Q a * Q b) / Q b) ∧
      |(associated Q) l b| ≤ Real.sqrt (m * ((associated Q) a b ^ 2 - Q a * Q b) / Q a) := by
  set A : ℝ := Q a with hA
  set B : ℝ := Q b with hB
  set c : ℝ := (associated Q) a b with hc
  set x : ℝ := (associated Q) l a with hxd
  set y : ℝ := (associated Q) l b with hyd
  set K : ℝ := c ^ 2 - A * B with hKd
  have hmain : B * x ^ 2 - 2 * c * (x * y) + A * y ^ 2 ≤ m * K := by
    rw [hxd, hyd, hA, hB, hc, hKd]
    exact pairing_quadratic_bound hpos ha.le hb.le hab (by rw [← hKd]; exact hK) hQl
  have hxy : x * y < 0 := mul_neg_of_pos_of_neg hx hy
  have hcx : c * (x * y) < 0 := mul_neg_of_pos_of_neg hab hxy
  have hy2 : 0 < y ^ 2 := sq_pos_of_ne_zero hy.ne
  constructor
  · have h1 : x ^ 2 < m * K / B := by
      rw [lt_div_iff₀ hb]
      nlinarith [hmain, hcx, hy2]
    calc |x| = Real.sqrt (x ^ 2) := (Real.sqrt_sq_eq_abs x).symm
      _ ≤ Real.sqrt (m * K / B) := Real.sqrt_le_sqrt h1.le
  · have h1 : y ^ 2 < m * K / A := by
      rw [lt_div_iff₀ ha]
      nlinarith [hmain, hcx, hy2]
    calc |y| = Real.sqrt (y ^ 2) := (Real.sqrt_sq_eq_abs y).symm
      _ ≤ Real.sqrt (m * K / A) := Real.sqrt_le_sqrt h1.le

/-- **The bound of the counting lemma, one generator isotropic**: with `Q b = 0` the relation of
`pairing_quadratic_bound` reads `2 (a · b) x |y| + Q a · y² ≤ m (a · b)²`, a hyperbola rather than a
box: the pairing with `b` is bounded by `a · b · sqrt (m / Q a)` and the *product* of the two
pairings by `m (a · b) / 2`. This is the case that fails over `ℝ`: the family
`ℓ_N = (N, N + 1/N, 0)` of the module docstring keeps `Q ℓ = -m` and cuts for every `N` by
letting the pairing with the isotropic generator tend to `0`, which is why the finiteness of the
counting lemma needs the integrality of that pairing — `abs_le_of_abs_mul_le_of_one_div_le` below
turns a lower bound `1/D` on it into an upper bound on the other pairing. -/
theorem abs_associated_le_of_isotropic {Q : QuadraticForm ℝ (realified V)}
    (hpos : sigPos Q = 1) {a b l : realified V} {m : ℝ}
    (ha : 0 < Q a) (hb : Q b = 0) (hab : 0 < (associated Q) a b)
    (hQl : Q l = -m) (hx : 0 < (associated Q) l a) (hy : (associated Q) l b < 0) :
    |(associated Q) l b| ≤ (associated Q) a b * Real.sqrt (m / Q a) ∧
      |(associated Q) l a| * |(associated Q) l b| ≤ m * (associated Q) a b / 2 := by
  set A : ℝ := Q a with hA
  set c : ℝ := (associated Q) a b with hc
  set x : ℝ := (associated Q) l a with hxd
  set y : ℝ := (associated Q) l b with hyd
  have hB0 : Q b = 0 := hb
  have hmain : -(2 * c * (x * y)) + A * y ^ 2 ≤ m * c ^ 2 := by
    have h := pairing_quadratic_bound (Q := Q) hpos (a := a) (b := b) (l := l) (m := m)
      ha.le hb.ge hab (by rw [hb]; nlinarith) hQl
    rw [hb] at h
    simpa [hxd, hyd, hA, hc] using h
  have hc0 : 0 < c := hc ▸ hab
  have hA0 : 0 < A := hA ▸ ha
  have hxy : x * y < 0 := mul_neg_of_pos_of_neg (hxd ▸ hx) (hyd ▸ hy)
  have hcx : c * (x * y) < 0 := mul_neg_of_pos_of_neg hc0 hxy
  have hy2 : 0 < y ^ 2 := sq_pos_of_ne_zero (hyd ▸ hy).ne
  constructor
  · have h1 : y ^ 2 ≤ m * c ^ 2 / A := by
      rw [le_div_iff₀ hA0]
      nlinarith [hmain, hcx]
    have h3 : Real.sqrt (m * c ^ 2 / A) = c * Real.sqrt (m / A) := by
      rw [show m * c ^ 2 / A = c ^ 2 * (m / A) by field_simp]
      rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hc0.le]
    rw [(Real.sqrt_sq_eq_abs y).symm, ← h3]
    exact Real.sqrt_le_sqrt h1
  · rw [abs_of_pos (hxd ▸ hx), abs_of_neg (hyd ▸ hy)]
    have h2 : 2 * c * (x * -y) ≤ m * c ^ 2 := by nlinarith [hmain, hy2]
    rw [show x * -y = -(x * y) by ring]
    nlinarith [h2, hc0]

/-- **The bound of the counting lemma, both generators isotropic**: with `Q a = Q b = 0` only the
mixed term survives, so the relation of `pairing_quadratic_bound` is `2 (a · b) x |y| ≤ m (a · b)²`
and the product of the two pairings is bounded by `m (a · b) / 2`. Both the pairing with `a` and the
pairing with `b` have to be bounded away from `0` by integrality for the product to bound either. -/
theorem abs_associated_mul_le_of_both_isotropic {Q : QuadraticForm ℝ (realified V)}
    (hpos : sigPos Q = 1) {a b l : realified V} {m : ℝ}
    (ha : Q a = 0) (hb : Q b = 0) (hab : 0 < (associated Q) a b)
    (hQl : Q l = -m) (hx : 0 < (associated Q) l a) (hy : (associated Q) l b < 0) :
    |(associated Q) l a| * |(associated Q) l b| ≤ m * (associated Q) a b / 2 := by
  set c : ℝ := (associated Q) a b with hc
  set x : ℝ := (associated Q) l a with hxd
  set y : ℝ := (associated Q) l b with hyd
  have hmain : -(2 * c * (x * y)) ≤ m * c ^ 2 := by
    have h := pairing_quadratic_bound (Q := Q) hpos (a := a) (b := b) (l := l) (m := m)
      ha.ge hb.ge hab (by rw [ha, hb]; nlinarith) hQl
    rw [ha, hb] at h
    simpa [hxd, hyd, hc] using h
  have hc0 : 0 < c := hc ▸ hab
  rw [abs_of_pos (hxd ▸ hx), abs_of_neg (hyd ▸ hy)]
  have h2 : 2 * c * (x * -y) ≤ m * c ^ 2 := by nlinarith [hmain]
  rw [show x * -y = -(x * y) by ring]
  nlinarith [h2, hc0]

/-- **Integrality in place of compactness**: a lower bound `1/D` on one pairing turns a bound on
the product of two pairings into an upper bound on the other pairing. This is the step that fails
over `ℝ` — where `1/D` is replaced by `|y| > 0` and `C / |y|` is unbounded — and the reason the
counting lemma is a statement about a lattice `Λ` and not about `L(ℝ)`. -/
theorem abs_le_of_abs_mul_le_of_one_div_le {x y C D : ℝ} (hC : 0 ≤ C) (hD : 0 < D)
    (hy : 1 / D ≤ |y|) (h : |x| * |y| ≤ C) : |x| ≤ C * D := by
  have hy0 : 0 < |y| := lt_of_lt_of_le (by positivity) hy
  have hCD : 0 ≤ C * D := mul_nonneg hC hD.le
  have h1 : |x| ≤ C / |y| := (le_div_iff₀ hy0).mpr h
  have h2 : C / |y| ≤ C * D := by
    rw [div_le_iff₀ hy0]
    calc C = C * D * (1 / D) := by field_simp
      _ ≤ C * D * |y| := by nlinarith [hy, hCD]
  linarith

end PairingBounds

section Lattice

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Finitely many lattice points with bounded pairings.** The dual family of a basis is
*Mathlib's* `LinearMap.BilinForm.dualBasis`, not a restatement of it: it is the image of the dual
basis under `B.toDual` (`Mathlib/LinearAlgebra/BilinearForm/Properties.lean:376`), it pairs as
`B (b j) (B.dualBasis hB b k) = δ j k` (`apply_dualBasis_left` `:390` composed with symmetry,
`apply_dualBasis_right` `:396`), and the coordinate of a vector against it is the pairing
(`dualBasis_repr_apply` `:384` read through `dualBasis_dualBasis` `:413`). With that, bounded
pairings bound the integer coordinates of the `ℤ`-span of the basis, and a box of integer
coordinates is finite. This is where the counting lemma's finiteness comes from: no topology, only
integrality. -/
theorem finite_span_int_of_pairings_bounded {b : Module.Basis ι ℚ V}
    {B : LinearMap.BilinForm ℚ V} (hB : B.Nondegenerate) (hBsym : B.IsSymm) (C : ι → ℕ) :
    {v : V | v ∈ Submodule.span ℤ (Set.range b) ∧
      ∀ k, |B v (B.dualBasis hB b k)| ≤ C k}.Finite := by
  classical
  have hbox : {n : ι → ℤ | ∀ k, |n k| ≤ (C k : ℤ)}.Finite := by
    have hsub : {n : ι → ℤ | ∀ k, |n k| ≤ (C k : ℤ)}
        ⊆ Set.univ.pi fun k => Set.Icc (-(C k : ℤ)) (C k) := by
      intro n hn
      rw [Set.mem_pi]
      intro k _
      rw [Set.mem_Icc]
      exact abs_le.mp (hn k)
    exact (Set.Finite.pi fun k => Set.finite_Icc (α := ℤ) _ _).subset hsub
  refine Set.Finite.subset (hbox.image fun n => ∑ k, algebraMap ℤ ℚ (n k) • b k) ?_
  rintro v ⟨hv, hb⟩
  choose n hn using fun k => (b.mem_span_iff_repr_mem ℤ v).mp hv k
  have hsum : ∑ k, algebraMap ℤ ℚ (n k) • b k = v := by
    rw [← b.sum_repr v]
    exact Finset.sum_congr rfl fun k _ => by rw [hn k]
  refine ⟨n, ?_, hsum⟩
  intro k
  have hpair : B v (B.dualBasis hB b k) = (n k : ℚ) := by
    have hrepr : B v (B.dualBasis hB b k) = b.repr v k := by
      rw [← LinearMap.BilinForm.dualBasis_repr_apply hB (B.dualBasis hB b) v k,
        LinearMap.BilinForm.dualBasis_dualBasis hB hBsym b]
    rw [hrepr]
    exact (hn k).symm
  have hbound := hb k
  rw [hpair] at hbound
  rw [← Int.cast_abs, ← Int.cast_natCast, Int.cast_le] at hbound
  exact hbound

end Lattice

/-! ## The counting lemma over `ℚ`: from the pair bounds to finitely many normals

The last step of the finiteness argument of Example 4.3 (b), pp. 17-18. The section above reduced a
normal `ℓ` of value `Q ℓ = -m` that takes both signs on a pair `a`, `b` of generators of `C₊` to a
bound on the pairings `ℓ · a` and `ℓ · b`; what is carried here is the rest: those bounds bound `ℓ`
*itself*, and a lattice has finitely many points in a bounded set.

* `abs_associated_le_of_pairing_bound`: **a bound on one pairing bounds every pairing.** With `t` of
  positive value and `w = spatialPart Q t ℓ` the projection off the line `ℝ t`,
  `ℓ = ((ℓ·t)/Q t) • t + w` and `Q w = Q ℓ - (ℓ·t)²/Q t ≥ -m - L²/Q t` for `|ℓ·t| ≤ L`, and the
  reverse Cauchy–Schwarz inequality on `t^⊥` (`associated_spatialPart_sq_le`) gives
  `|w·z| ≤ sqrt((-Q w)(-Q (spatialPart Q t z)))`. So every pairing of `ℓ` is bounded by an explicit
  constant depending on `z`, on `m` and on `L`. The bound `L` comes from the pair: at `t = a + b`
  the pairing `ℓ·t = ℓ·a + ℓ·b` is bounded by the two pair bounds of the section above.
* `finite_cutting_of_pairing_bounds`: **bounded pairings leave finitely many lattice vectors.** For
  a `ℚ`-basis `bs` of `L(ℚ)` and the rational form `BQ` of `associated Q`, the bound of the previous
  item applied to each vector of Mathlib's `BQ.dualBasis hBQnd bs` is a bound on the pairings with a
  family spanning `L(ℚ)`, and `finite_span_int_of_pairings_bounded` makes the set finite: no
  `ProperSpace`, no compactness, only integrality and the `ℤ`-span.
* `finite_cutting_normals_of_both_timelike` and `finite_cutting_normals_of_isotropic`: the two
  discharged cases, where the pair bounds of `abs_associated_le_of_both_timelike` (both generators
  timelike) and of `abs_associated_le_of_isotropic` (one isotropic) become the `Cx`, `Cy` of the
  finiteness lemma. The isotropic case needs one thing more, supplied by
  `one_div_le_abs_of_integral`: a nonzero value of the form on the lattice is at least `1/D` in
  absolute value, `D` the denominator of the generator, so
  `abs_le_of_abs_mul_le_of_one_div_le` bounds the *other* pairing by the product bound. That is the
  step that fails over `ℝ`, where the same estimates leave the family `ℓ_N = (N, N + 1/N, 0)`
  cutting for every `N`.
* `finite_cutters_of_pair_bounds`: **and finitely many of them cut.** The cutting condition is the
  disjunction, over the finitely many ordered pairs of generators, of the two sign conditions
  (`cutsOn_iff_generators`), so finiteness for every ordered pair gives finiteness for the cutters.

### What the pieces are for

* The case of two isotropic generators: `abs_associated_mul_le_of_both_isotropic` gives the product
  bound, and the same denominator argument with *both* denominators bounds both pairings —
  `finite_cutting_normals_of_both_isotropic`, in this section.

### What is not carried here
* **The orbit layer of step (i), now carried for the norms.** `H` is not a finite family: a finite
  family cuts every cone finitely for a trivial reason, so the statement would say nothing about the
  issue. It is the `Set` `orbitFamily H₀ Γ` — the union of the `Γ`-orbits of the finitely many
  representatives `H₀`, Looijenga's "collection of `Q`-hyperplanes of `L` which meet `C`" (Example
  4.3 (b), p. 18; `.tmp-sources/looijenga-math0201218v2.md:487`), infinite as soon as `Γ` is. What
  the arithmeticity of `Γ` then gives, and what the last section of this file carries, is that *the
  normals take finitely many values*: for a `ℚ`-line `ℓ` meeting `Λ` the `ℤ`-module `ℓ ∩ Λ` is free
  of rank one (`exists_primitive_of_line`, from the freeness of submodules of a finitely generated
  free `ℤ`-module), so `ℓ ∩ Λ = ℤ v_ℓ` with `v_ℓ` unique up to sign
  (`eq_or_eq_neg_of_span_singleton_eq`); an isometry `e` with `e(Λ) = Λ` carries `ℓ ∩ Λ` onto
  `e(ℓ) ∩ Λ` (`map_inf_restrictScalars`), so `e(v_ℓ) = ±v_{e(ℓ)}` and `q(v_{e(ℓ)}) = q(v_ℓ)`
  (`form_eq_of_primitive_map`); hence `H` has no more norm values than `H₀` has members
  (`finite_form_values_of_orbitFamily`). No coordinates and no gcd: the generator is the basis
  vector of a free module of rank one.

  The statement, with `H` as it is, is `cutsFinitelyOnRational_orbitFamily` in the last section:

  ```
  theorem cutsFinitelyOnRational_orbitFamily ... (Γ : Set (V ≃ₗ[ℚ] V))
      (H₀ : Finset (Submodule ℚ V))
      (hΓΛ : ∀ e ∈ Γ, Λ.map (e : V →ₗ[ℚ] V) = Λ)
      (hΓiso : ∀ e ∈ Γ, ∀ x y, BQ (e x) (e y) = BQ x y)
      (hH₀ : ∀ ℓ₀ ∈ H₀, ∃ v ≠ 0, Λ ⊓ ℓ₀.restrictScalars ℤ = ℤ ∙ v) :
      CutsFinitelyOnRational Cplus (fun ℓ : orbitFamily H₀ Γ => normalForm Q (g ℓ))
  ```

  where `Λ` is the `ℤ`-span of a `ℚ`-basis `bs` and `g ℓ` is the primitive generator of `ℓ ⊓ Λ`
  (`exists_generator_of_orbitFamily`; the general form of the theorem,
  `cutsFinitelyOnRational_of_finiteOrbits`, takes `g` as a parameter). Its first step is
  `finite_form_values_of_orbitFamily` (the norm values are a finite set `M`); the per-value
  finiteness is `finite_pairSet_of_cutSigns` over the finitely many ordered pairs of generators of
  the cone, that is `finite_cutters_of_pair_bounds` with the three cases of the counting lemma
  discharged; the values that are not negative contribute nothing
  (`one_signed_of_nonneg_quadratic`); and the transport of "the line `ℓ` cuts the rational cone" to
  "the form `x ↦ v_ℓ · x` cuts it" is `hyperplaneCuts_iff_cutsOn` together with
  `hyperplaneCuts_iff_generators`, which is what `cutsOn_iff_generators` decides on the cone's
  rational generators. The exclusion of an isotropic normal for a hyperplane meeting `C` is not part
  of it: `neg_quadratic_of_associated_eq_zero` gives `Q ℓ < 0` for the normal of such a hyperplane,
  from `sigPos Q = 1` and nondegeneracy alone.
* **The `[Fintype ι] [DecidableEq ι]` binders of the four lattice lemmas, kept deliberately.**
  `linter.unusedFintypeInType` reports them for `finite_span_int_of_pairings_bounded`,
  `finite_cutting_of_pairing_bounds`, `finite_cutting_normals_of_both_timelike` and
  `finite_cutting_normals_of_isotropic`, because their types mention the basis but not its index
  type. They are not removable: the conclusion is *false* for an infinite index type (the box of
  integer coordinates is finite exactly when the index set is), so finiteness of `ι` is a
  hypothesis of the theorem and not an artefact of the presentation. Dropping them and deriving
  `Fintype ι` inside the proof from `Module.Finite.finite_basis` does work, but the `letI` that
  requires is rejected by `linter.style.haveILetI`, which fires on any local instance in a proof of
  a proposition (it fires on `haveI : Fintype (Fin 3) := inferInstance`); the two linters' remedies
  are incompatible here, and the substantive reading — a hypothesis of the theorem — decides it. The
  binders stay, the warnings with them.
* The negative definiteness of the complement of the pair's plane, which the projection onto
  `ℝ (a + b)` above makes unnecessary, has a port target should it be wanted: TauCeti
  `LowDimTopology/Plumbing/NegativeDefinite.lean`,
  `IsNegativeDefinite.finite_setOfPred_le_intersectionForm_self` (a `ℤ`-sublevel set of a negative
  definite integral form is finite, by the injectivity of its Gram matrix); not ported, because the
  route through `associated_spatialPart_sq_le` discharges the same step in this repository.

### LC-09 record for the counting lemma (2026-11-15, #161, fifth unit)

The five queries of this unit, with every hit. `content:ZLattice finite`: 319 files, 8617 matches,
the import lists and the `ZLattice` developments recorded above; nothing new. `content:Finite inter
ZSpan`: 18 files, 1341 matches, 1 returned — atlas-lean
`v1/Atlas/NumberTheoryI/code/Adeles.lean` (finite residue fields), unrelated. `content:PointedCone
hull`: 8 files, 301 matches, 1 returned — TauCeti `Geometry/Convex/Cone/Basis.lean`
(`mem_pointedCone_hull_range_iff`: a vector is in the cone on a basis iff all its coordinates are
nonnegative), the cone-side counterpart of `forall_nonneg_of_forall_nonneg_generators`, not needed
here (this file's cone carries its rational generators, and `cutsOn_iff_generators` decides the
signs on those). `content:integral pairing denominator bounded`: 44 files, 4043 matches, no file
returned. `content:lattice points bounded pairings finite`: 10 files, 1162 matches, 1 returned —
TauCeti `LowDimTopology/Plumbing/NegativeDefinite.lean`, the port target named above; nothing
ported. What the lemmas here use is Mathlib's `abs_add_le`, `Real.sqrt_sq_eq_abs`,
`Real.sqrt_le_sqrt` and `LinearMap.BilinForm.dualBasis` / `dualBasis_repr_apply`, none re-derived.

-/

section CountingLemma

/-- **A nonzero integral pairing is at least `1/D`.** If `ℓ` and `D • v` are lattice vectors of a
form integral on the lattice, `ℓ · v = n/D` for an integer `n ≠ 0`, so `|ℓ · v| ≥ 1/D`. This is the
"bounded denominator" of the isotropic case of the counting lemma: the one quantity that the
estimate `abs_associated_le_of_isotropic` leaves free, and the reason the counting lemma is about a
lattice and not about `L(ℝ)`. -/
theorem one_div_le_abs_of_integral {BQ : LinearMap.BilinForm ℚ V}
    {Λ : Submodule ℤ V} {D : ℕ} (hD : 0 < D) {u w : V}
    (hu : u ∈ Λ) (hw : (D : ℤ) • w ∈ Λ)
    (hint : ∀ x ∈ Λ, ∀ y ∈ Λ, ∃ n : ℤ, BQ x y = (n : ℚ))
    (hne : BQ u w ≠ 0) : (1 : ℚ) / D ≤ |BQ u w| := by
  obtain ⟨n, hn⟩ := hint u hu ((D : ℤ) • w) hw
  have h1 : BQ u ((D : ℤ) • w) = (D : ℚ) * BQ u w := by
    rw [map_zsmul, zsmul_eq_mul]
    push_cast
    ring
  rw [h1] at hn
  have hn0 : n ≠ 0 := by
    rintro rfl
    simp only [Int.cast_zero] at hn
    have hDq : (D : ℚ) ≠ 0 := by exact_mod_cast hD.ne'
    exact hne (by
      rcases mul_eq_zero.1 hn with h | h
      · exact absurd h hDq
      · exact h)
  have habs : (1 : ℚ) ≤ |(n : ℚ)| := by
    have h2 : (1 : ℤ) ≤ |n| := Int.one_le_abs hn0
    exact_mod_cast h2
  have hkey : |(n : ℚ)| = (D : ℚ) * |BQ u w| := by
    rw [← hn, abs_mul]
    have : |(D : ℚ)| = (D : ℚ) := abs_of_nonneg (by positivity)
    rw [this]
  rw [hkey] at habs
  rw [div_le_iff₀ (by exact_mod_cast hD), mul_comm]
  exact habs

variable [Module.Finite ℚ V] {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem abs_associated_le_of_pairing_bound {Q : QuadraticForm ℝ (realified V)}
    (hpos : sigPos Q = 1) {t l z : realified V} (ht : 0 < Q t) {L m : ℝ}
    (hL : |(associated Q) l t| ≤ L) (hQl : Q l = -m) :
    |(associated Q) l z| ≤ Real.sqrt ((m + L ^ 2 / Q t) * (-(Q (spatialPart Q t z)))) +
      L / Q t * |(associated Q) t z| := by
  set c : ℝ := (associated Q) l t / Q t with hc
  have htne : Q t ≠ 0 := ht.ne'
  have hl : l = c • t + spatialPart Q t l := by
    rw [hc, spatialPart]
    module
  have hwt : (associated Q) (spatialPart Q t l) t = 0 := associated_spatialPart_right Q htne l
  have hwz : (associated Q) (spatialPart Q t l) z
      = (associated Q) (spatialPart Q t l) (spatialPart Q t z) := by
    have hzsplit : z = ((associated Q) z t / Q t) • t + spatialPart Q t z := by
      rw [spatialPart]
      module
    conv_lhs => rw [hzsplit]
    simp only [map_add, map_smul, smul_eq_mul, hwt, mul_zero, zero_add]
  have hsplit : (associated Q) l z
      = c * ((associated Q) t z) + (associated Q) (spatialPart Q t l) (spatialPart Q t z) := by
    conv_lhs => rw [hl]
    rw [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, hwz]
  have hcs := associated_spatialPart_sq_le (Q := Q) hpos ht l z
  have hQw : Q (spatialPart Q t l) = -m - (associated Q) l t ^ 2 / Q t := by
    rw [quadratic_spatialPart Q htne l, hQl]
  have hsqt : (associated Q) l t ^ 2 ≤ L ^ 2 := by
    nlinarith [abs_le.mp hL, abs_nonneg ((associated Q) l t)]
  have hb : -(Q (spatialPart Q t l)) ≤ m + L ^ 2 / Q t := by
    rw [hQw]
    have : 0 < Q t := ht
    field_simp
    nlinarith [hsqt, ht]
  have hb2 : 0 ≤ -(Q (spatialPart Q t z)) := by
    have := quadratic_spatialPart_nonpos (Q := Q) hpos ht z
    linarith
  have hcs' : (associated Q) (spatialPart Q t l) (spatialPart Q t z) ^ 2
      ≤ (m + L ^ 2 / Q t) * (-(Q (spatialPart Q t z))) := by
    have h1 : -(Q (spatialPart Q t l)) * (-(Q (spatialPart Q t z))) ≤
        (m + L ^ 2 / Q t) * (-(Q (spatialPart Q t z))) := by
      have h2 : 0 ≤ -(Q (spatialPart Q t z)) := hb2
      have h3 : -(Q (spatialPart Q t l)) ≤ m + L ^ 2 / Q t := hb
      nlinarith [h2, h3]
    linarith [hcs, h1]
  have hwbound : |(associated Q) (spatialPart Q t l) (spatialPart Q t z)|
      ≤ Real.sqrt ((m + L ^ 2 / Q t) * (-(Q (spatialPart Q t z)))) := by
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt hcs'
  have hcbound : |c| ≤ L / Q t := by
    rw [hc, abs_div, abs_of_pos ht]
    exact div_le_div_of_nonneg_right hL ht.le
  rw [hsplit]
  have ht1 : |c * ((associated Q) t z)| ≤ L / Q t * |(associated Q) t z| := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right hcbound (abs_nonneg _)
  calc |c * ((associated Q) t z) + (associated Q) (spatialPart Q t l) (spatialPart Q t z)|
      ≤ |c * ((associated Q) t z)| +
        |(associated Q) (spatialPart Q t l) (spatialPart Q t z)| := abs_add_le _ _
    _ ≤ L / Q t * |(associated Q) t z| +
        Real.sqrt ((m + L ^ 2 / Q t) * (-(Q (spatialPart Q t z)))) := by
        have := hwbound
        linarith [ht1]
    _ = _ := by ring

/-- **Bounded pairings leave finitely many lattice vectors.** The bounds on the pairings of `ℓ` with
the pair (`hbnd`) bound, through `abs_associated_le_of_pairing_bound` at `t = a + b`, the pairing of
`ℓ` with every vector, in particular with each vector of Mathlib's dual basis `BQ.dualBasis`; the
pairings with that family are the coordinates of `ℓ` against the `ℤ`-span of the basis, where
`finite_span_int_of_pairings_bounded` leaves finitely many vectors. -/
theorem finite_cutting_of_pairing_bounds {ι : Type*} [Fintype ι] [DecidableEq ι]
    {bs : Module.Basis ι ℚ V} {Q : QuadraticForm ℝ (realified V)} (hpos : sigPos Q = 1)
    {BQ : LinearMap.BilinForm ℚ V} (hBQsym : BQ.IsSymm) (hBQnd : BQ.Nondegenerate)
    (hBQ : ∀ u w : V, (associated Q) (rationalPoint u) (rationalPoint w) = (BQ u w : ℝ))
    {a b : V} {m : ℝ} (ht : 0 < Q (rationalPoint a + rationalPoint b)) {Cx Cy : ℝ}
    (hbnd : ∀ v : V, v ∈ Submodule.span ℤ (Set.range bs) → Q (rationalPoint v) = -m →
      0 < (BQ v a : ℝ) → (BQ v b : ℝ) < 0 →
      |(BQ v a : ℝ)| ≤ Cx ∧ |(BQ v b : ℝ)| ≤ Cy) :
    {v : V | v ∈ Submodule.span ℤ (Set.range bs) ∧ Q (rationalPoint v) = -m ∧
      0 < (BQ v a : ℝ) ∧ (BQ v b : ℝ) < 0}.Finite := by
  classical
  have key : ∀ k : ι, ∃ C : ℕ, ∀ v : V, v ∈ Submodule.span ℤ (Set.range bs) →
      Q (rationalPoint v) = -m → 0 < (BQ v a : ℝ) → (BQ v b : ℝ) < 0 →
      |BQ v (BQ.dualBasis hBQnd bs k)| ≤ (C : ℚ) := by
    intro k
    obtain ⟨C, hC⟩ := exists_nat_ge (Real.sqrt
      ((m + (Cx + Cy) ^ 2 / Q (rationalPoint a + rationalPoint b)) *
        (-(Q (spatialPart Q (rationalPoint a + rationalPoint b)
          (rationalPoint (BQ.dualBasis hBQnd bs k)))))) +
      (Cx + Cy) / Q (rationalPoint a + rationalPoint b) *
        |(associated Q) (rationalPoint a + rationalPoint b)
          (rationalPoint (BQ.dualBasis hBQnd bs k))|)
    refine ⟨C, fun v hv hQ hx hy => ?_⟩
    obtain ⟨h1, h2⟩ := hbnd v hv hQ hx hy
    have hsum : (associated Q) (rationalPoint v) (rationalPoint a + rationalPoint b)
        = (BQ v a : ℝ) + (BQ v b : ℝ) := by
      simp only [map_add, hBQ v a, hBQ v b]
    have hL : |(associated Q) (rationalPoint v) (rationalPoint a + rationalPoint b)| ≤ Cx + Cy := by
      rw [hsum]
      refine le_trans (abs_add_le _ _) ?_
      linarith
    have hgt := abs_associated_le_of_pairing_bound (Q := Q) hpos ht (l := rationalPoint v)
      (z := rationalPoint (BQ.dualBasis hBQnd bs k)) (L := Cx + Cy) (m := m) hL hQ
    have hreal : |((BQ v (BQ.dualBasis hBQnd bs k) : ℚ) : ℝ)| ≤ (C : ℝ) := by
      rw [← hBQ v (BQ.dualBasis hBQnd bs k)]
      exact le_trans hgt hC
    exact_mod_cast hreal
  choose C hC using key
  refine Set.Finite.subset (finite_span_int_of_pairings_bounded (b := bs) hBQnd hBQsym C) ?_
  rintro v ⟨hv, hQ, hx, hy⟩
  exact ⟨hv, fun k => hC k v hv hQ hx hy⟩

/-- **The counting lemma at a pair of timelike generators**: the bounds
`abs_associated_le_of_both_timelike` turn the sign conditions on the pair into the bounded pairings
of `finite_cutting_of_pairing_bounds`. Both constants are explicit — the Gram data of the pair and
`m`. -/
theorem finite_cutting_normals_of_both_timelike {ι : Type*} [Fintype ι] [DecidableEq ι]
    {bs : Module.Basis ι ℚ V} {Q : QuadraticForm ℝ (realified V)} (hpos : sigPos Q = 1)
    {BQ : LinearMap.BilinForm ℚ V} (hBQsym : BQ.IsSymm) (hBQnd : BQ.Nondegenerate)
    (hBQ : ∀ u w : V, (associated Q) (rationalPoint u) (rationalPoint w) = (BQ u w : ℝ))
    {a b : V} {m : ℝ}
    (ha : 0 < Q (rationalPoint a)) (hb : 0 < Q (rationalPoint b))
    (hab : 0 < (associated Q) (rationalPoint a) (rationalPoint b))
    (hK : 0 < (associated Q) (rationalPoint a) (rationalPoint b) ^ 2 -
      Q (rationalPoint a) * Q (rationalPoint b)) :
    {v : V | v ∈ Submodule.span ℤ (Set.range bs) ∧ Q (rationalPoint v) = -m ∧
      0 < (BQ v a : ℝ) ∧ (BQ v b : ℝ) < 0}.Finite := by
  have ht : 0 < Q (rationalPoint a + rationalPoint b) := by
    rw [show rationalPoint a + rationalPoint b
        = (1 : ℝ) • rationalPoint a + (1 : ℝ) • rationalPoint b by simp, quadratic_expand]
    nlinarith [ha, hb, hab]
  set K := (associated Q) (rationalPoint a) (rationalPoint b) ^ 2 -
    Q (rationalPoint a) * Q (rationalPoint b) with hKdef
  have hKpos : 0 < K := hKdef ▸ hK
  refine finite_cutting_of_pairing_bounds (Q := Q) hpos hBQsym hBQnd hBQ (a := a) (b := b) ht
    (Cx := Real.sqrt (m * K / Q (rationalPoint b)))
    (Cy := Real.sqrt (m * K / Q (rationalPoint a))) ?_
  intro v hv hQ hx hy
  have hx' : 0 < (associated Q) (rationalPoint v) (rationalPoint a) := by
    rw [hBQ v a]; exact hx
  have hy' : (associated Q) (rationalPoint v) (rationalPoint b) < 0 := by
    rw [hBQ v b]; exact hy
  have h := abs_associated_le_of_both_timelike (Q := Q) hpos ha hb hab hKpos hQ hx' hy'
  constructor
  · rw [← hBQ v a]
    exact h.1
  · rw [← hBQ v b]
    exact h.2

/-- **The counting lemma at a timelike and an isotropic generator**: the hyperbola of
`abs_associated_le_of_isotropic` bounds `ℓ · b` and the product of the two pairings, and the
denominator of `b` in the lattice (`one_div_le_abs_of_integral`) turns the product bound into a
bound on `ℓ · a`. -/
theorem finite_cutting_normals_of_isotropic {ι : Type*} [Fintype ι] [DecidableEq ι]
    {bs : Module.Basis ι ℚ V} {Q : QuadraticForm ℝ (realified V)} (hpos : sigPos Q = 1)
    {BQ : LinearMap.BilinForm ℚ V} (hBQsym : BQ.IsSymm) (hBQnd : BQ.Nondegenerate)
    (hBQ : ∀ u w : V, (associated Q) (rationalPoint u) (rationalPoint w) = (BQ u w : ℝ))
    {a b : V} {m : ℝ} (hm : 0 < m) (ha : 0 < Q (rationalPoint a)) (hb : Q (rationalPoint b) = 0)
    (hab : 0 < (associated Q) (rationalPoint a) (rationalPoint b))
    {D : ℕ} (hD : 0 < D)
    (hbD : (D : ℤ) • b ∈ Submodule.span ℤ (Set.range bs))
    (hint : ∀ x ∈ Submodule.span ℤ (Set.range bs), ∀ y ∈ Submodule.span ℤ (Set.range bs),
      ∃ n : ℤ, BQ x y = (n : ℚ)) :
    {v : V | v ∈ Submodule.span ℤ (Set.range bs) ∧ Q (rationalPoint v) = -m ∧
      0 < (BQ v a : ℝ) ∧ (BQ v b : ℝ) < 0}.Finite := by
  have ht : 0 < Q (rationalPoint a + rationalPoint b) := by
    rw [show rationalPoint a + rationalPoint b
        = (1 : ℝ) • rationalPoint a + (1 : ℝ) • rationalPoint b by simp, quadratic_expand, hb]
    nlinarith [ha, hab]
  refine finite_cutting_of_pairing_bounds (Q := Q) hpos hBQsym hBQnd hBQ (a := a) (b := b) ht
    (Cx := m * (associated Q) (rationalPoint a) (rationalPoint b) / 2 * D)
    (Cy := (associated Q) (rationalPoint a) (rationalPoint b) *
      Real.sqrt (m / Q (rationalPoint a))) ?_
  intro v hv hQ hx hy
  have hx' : 0 < (associated Q) (rationalPoint v) (rationalPoint a) := by
    rw [hBQ v a]; exact hx
  have hy' : (associated Q) (rationalPoint v) (rationalPoint b) < 0 := by
    rw [hBQ v b]; exact hy
  have h := abs_associated_le_of_isotropic (Q := Q) hpos ha hb hab hQ hx' hy'
  have hne : BQ v b ≠ 0 := by
    intro h0
    rw [h0] at hy
    simp at hy
  have hdenq := one_div_le_abs_of_integral (BQ := BQ)
    (Λ := Submodule.span ℤ (Set.range bs)) (D := D) hD (u := v) (w := b) hv hbD hint hne
  have hden : (1 : ℝ) / (D : ℝ) ≤ |(BQ v b : ℝ)| := by
    have h2 : ((1 : ℚ) / (D : ℚ) : ℝ) ≤ ((|BQ v b| : ℚ) : ℝ) := by exact_mod_cast hdenq
    simpa using h2
  have hxy : |(BQ v a : ℝ)| * |(BQ v b : ℝ)| ≤
      m * (associated Q) (rationalPoint a) (rationalPoint b) / 2 := by
    rw [← hBQ v a, ← hBQ v b]
    exact h.2
  have hC : 0 ≤ m * (associated Q) (rationalPoint a) (rationalPoint b) / 2 := by
    nlinarith [hab, hm]
  constructor
  · have hb1 : |(BQ v a : ℝ)| ≤
        m * (associated Q) (rationalPoint a) (rationalPoint b) / 2 * (D : ℝ) :=
      abs_le_of_abs_mul_le_of_one_div_le (x := (BQ v a : ℝ)) (y := (BQ v b : ℝ)) hC
        (by exact_mod_cast hD) hden hxy
    exact hb1
  · rw [← hBQ v b]
    exact h.1

/-- **The counting lemma at a pair of isotropic generators**: with `Q a = Q b = 0` the relation of
`pairing_quadratic_bound` bounds only the product of the two pairings, so both are bounded away
from `0` by integrality — the denominators `Da`, `Db` of the two generators — and
`abs_le_of_abs_mul_le_of_one_div_le` turns the product bound into a bound on each. -/
theorem finite_cutting_normals_of_both_isotropic {ι : Type*} [Fintype ι] [DecidableEq ι]
    {bs : Module.Basis ι ℚ V} {Q : QuadraticForm ℝ (realified V)} (hpos : sigPos Q = 1)
    {BQ : LinearMap.BilinForm ℚ V} (hBQsym : BQ.IsSymm) (hBQnd : BQ.Nondegenerate)
    (hBQ : ∀ u w : V, (associated Q) (rationalPoint u) (rationalPoint w) = (BQ u w : ℝ))
    {a b : V} {m : ℝ} (hm : 0 < m) (ha : Q (rationalPoint a) = 0) (hb : Q (rationalPoint b) = 0)
    (hab : 0 < (associated Q) (rationalPoint a) (rationalPoint b))
    {Da Db : ℕ} (hDa : 0 < Da) (hDb : 0 < Db)
    (haDa : (Da : ℤ) • a ∈ Submodule.span ℤ (Set.range bs))
    (hbDb : (Db : ℤ) • b ∈ Submodule.span ℤ (Set.range bs))
    (hint : ∀ x ∈ Submodule.span ℤ (Set.range bs), ∀ y ∈ Submodule.span ℤ (Set.range bs),
      ∃ n : ℤ, BQ x y = (n : ℚ)) :
    {v : V | v ∈ Submodule.span ℤ (Set.range bs) ∧ Q (rationalPoint v) = -m ∧
      0 < (BQ v a : ℝ) ∧ (BQ v b : ℝ) < 0}.Finite := by
  have ht : 0 < Q (rationalPoint a + rationalPoint b) := by
    rw [show rationalPoint a + rationalPoint b
        = (1 : ℝ) • rationalPoint a + (1 : ℝ) • rationalPoint b by simp, quadratic_expand,
      ha, hb]
    linarith
  refine finite_cutting_of_pairing_bounds (Q := Q) hpos hBQsym hBQnd hBQ (a := a) (b := b) ht
    (Cx := m * (associated Q) (rationalPoint a) (rationalPoint b) / 2 * (Db : ℝ))
    (Cy := m * (associated Q) (rationalPoint a) (rationalPoint b) / 2 * (Da : ℝ)) ?_
  intro v hv hQ hx hy
  have hx' : 0 < (associated Q) (rationalPoint v) (rationalPoint a) := by
    rw [hBQ v a]; exact hx
  have hy' : (associated Q) (rationalPoint v) (rationalPoint b) < 0 := by
    rw [hBQ v b]; exact hy
  have h := abs_associated_mul_le_of_both_isotropic (Q := Q) hpos ha hb hab hQ hx' hy'
  have hxy : |(BQ v a : ℝ)| * |(BQ v b : ℝ)| ≤
      m * (associated Q) (rationalPoint a) (rationalPoint b) / 2 := by
    rw [← hBQ v a, ← hBQ v b]
    exact h
  have hC : 0 ≤ m * (associated Q) (rationalPoint a) (rationalPoint b) / 2 := by
    nlinarith [hab, hm]
  have hne_a : BQ v a ≠ 0 := by
    intro h0
    rw [h0] at hx
    simp at hx
  have hne_b : BQ v b ≠ 0 := by
    intro h0
    rw [h0] at hy
    simp at hy
  have hdena := one_div_le_abs_of_integral (BQ := BQ)
    (Λ := Submodule.span ℤ (Set.range bs)) (D := Da) hDa (u := v) (w := a) hv haDa hint hne_a
  have hdenb := one_div_le_abs_of_integral (BQ := BQ)
    (Λ := Submodule.span ℤ (Set.range bs)) (D := Db) hDb (u := v) (w := b) hv hbDb hint hne_b
  have hdena' : (1 : ℝ) / (Da : ℝ) ≤ |(BQ v a : ℝ)| := by
    have h2 : ((1 : ℚ) / (Da : ℚ) : ℝ) ≤ ((|BQ v a| : ℚ) : ℝ) := by exact_mod_cast hdena
    simpa using h2
  have hdenb' : (1 : ℝ) / (Db : ℝ) ≤ |(BQ v b : ℝ)| := by
    have h2 : ((1 : ℚ) / (Db : ℚ) : ℝ) ≤ ((|BQ v b| : ℚ) : ℝ) := by exact_mod_cast hdenb
    simpa using h2
  constructor
  · exact abs_le_of_abs_mul_le_of_one_div_le (x := (BQ v a : ℝ)) (y := (BQ v b : ℝ)) hC
      (by exact_mod_cast hDb) hdenb' hxy
  · refine abs_le_of_abs_mul_le_of_one_div_le (x := (BQ v b : ℝ)) (y := (BQ v a : ℝ)) hC
      (by exact_mod_cast hDa) hdena' ?_
    rw [mul_comm]
    exact hxy

end CountingLemma

/-- **Finitely many cutting normals.** The two sign conditions on a pair of generators, taken over
the finitely many ordered pairs of a finite family `s`, is the cutting condition
(`cutsOn_iff_generators`), so finiteness for each pair is finiteness for the cutters. -/
theorem finite_cutters_of_pair_bounds {Q : QuadraticForm ℝ (realified V)}
    {BQ : LinearMap.BilinForm ℚ V} {m : ℝ} (Λs : Submodule ℤ V) (s : Finset V)
    (hpair : ∀ a ∈ s, ∀ b ∈ s,
      {v : V | v ∈ Λs ∧ Q (rationalPoint v) = -m ∧ 0 < (BQ v a : ℝ) ∧ (BQ v b : ℝ) < 0}.Finite) :
    {v : V | v ∈ Λs ∧ Q (rationalPoint v) = -m ∧
      ∃ a ∈ s, ∃ b ∈ s, 0 < (BQ v a : ℝ) ∧ (BQ v b : ℝ) < 0}.Finite := by
  have hunion : (⋃ a ∈ (s : Set V), ⋃ b ∈ (s : Set V),
      {v : V | v ∈ Λs ∧ Q (rationalPoint v) = -m ∧
        0 < (BQ v a : ℝ) ∧ (BQ v b : ℝ) < 0}).Finite :=
    Set.Finite.biUnion s.finite_toSet (fun a _ =>
      Set.Finite.biUnion s.finite_toSet (fun b _ => hpair a ‹a ∈ s› b ‹b ∈ s›))
  refine hunion.subset ?_
  rintro v ⟨hv, hQ, a, ha, b, hb, hxa, hxb⟩
  exact Set.mem_iUnion₂.mpr ⟨a, ha, Set.mem_iUnion₂.mpr ⟨b, hb, hv, hQ, hxa, hxb⟩⟩

end CountingOverRat

/-! ## The lattice and orbit layer: finitely many norms on a finite union of `Γ`-orbits

The hypothesis of Example 4.3 (b), p. 18, for the arithmetic `H` (`CutsFinitelyOnRational` below the
arrangement section), in the form the source gives it: `H` is a *finite union of `Γ`-orbits* of
`ℚ`-hyperplanes (`orbitFamily`), not a finite family — a finite family cuts every cone finitely,
for a trivial reason, and says nothing about the issue.

The mathematical content of the layer, and the step at which the last turn stopped, is that the
normals of `H` take **finitely many values** on the lattice. Not by coordinates: for a `ℚ`-line `ℓ`
meeting the lattice `Λ`, the `ℤ`-module `ℓ ∩ Λ` is a submodule of the finitely generated free
`ℤ`-module `Λ`, hence free (`Module.basisOfFiniteTypeTorsionFree'`,
`Mathlib/LinearAlgebra/FreeModule/PID.lean:387`), and it is free of rank one because its elements
are `ℚ`-multiples of one another — a `ℤ`-basis cannot contain two `ℚ`-collinear vectors. So
`ℓ ∩ Λ = ℤ v_ℓ` for a generator unique up to sign (`eq_or_eq_neg_of_span_singleton_eq`). An isometry
`e ∈ Γ` with `e(Λ) = Λ` carries `ℓ ∩ Λ` onto `e(ℓ) ∩ Λ` (`map_inf_restrictScalars`), so
`e(v_ℓ) = ± v_{e(ℓ)}` and the norm of the generator is constant on the orbit
(`form_eq_of_primitive_map`). Hence `H` has as many norms as `H₀` has members
(`finite_form_values_of_orbitFamily`).

### LC-09 record for the orbit layer (2026-11-15, #161, sixth unit)

The four queries this unit names, with every hit, plus the two formulations added.
`content:Submodule.IsPrincipal`: 77 files, 200 matches, 3 returned — atlas-lean `Ideals.lean`
(`Submodule.IsPrincipal` of an ideal), CBirkbeck/AINTLIB `SmallNumbers/PID.lean` and
`CaseII/AuxLemmas.lean` (principal ideals in rings of integers); ideals, not submodules of a
lattice, so not the statement needed. `content:free_of_finite_type_torsion_free`: 34 files, 42
matches, 3 returned — atlas-lean `NumberTheoryI/code/Cor2344.lean` and
`MathlibExt/Algebra/Module/QuillenSuslin.lean`, Vilin97/lean-pool `BruhatTits/Lattice/Basic.lean`,
all of them the same use of Mathlib's `Module.free_of_finite_type_torsion_free'` on a submodule
`M ⊓ N` of a lattice; that is the recipe ported here (Mathlib's lemma, called, not re-derived).
`content:Module.Free submodule PID`: 73 files, 1845 matches, no file returned.
`content:finrank_eq_one_iff`: 148 files, 184 matches, none returned. `content:subgroup Rat cyclic
finitely generated`: 26 files, 2893 matches, none returned — the subgroup-of-`ℚ` route to the
generator is not formalized anywhere in the corpus. `content:lattice line primitive vector
generator`: 85 files, 7662 matches, none returned. Follow-up `file:BruhatTits/Lattice content:inf`:
chrisflav/bruhat-tits and Vilin97 `BruhatTits/Lattice/Basic.lean`, the nearest neighbour — they
prove that an intersection of two lattices is a lattice (`IsLattice.isFG`, `Submodule.rank_sup_add_
rank_inf_eq`) and get freeness of `M ⊓ N` from `Module.free_of_finite_type_torsion_free'`, but not
that a line's intersection with a lattice is cyclic. Nothing to port beyond that recipe; the
primitive-vector statement is residue and is proved here (`exists_primitive_of_line`), with the
rank-one step taken from the `ℚ`-collinearity of two elements of the line rather than from a
`finrank` computation.

### LC-09 record for the cut identification (2026-11-16, #161, seventh unit)

The five queries of this unit, with every hit. `content:orthogonal complement bilinear form
submodule`: 3 files returned — facebookresearch/atlas-lean `CSLibExt/Coding/LinearCode.lean`
(`dual_dual`, from `LinearMap.BilinForm.orthogonal_orthogonal`), atlas-lean
`MathlibExt/Algebra/Lie/LeviDecomposition.lean` and TauCeti `Geometry/Hodge/Orthogonal.lean`, all of
them *using* the orthogonal complement of a bilinear form. Mathlib owns the statement, at
`LinearMap.BilinForm.orthogonal` / `mem_orthogonal_iff`
(`Mathlib/LinearAlgebra/BilinearForm/Orthogonal.lean:145`, `:150`), and nothing is ported: the
kernel identity of `hyperplaneOf_span_singleton` is proved from `mem_orthogonal_iff` rather than
from Mathlib's `orthogonal_span_singleton_eq_toLin_ker` (`:175`), whose statement goes through
`toLinHomAux₁`. `LinearMap.BilinForm.orthogonal` (the Mathlib-style identifier): the same three
files. `content:isotropic vectors orthogonal proportional`: 3 files, 120 matches, one returned —
TauCeti `LinearAlgebra/CliffordAlgebra/Vectors.lean`, unrelated — so the proportionality of two
sheet vectors with vanishing pairing (`exists_smul_of_associated_eq_zero_of_mem_closedSheet`) is
residue. `content:opposite sides hyperplane segment`: 7 files, 1560 matches, one returned —
Vilin97/lean-pool `ClassificationOfSurfaces/Moise/LineSubdivision.lean`, whose affine functional
changing sign at the ends of an edge is the planar analogue of the same picture; no statement about
a cone cut by the two sides of a hyperplane, so `OppositeSides` and `HyperplaneCuts` are written
here. `content:lattice points fixed norm quadratic form finite`: 31 files, one returned —
CBirkbeck/LeanBridge `ShimuraCurve/EllipticPointStabilizer.lean`, unrelated; the finiteness used is
this file's `finite_cutting_of_pairing_bounds`. The one Mathlib ingredient the unit needed is
`IsModuleTopology.continuous_of_linearMap`
(`Mathlib/Topology/Algebra/Module/ModuleTopology.lean:340`) for `normalForm` — every linear form on
the module topology is continuous, so no continuity hypothesis enters the theorem. That is not in
tension with the `hcl` hypothesis of `salient_rationalClosure`: that one asks for the continuity of
the *quadratic* form `Q`, which Mathlib does not have, while a linear form is continuous by that
lemma.

The exclusion of an isotropic normal for a hyperplane meeting `C` is on main and is not repeated:
`neg_quadratic_of_associated_eq_zero` (below, the hyperbolic section) gives `Q ℓ < 0` for the normal
of a hyperplane meeting `C`, from `sigPos Q = 1` and nondegeneracy alone.

### What is carried, and what is not

The counting lemma for this `H` is `cutsFinitelyOnRational_orbitFamily` in the next section: per
value of the norm the cutters are finite (`finite_pairSet_of_cutSigns`, over the ordered pairs of
rational generators of the cone), and `finite_form_values_of_orbitFamily` says there are finitely
many values; the lines of `H` are recovered from their generators
(`span_singleton_of_inf_span_eq`, `exists_generator_of_orbitFamily`), which makes the passage from
normals to hyperplanes injective.

Not carried: the arithmeticity of `Γ` (the finite-index subgroup of `O(L(ℚ))` preserving `Λ`), so
`Λ`, the integrality of the form on it and its `Γ`-stability are hypotheses; the reduction of a
general lattice to the `ℤ`-span of a `ℚ`-basis (recorded in the module docstring); and the passage
in the other direction — that `H` consists of hyperplanes *meeting* `C` is not used, since a normal
of nonnegative value does not cut a cone inside the sheet (`one_signed_of_nonneg_quadratic`).
-/

section OrbitLayer

variable {V : Type u} [AddCommGroup V] [Module ℚ V]

/-- A `ℚ`-vector space is torsion free over `ℤ`, so that a finitely generated `ℤ`-submodule of it is
free: the hypothesis of `Module.basisOfFiniteTypeTorsionFree'`, which is
`Module.IsTorsionFree.comap` along `ℤ → ℚ`. -/
instance instIsTorsionFreeIntOfRat : Module.IsTorsionFree ℤ V :=
  Module.IsTorsionFree.comap (Int.cast : ℤ → ℚ) (fun r hr => by
    rw [isRegular_iff_ne_zero] at hr ⊢
    exact Int.cast_ne_zero.mpr hr) (fun r m => by rw [Int.cast_smul_eq_zsmul])

/-- **A `ℚ`-line meeting a lattice is spanned over `ℤ` by one primitive lattice vector.** The
`ℤ`-module `ℓ ∩ Λ` is a submodule of the finitely generated free `ℤ`-module `Λ`, hence free
(`Module.basisOfFiniteTypeTorsionFree'`), and its basis has at most one vector: two basis vectors
would be `ℤ`-independent, while two elements of a `ℚ`-line are `ℚ`-collinear, and clearing the
denominator of the ratio turns collinearity into a nontrivial `ℤ`-relation. So `ℓ ∩ Λ = ℤ v`. -/
theorem exists_primitive_of_line (Λ : Submodule ℤ V) [Module.Finite ℤ ↥Λ]
    {ℓ : Submodule ℚ V} {v₀ : V} (hℓ : ℓ = Submodule.span ℚ {v₀})
    (hne : ∃ v : V, v ∈ Λ ⊓ ℓ.restrictScalars ℤ ∧ v ≠ 0) :
    ∃ v : V, v ∈ Λ ⊓ ℓ.restrictScalars ℤ ∧
      Λ ⊓ ℓ.restrictScalars ℤ = Submodule.span ℤ {v} := by
  classical
  set S : Submodule ℤ V := Λ ⊓ ℓ.restrictScalars ℤ with hS
  have hfin : Module.Finite ℤ ↥S :=
    Module.Finite.of_injective (Submodule.inclusion inf_le_left)
      (fun x y h => Subtype.ext (congrArg (Subtype.val : ↥Λ → V) h))
  obtain ⟨n, bN⟩ := @Module.basisOfFiniteTypeTorsionFree' ℤ _ ↥S _ _ _ _ hfin _
  have hnpos : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · exfalso
      obtain ⟨v, hv, hv0⟩ := hne
      subst h0
      have hz : (⟨v, hv⟩ : ↥S) = 0 := by
        rw [← bN.sum_repr (⟨v, hv⟩ : ↥S)]
        simp
      exact hv0 (congrArg Subtype.val hz)
    · exact hpos
  have hnle : n ≤ 1 := by
    by_contra hcon
    have hn2 : 2 ≤ n := by omega
    let i0 : Fin n := ⟨0, by omega⟩
    let i1 : Fin n := ⟨1, by omega⟩
    have h01 : i0 ≠ i1 := by
      intro h
      have h2 : (i0 : ℕ) = (i1 : ℕ) := congrArg Fin.val h
      simp only [i0, i1] at h2
      omega
    have hspan0 : ((bN i0 : ↥S) : V) ∈ Submodule.span ℚ {v₀} := by
      rw [← hℓ]; exact (bN i0).2.2
    have hspan1 : ((bN i1 : ↥S) : V) ∈ Submodule.span ℚ {v₀} := by
      rw [← hℓ]; exact (bN i1).2.2
    obtain ⟨c0, hc0⟩ := Submodule.mem_span_singleton.mp hspan0
    obtain ⟨c1, hc1⟩ := Submodule.mem_span_singleton.mp hspan1
    have hx0 : ((bN i0 : ↥S) : V) ≠ 0 := fun h => bN.ne_zero i0 (Subtype.ext h)
    have hc0ne : c0 ≠ 0 := by
      intro h
      exact hx0 (by rw [← hc0, h, zero_smul])
    set c : ℚ := c1 / c0 with hc
    have hratio : ((bN i1 : ↥S) : V) = c • ((bN i0 : ↥S) : V) := by
      rw [hc, ← hc0, ← hc1, smul_smul, div_mul_cancel₀ _ hc0ne]
    have hden : ((c.den : ℚ)) * c = (c.num : ℚ) := by
      rw [mul_comm, Rat.mul_den_eq_num]
    have hrel : (-(c.num) : ℤ) • (bN i0) + (c.den : ℤ) • (bN i1) = 0 := by
      apply Subtype.ext
      show ((-(c.num) : ℤ) • ((bN i0 : ↥S) : V) + (c.den : ℤ) • ((bN i1 : ↥S) : V) : V) = 0
      have hQ : (-(c.num) : ℚ) • ((bN i0 : ↥S) : V) + (c.den : ℚ) • ((bN i1 : ↥S) : V)
          = 0 := by
        rw [hratio, smul_smul, hden, neg_smul, neg_add_cancel]
      rw [← Int.cast_smul_eq_zsmul (R := ℚ), ← Int.cast_smul_eq_zsmul (R := ℚ)]
      push_cast
      exact hQ
    have hinj : Function.Injective (![i0, i1] : Fin 2 → Fin n) := by
      intro j k hjk
      fin_cases j <;> fin_cases k <;> simp_all
    have hpair : LinearIndependent ℤ ![bN i0, bN i1] := by
      have hfe : (![bN i0, bN i1] : Fin 2 → ↥S) = fun j => bN (![i0, i1] j) := by
        funext j
        fin_cases j <;> rfl
      rw [hfe]
      exact bN.linearIndependent.comp _ hinj
    obtain ⟨-, hd⟩ := LinearIndependent.pair_iff.mp hpair _ _ hrel
    have hdenne : (c.den : ℤ) ≠ 0 := by
      have := c.den_nz
      exact_mod_cast this
    exact hdenne hd
  have hn1 : n = 1 := by omega
  obtain rfl : n = 1 := hn1
  refine ⟨((bN 0 : ↥S) : V), (bN 0).2, ?_⟩
  refine le_antisymm ?_ ?_
  · intro z hz
    have hzsum : (⟨z, hz⟩ : ↥S) = ∑ i : Fin 1, bN.repr ⟨z, hz⟩ i • bN i :=
      (bN.sum_repr _).symm
    rw [Fin.sum_univ_one] at hzsum
    rw [Submodule.mem_span_singleton]
    refine ⟨bN.repr ⟨z, hz⟩ 0, ?_⟩
    have hval := congrArg (Subtype.val : ↥S → V) hzsum
    simpa using hval.symm
  · intro z hz
    rw [Submodule.mem_span_singleton] at hz
    obtain ⟨c, rfl⟩ := hz
    exact Submodule.smul_mem _ c (bN 0).2

/-- **An isometry of the lattice carries the line-lattice intersection along**: `e(ℓ ∩ Λ)` is
`e(ℓ) ∩ Λ` when `e(Λ) = Λ`. This is the identity behind the `Γ`-invariance of the norm of the
generator. -/
theorem map_inf_restrictScalars (Λ : Submodule ℤ V) {e : V ≃ₗ[ℚ] V}
    (hΛ : Submodule.map ((e : V →ₗ[ℚ] V).restrictScalars ℤ) Λ = Λ) (ℓ : Submodule ℚ V) :
    Submodule.map ((e : V →ₗ[ℚ] V).restrictScalars ℤ) (Λ ⊓ ℓ.restrictScalars ℤ)
      = Λ ⊓ (ℓ.map (e : V →ₗ[ℚ] V)).restrictScalars ℤ := by
  have hinj : Function.Injective ((e : V →ₗ[ℚ] V).restrictScalars ℤ) :=
    fun x y h => e.injective (by simpa using h)
  rw [Submodule.map_inf ((e : V →ₗ[ℚ] V).restrictScalars ℤ) hinj, hΛ,
    Submodule.restrictScalars_map]

/-- **A generator of a line-lattice intersection is unique up to sign**: two nonzero vectors
spanning the same `ℤ`-submodule of a torsion free module are `v` and `-v`. -/
theorem eq_or_eq_neg_of_span_singleton_eq {v w : V}
    (h : Submodule.span ℤ ({v} : Set V) = Submodule.span ℤ ({w} : Set V)) (hv : v ≠ 0) :
    w = v ∨ w = -v := by
  have hw : w ∈ Submodule.span ℤ ({v} : Set V) := by rw [h]; exact Submodule.subset_span rfl
  have hv' : v ∈ Submodule.span ℤ ({w} : Set V) := by rw [← h]; exact Submodule.subset_span rfl
  obtain ⟨b, hb⟩ := Submodule.mem_span_singleton.mp hv'
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hw
  have hba : (b * a) • v = v := by rw [mul_smul, ha, hb]
  have hzero : ((b * a - 1 : ℤ) : ℚ) • v = 0 := by
    rw [Int.cast_smul_eq_zsmul, sub_smul, hba, one_smul, sub_self]
  have hq : ((b * a - 1 : ℤ) : ℚ) = 0 := by
    rcases smul_eq_zero.mp hzero with h' | h'
    · exact h'
    · exact absurd h' hv
  have hba1 : b * a = 1 := by
    have h' : b * a - 1 = 0 := by exact_mod_cast hq
    omega
  rcases Int.eq_one_or_neg_one_of_mul_eq_one' hba1 with ⟨-, ha1⟩ | ⟨-, ha1⟩
  · left
    rw [← ha, ha1, one_smul]
  · right
    rw [← ha, ha1, neg_one_smul]

/-- **The norm of the primitive vector is constant on a `Γ`-orbit of hyperplanes** (Looijenga,
Example 4.3 (b), p. 18): an isometry `e` with `e(Λ) = Λ` carries `ℓ ∩ Λ = ℤ v` onto
`e(ℓ) ∩ Λ = ℤ (e v)`, whose generator is `e v` up to sign, and `q(e v) = q(v)`: so `q(w) = q(v)` for
a generator `w` of `e(ℓ) ∩ Λ`. This is the step that makes the normals of `H` take finitely many
values without any coordinates. -/
theorem form_eq_of_primitive_map (Λ : Submodule ℤ V) (BQ : LinearMap.BilinForm ℚ V)
    {e : V ≃ₗ[ℚ] V} (hΛ : Submodule.map ((e : V →ₗ[ℚ] V).restrictScalars ℤ) Λ = Λ)
    (he : ∀ x y, BQ (e x) (e y) = BQ x y)
    {ℓ : Submodule ℚ V} {v w : V}
    (hv : Λ ⊓ ℓ.restrictScalars ℤ = Submodule.span ℤ ({v} : Set V))
    (hw : Λ ⊓ (ℓ.map (e : V →ₗ[ℚ] V)).restrictScalars ℤ = Submodule.span ℤ ({w} : Set V))
    (hv0 : v ≠ 0) : BQ w w = BQ v v := by
  have hspanA : Submodule.map ((e : V →ₗ[ℚ] V).restrictScalars ℤ)
      (Submodule.span ℤ ({v} : Set V)) = Submodule.span ℤ ({e v} : Set V) := by
    rw [Submodule.map_span]
    simp
  have hspan : Submodule.span ℤ ({w} : Set V) = Submodule.span ℤ ({e v} : Set V) := by
    have h := map_inf_restrictScalars (Λ := Λ) (e := e) hΛ ℓ
    rw [hv, hw, hspanA] at h
    exact h.symm
  have hev0 : e v ≠ 0 := fun h => hv0 (e.injective (by rw [h]; exact (map_zero e).symm))
  have hw0 : w ≠ 0 := by
    intro h0
    have : e v ∈ Submodule.span ℤ ({w} : Set V) := by
      rw [hspan]; exact Submodule.subset_span rfl
    rw [h0, Submodule.mem_span_singleton] at this
    obtain ⟨c, hc⟩ := this
    rw [smul_zero] at hc
    exact hev0 hc.symm
  rcases eq_or_eq_neg_of_span_singleton_eq hspan.symm hev0 with h | h
  · rw [h, he]
  · rw [h]
    simp only [map_neg, LinearMap.neg_apply, neg_neg]
    exact he v v

/-- **The family of `ℚ`-hyperplanes generated by a finite family under a set `Γ` of isometries**:
Looijenga's `H` in Example 4.3 (b), p. 18, a finite union of `Γ`-orbits of `ℚ`-hyperplanes of `L`
(`.tmp-sources/looijenga-math0201218v2.md:487`: "a collection of Q-hyperplanes of L which meet C").
It is an infinite set whenever `Γ` is infinite; the finiteness argument of the counting lemma is
about it, not about a finite family, which would cut every cone finitely for a trivial reason. -/
def orbitFamily (H₀ : Finset (Submodule ℚ V)) (Γ : Set (V ≃ₗ[ℚ] V)) : Set (Submodule ℚ V) :=
  ⋃ ℓ₀ ∈ (H₀ : Set (Submodule ℚ V)),
    {ℓ : Submodule ℚ V | ∃ e ∈ Γ, ℓ = ℓ₀.map (e : V →ₗ[ℚ] V)}

theorem mem_orbitFamily {H₀ : Finset (Submodule ℚ V)} {Γ : Set (V ≃ₗ[ℚ] V)}
    {ℓ : Submodule ℚ V} :
    ℓ ∈ orbitFamily H₀ Γ ↔ ∃ ℓ₀ ∈ H₀, ∃ e ∈ Γ, ℓ = ℓ₀.map (e : V →ₗ[ℚ] V) := by
  rw [orbitFamily, Set.mem_iUnion₂]
  exact ⟨fun ⟨ℓ₀, _, e, he, h⟩ => ⟨ℓ₀, ‹ℓ₀ ∈ H₀›, e, he, h⟩,
    fun ⟨ℓ₀, h₀, e, he, h⟩ => ⟨ℓ₀, h₀, e, he, h⟩⟩

/-- **The norms on a finite union of `Γ`-orbits take finitely many values** (Looijenga, Example 4.3
(b), p. 18): with `Γ` preserving the lattice `Λ` and its form, the generator of `ℓ ∩ Λ` has the same
norm as the generator of `ℓ₀ ∩ Λ` for the representative `ℓ₀` of its orbit
(`form_eq_of_primitive_map`), so `H` has no more norm values than `H₀` has members. This is the
stopping step of the previous turn, and it is what turns "finitely many normals of value `-m` cut
`P` for each `m`" into the statement of #161. -/
theorem finite_form_values_of_orbitFamily (Λ : Submodule ℤ V) (BQ : LinearMap.BilinForm ℚ V)
    (H₀ : Finset (Submodule ℚ V)) (Γ : Set (V ≃ₗ[ℚ] V))
    (hΓΛ : ∀ e ∈ Γ, Submodule.map ((e : V →ₗ[ℚ] V).restrictScalars ℤ) Λ = Λ)
    (hΓiso : ∀ e ∈ Γ, ∀ x y, BQ (e x) (e y) = BQ x y)
    (hH₀ : ∀ ℓ₀ ∈ H₀, ∃ v : V, v ≠ 0 ∧
      Λ ⊓ ℓ₀.restrictScalars ℤ = Submodule.span ℤ ({v} : Set V)) :
    ∃ M : Finset ℚ, ∀ ℓ ∈ orbitFamily H₀ Γ, ∀ v : V, v ≠ 0 →
      Λ ⊓ ℓ.restrictScalars ℤ = Submodule.span ℤ ({v} : Set V) → BQ v v ∈ M := by
  classical
  choose g hg0 hgspan using hH₀
  refine ⟨H₀.attach.image (fun ℓ₀ => BQ (g ℓ₀.1 ℓ₀.2) (g ℓ₀.1 ℓ₀.2)), ?_⟩
  intro ℓ hℓ v hv0 hv
  obtain ⟨ℓ₀, hℓ₀, e, he, rfl⟩ := mem_orbitFamily.mp hℓ
  have hform := form_eq_of_primitive_map (Λ := Λ) (BQ := BQ) (e := e) (hΓΛ e he) (hΓiso e he)
    (ℓ := ℓ₀) (v := g ℓ₀ hℓ₀) (w := v) (hgspan ℓ₀ hℓ₀) hv (hg0 ℓ₀ hℓ₀)
  rw [hform]
  refine Finset.mem_image.2 ⟨⟨ℓ₀, hℓ₀⟩, ?_, rfl⟩
  exact Finset.mem_attach H₀ ⟨ℓ₀, hℓ₀⟩

end OrbitLayer

/-! ## Example 4.3 (b): finitely many cutters per rational subcone, for the `H` of the source

The hypothesis `CutsFinitelyOnRational` of the arrangement section, discharged for Looijenga's
`H` — a finite union of `Γ`-orbits of `ℚ`-hyperplanes (`orbitFamily`), carried by the lines of
their normals — from the two steps the module docstring names: the norm of the primitive generator
of `ℓ ⊓ Λ` is constant on an orbit (`finite_form_values_of_orbitFamily`), so it takes finitely many
values; per value the pair bounds of the counting lemma leave finitely many lattice normals, taken
over the finitely many ordered pairs of rational generators of the cone
(`finite_pairSet_of_cutSigns`, `finite_cutters_of_pair_bounds`); the values of one sign contribute
nothing (`one_signed_of_nonneg_quadratic`); and a line of `H` is recovered from its generator
(`span_singleton_of_inf_span_eq`), which makes `ℓ ↦ v_ℓ` injective. The result is
`cutsFinitelyOnRational_orbitFamily`, the form the module docstring names as owed, and
`cutsFinitelyOnRational_of_finiteOrbits` with a general choice of generator. -/

section FiniteOrbits

variable [Module.Finite ℚ V]

/-- **A normal of nonnegative value is one-signed on a cone inside the closed sheet**: the pairing
with a timelike or isotropic vector of the sheet does not change sign on the sheet
(`nonneg_associated_of_mem_closedSheet`, applied to the normal or to its negative),
in either of the two sheets. Such a normal therefore never cuts a cone inside `C₊`, which is why the
count over the norm values of `H` runs only over the negative ones. -/
theorem one_signed_of_nonneg_quadratic {Q : QuadraticForm ℝ (realified V)} (hpos : sigPos Q = 1)
    {BQ : LinearMap.BilinForm ℚ V}
    (hBQ : ∀ u w : V, (associated Q) (rationalPoint u) (rationalPoint w) = (BQ u w : ℝ))
    {Cplus : PointedCone ℝ (realified V)} {t : realified V} (ht : 0 < Q t)
    (hsheet : ∀ v : V, rationalPoint v ∈ Cplus →
      0 ≤ Q (rationalPoint v) ∧ 0 ≤ (associated Q) (rationalPoint v) t)
    {v : V} (hQv : 0 ≤ Q (rationalPoint v)) :
    (∀ x : V, rationalPoint x ∈ Cplus → 0 ≤ (BQ v x : ℝ)) ∨
      ∀ x : V, rationalPoint x ∈ Cplus → (BQ v x : ℝ) ≤ 0 := by
  have key : ∀ w : V, 0 ≤ Q (rationalPoint w) → 0 ≤ (associated Q) (rationalPoint w) t →
      ∀ x : V, rationalPoint x ∈ Cplus → 0 ≤ (BQ w x : ℝ) := by
    intro w hQw hwt x hx
    rw [← hBQ w x]
    exact nonneg_associated_of_mem_closedSheet (Q := Q) hpos ht hQw hwt
      (hsheet x hx).1 (hsheet x hx).2
  rcases le_or_gt 0 ((associated Q) (rationalPoint v) t) with hvt | hvt
  · exact Or.inl (key v hQv hvt)
  · exact Or.inr fun x hx => by
      have hQ := key (-v) (by simpa using hQv) (by simpa using hvt.le) x hx
      simpa using hQ

set_option maxHeartbeats 800000 in
/-- **Two sheet vectors with vanishing pairing are ℝ-proportional** (for a form of signature
`(1, dim − 1)`): a timelike one of the pair is orthogonal to a sheet vector, which is on the
negative definite side of a timelike vector and hence zero; and for a pair of null ones, the
combination `⟨a, t⟩ • b - ⟨b, t⟩ • a` is null and orthogonal to the timelike `t`, so it vanishes —
the two are proportional along the boundary. This is what makes a pair of generators of a cone of
the sheet, one taking each sign of a cutting normal, a pair with positive pairing, which is what
the three bounds of the counting lemma need. -/
theorem exists_smul_of_associated_eq_zero_of_mem_closedSheet
    {Q : QuadraticForm ℝ (realified V)} (hpos : sigPos Q = 1) (hnd : Q.Nondegenerate)
    {t : realified V} (ht : 0 < Q t) {a b : V}
    (ha : rationalPoint a ∈ closedSheet Q hpos ht) (hb : rationalPoint b ∈ closedSheet Q hpos ht)
    (hab : (associated Q) (rationalPoint a) (rationalPoint b) = 0)
    (ha0 : rationalPoint a ≠ 0) :
    ∃ c : ℝ, rationalPoint b = c • rationalPoint a := by
  rcases eq_or_lt_of_le ha.1 with hQa | hQa
  · rcases eq_or_lt_of_le hb.1 with hQb | hQb
    · -- both null: `⟨a, t⟩ • b - ⟨b, t⟩ • a` is null and orthogonal to the timelike `t`
      have hA : (associated Q) (rationalPoint a) t ≠ 0 := by
        intro h0
        exact ha0 (eq_zero_of_perp_of_quadratic_eq_zero (Q := Q) (t := t) (x := rationalPoint a)
          hpos hnd ht h0 hQa.symm)
      set A : ℝ := (associated Q) (rationalPoint a) t with hAdef
      set B : ℝ := (associated Q) (rationalPoint b) t with hBdef
      set z : realified V := A • rationalPoint b - B • rationalPoint a with hzdef
      have hQz : Q z = 0 := by
        rw [hzdef, sub_eq_add_neg, ← neg_smul, quadratic_expand]
        rw [← hQa, ← hQb, associated_comm (Q := Q) (rationalPoint b) (rationalPoint a), hab]
        ring
      have hzt : (associated Q) z t = 0 := by
        rw [hzdef, map_sub, map_smul, map_smul, LinearMap.sub_apply, LinearMap.smul_apply,
          LinearMap.smul_apply, smul_eq_mul, smul_eq_mul, ← hAdef, ← hBdef]
        ring
      have hz0 : z = 0 :=
        eq_zero_of_perp_of_quadratic_eq_zero (Q := Q) (t := t) (x := z) hpos hnd ht hzt hQz
      have hAB : A • rationalPoint b = B • rationalPoint a := by
        rw [hzdef, sub_eq_zero] at hz0
        exact hz0
      refine ⟨B / A, ?_⟩
      rw [div_eq_inv_mul, mul_smul]
      have hstep := congrArg (fun y : realified V => A⁻¹ • y) hAB
      rw [smul_smul, inv_mul_cancel₀ hA, one_smul] at hstep
      exact hstep
    · -- `b` timelike: `a` is orthogonal to it and on the sheet, hence zero
      exact absurd (eq_zero_of_perp_of_quadratic_eq_zero (Q := Q) (t := rationalPoint b)
        (x := rationalPoint a) hpos hnd hQb hab hQa.symm) ha0
  · -- `a` timelike: `b` is orthogonal to it and on the sheet, hence zero
    have hle := quadratic_nonpos_of_associated_eq_zero (Q := Q) hpos (a := rationalPoint a) hQa
      (by rw [associated_comm]; exact hab)
    have hQb : Q (rationalPoint b) = 0 := le_antisymm hle hb.1
    have hb0 : rationalPoint b = 0 :=
      eq_zero_of_perp_of_quadratic_eq_zero (Q := Q) (t := rationalPoint a) (x := rationalPoint b)
        hpos hnd hQa (by rw [associated_comm]; exact hab) hQb
    exact ⟨0, by rw [hb0, zero_smul]⟩

omit [Module.Finite ℚ V] in
/-- **Every rational vector becomes a lattice vector after scaling by a positive integer**: on a
`ℚ`-basis the coordinates of `a` are rationals, and the product of their denominators clears
them. -/
theorem exists_nat_smul_mem_span {ι : Type*} [Fintype ι] (bs : Module.Basis ι ℚ V) (a : V) :
    ∃ D : ℕ, 0 < D ∧ (D : ℤ) • a ∈ Submodule.span ℤ (Set.range bs) := by
  classical
  refine ⟨∏ i, (bs.repr a i).den, Finset.prod_pos fun i _ => (bs.repr a i).den_pos, ?_⟩
  rw [bs.mem_span_iff_repr_mem ℤ]
  intro i
  have hrepr : bs.repr ((↑(∏ i, (bs.repr a i).den) : ℤ) • a) i
      = ((∏ i, (bs.repr a i).den : ℕ) : ℚ) * bs.repr a i := by
    rw [← Int.cast_smul_eq_zsmul (R := ℚ) (↑(∏ i, (bs.repr a i).den) : ℤ), map_smul,
      Finsupp.smul_apply, smul_eq_mul]
    push_cast
    ring
  rw [hrepr]
  obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem (f := fun i => (bs.repr a i).den) (Finset.mem_univ i)
  refine ⟨(k : ℤ) * (bs.repr a i).num, ?_⟩
  rw [hk]
  rw [show (((bs.repr a i).den * k : ℕ) : ℚ) = ((bs.repr a i).den : ℚ) * (k : ℚ) by
    push_cast; ring]
  rw [show (algebraMap ℤ ℚ) ((k : ℤ) * (bs.repr a i).num)
      = (k : ℚ) * ((bs.repr a i).num : ℚ) by push_cast; rfl]
  rw [← Rat.mul_den_eq_num (bs.repr a i)]
  ring

omit [Module.Finite ℚ V] in
/-- **A rational line with a rank-one intersection with the lattice is the line of its
generator**: every vector of it becomes a lattice vector after scaling, so it is a rational
multiple of the generator. -/
theorem span_singleton_of_inf_span_eq {ι : Type*} [Fintype ι] (bs : Module.Basis ι ℚ V)
    {ℓ : Submodule ℚ V}
    {v : V} (h : Submodule.span ℤ (Set.range bs) ⊓ ℓ.restrictScalars ℤ
      = Submodule.span ℤ ({v} : Set V)) :
    ℓ = Submodule.span ℚ ({v} : Set V) := by
  have hvℓ : v ∈ ℓ := by
    have hv : v ∈ Submodule.span ℤ (Set.range bs) ⊓ ℓ.restrictScalars ℤ := by
      rw [h]
      exact Submodule.subset_span (Set.mem_singleton v)
    exact hv.2
  refine le_antisymm ?_ (Submodule.span_le.mpr fun x hx => by
    rw [Set.mem_singleton_iff] at hx
    exact hx ▸ hvℓ)
  intro w hw
  obtain ⟨D, hDpos, hDw⟩ := exists_nat_smul_mem_span bs w
  have hmem : ((D : ℤ) • w : V) ∈ Submodule.span ℤ (Set.range bs) ⊓ ℓ.restrictScalars ℤ :=
    ⟨hDw, Submodule.smul_mem _ _ hw⟩
  rw [h] at hmem
  obtain ⟨n, hn⟩ := Submodule.mem_span_singleton.mp hmem
  rw [Submodule.mem_span_singleton]
  refine ⟨(n : ℚ) / (D : ℚ), ?_⟩
  have hcast : ((n : ℚ) • v : V) = (D : ℚ) • w := by
    have h1 : ((n : ℚ) • v : V) = n • v := Int.cast_smul_eq_zsmul (R := ℚ) n v
    have h2 : ((D : ℤ) • w : V) = (D : ℚ) • w := by
      rw [← Int.cast_smul_eq_zsmul (R := ℚ) (D : ℤ) w]
      push_cast
      rfl
    rw [h1, hn, h2]
  have hDq : (D : ℚ) ≠ 0 := by exact_mod_cast hDpos.ne'
  calc ((n : ℚ) / (D : ℚ)) • v = ((D : ℚ)⁻¹ * (n : ℚ)) • v := by rw [div_eq_inv_mul]
    _ = (D : ℚ)⁻¹ • ((n : ℚ) • v) := by rw [mul_smul]
    _ = (D : ℚ)⁻¹ • ((D : ℚ) • w) := by rw [hcast]
    _ = w := by rw [smul_smul, inv_mul_cancel₀ hDq, one_smul]

omit [Module.Finite ℚ V] in
/-- **The two sign conditions of a pair are symmetric under `v ↦ -v`**: the set of lattice normals
of a value `-m` taking a positive value on `a` and a negative one on `b` is finite exactly when the
same set with the roles of `a` and `b` exchanged is. This is what lets the isotropic case of the
counting lemma be applied in either order of the pair. -/
theorem finite_pairSigns_iff_neg {Λs : Submodule ℤ V} {Q : QuadraticForm ℝ (realified V)}
    {BQ : LinearMap.BilinForm ℚ V} {m : ℝ} {a b : V} :
    {v : V | v ∈ Λs ∧ Q (rationalPoint v) = -m ∧ 0 < (BQ v a : ℝ) ∧ (BQ v b : ℝ) < 0}.Finite ↔
      {v : V | v ∈ Λs ∧ Q (rationalPoint v) = -m ∧ 0 < (BQ v b : ℝ) ∧
        (BQ v a : ℝ) < 0}.Finite := by
  have hstep : ∀ (c d : V) (v : V), (v ∈ Λs ∧ Q (rationalPoint v) = -m ∧
      0 < (BQ v c : ℝ) ∧ (BQ v d : ℝ) < 0) →
      (-v ∈ Λs ∧ Q (rationalPoint (-v)) = -m ∧ 0 < (BQ (-v) d : ℝ) ∧ (BQ (-v) c : ℝ) < 0) := by
    rintro c d v ⟨hv, hQ, hx, hy⟩
    refine ⟨Submodule.neg_mem _ hv, ?_, ?_, ?_⟩
    · rw [map_neg, QuadraticMap.map_neg]
      exact hQ
    · rw [map_neg, LinearMap.neg_apply]
      push_cast
      linarith
    · rw [map_neg, LinearMap.neg_apply]
      push_cast
      linarith
  constructor
  · intro h
    refine (h.image fun v => -v).subset ?_
    rintro v hv
    exact ⟨-v, hstep b a v hv, neg_neg v⟩
  · intro h
    refine (h.image fun v => -v).subset ?_
    rintro v hv
    exact ⟨-v, hstep a b v hv, neg_neg v⟩

omit [Module.Finite ℚ V] in
/-- **A pair of proportional generators contributes no cutting normal**: if `b` is a real multiple
of `a`, either the two sign conditions are incompatible (a positive multiple) or the multiple is
negative and the line of `a` lies in the cone, which salience forbids. -/
theorem finite_pairSet_of_smul {Q : QuadraticForm ℝ (realified V)}
    {BQ : LinearMap.BilinForm ℚ V}
    (hBQ : ∀ u w : V, (associated Q) (rationalPoint u) (rationalPoint w) = (BQ u w : ℝ))
    {Λs : Submodule ℤ V} {m : ℝ} {P : PointedCone ℝ (realified V)}
    (hPsal : (P : ConvexCone ℝ (realified V)).Salient) {a b : V}
    (haP : rationalPoint a ∈ P) (hbP : rationalPoint b ∈ P) {c : ℝ}
    (hc : rationalPoint b = c • rationalPoint a) :
    {v : V | v ∈ Λs ∧ Q (rationalPoint v) = -m ∧ 0 < (BQ v a : ℝ) ∧ (BQ v b : ℝ) < 0}.Finite := by
  by_cases ha0 : rationalPoint a = 0
  · refine Set.Finite.subset Set.finite_empty ?_
    rintro v ⟨-, -, hx, -⟩
    rw [← hBQ v a, ha0, map_zero] at hx
    simp at hx
  · refine Set.Finite.subset Set.finite_empty ?_
    rintro v ⟨-, -, hx, hy⟩
    have hbval : (BQ v b : ℝ) = c * (BQ v a : ℝ) := by
      rw [← hBQ v b, hc, map_smul, smul_eq_mul, hBQ v a]
    rcases lt_trichotomy c 0 with hc0 | hc0 | hc0
    · exfalso
      have hca : rationalPoint a = c⁻¹ • rationalPoint b := by
        rw [hc, smul_smul, inv_mul_cancel₀ (ne_of_lt hc0), one_smul]
      have hneg : -rationalPoint a ∈ P := by
        have hcoef : (0 : ℝ) ≤ -c⁻¹ := by
          have : c⁻¹ < 0 := inv_neg''.mpr hc0
          linarith
        have hrewrite : -rationalPoint a = (-c⁻¹) • rationalPoint b := by
          rw [hca, neg_smul]
        rw [hrewrite]
        exact PointedCone.smul_mem _ hcoef hbP
      exact hPsal (rationalPoint a) haP ha0 hneg
    · rw [hc0, zero_mul] at hbval
      rw [hbval] at hy
      exact absurd hy (lt_irrefl 0)
    · nlinarith [hx, hbval, hc0]

set_option maxHeartbeats 1000000 in
/-- **One ordered pair of generators bounds the cutting normals of a fixed value.** For a rational
cone `P = hull (rationalPoint '' s)` inside `C₊` and two of its generators, only finitely many
lattice normals of value `-m` take a positive value on the first and a negative one on the second.
The three cases of the counting lemma (`finite_cutting_normals_of_both_timelike`,
`finite_cutting_normals_of_isotropic`, `finite_cutting_normals_of_both_isotropic`) cover the pairs
with positive pairing; a pair with vanishing pairing is proportional
(`exists_smul_of_associated_eq_zero_of_mem_closedSheet`) and contributes nothing
(`finite_pairSet_of_smul`); and a pair of two timelike generators with vanishing Gram determinant is
proportional, since the difference `b - (a·b / Q a) • a` is null and orthogonal to a timelike
vector. -/
theorem finite_pairSet_of_cutSigns {ι : Type*} [Fintype ι] [DecidableEq ι]
    {bs : Module.Basis ι ℚ V} {Q : QuadraticForm ℝ (realified V)} (hpos : sigPos Q = 1)
    (hnd : Q.Nondegenerate) {BQ : LinearMap.BilinForm ℚ V} (hBQsym : BQ.IsSymm)
    (hBQnd : BQ.Nondegenerate)
    (hBQ : ∀ u w : V, (associated Q) (rationalPoint u) (rationalPoint w) = (BQ u w : ℝ))
    {Cplus : PointedCone ℝ (realified V)} (hsal : (Cplus : ConvexCone ℝ (realified V)).Salient)
    {t : realified V} (ht : 0 < Q t)
    (hsheet : ∀ v : V, rationalPoint v ∈ Cplus →
      0 ≤ Q (rationalPoint v) ∧ 0 ≤ (associated Q) (rationalPoint v) t)
    {P : PointedCone ℝ (realified V)} (hPle : P ≤ Cplus)
    {s : Finset V} (hP : P = PointedCone.hull ℝ (rationalPoint '' (s : Set V)))
    {m : ℝ} (hm : 0 < m) {D : ℕ} (hD : 0 < D)
    (hDs : ∀ a ∈ s, (D : ℤ) • a ∈ Submodule.span ℤ (Set.range bs))
    (hint : ∀ x ∈ Submodule.span ℤ (Set.range bs), ∀ y ∈ Submodule.span ℤ (Set.range bs),
      ∃ n : ℤ, BQ x y = (n : ℚ))
    {a b : V} (ha : a ∈ s) (hb : b ∈ s) :
    {v : V | v ∈ Submodule.span ℤ (Set.range bs) ∧ Q (rationalPoint v) = -m ∧
      0 < (BQ v a : ℝ) ∧ (BQ v b : ℝ) < 0}.Finite := by
  have hPsal : (P : ConvexCone ℝ (realified V)).Salient := hsal.anti hPle
  have haP : rationalPoint a ∈ P := by
    rw [hP]
    exact PointedCone.subset_hull (Set.mem_image_of_mem _ (by exact_mod_cast ha))
  have hbP : rationalPoint b ∈ P := by
    rw [hP]
    exact PointedCone.subset_hull (Set.mem_image_of_mem _ (by exact_mod_cast hb))
  have hsa := hsheet a (hPle haP)
  have hsb := hsheet b (hPle hbP)
  have hnn : 0 ≤ (associated Q) (rationalPoint a) (rationalPoint b) :=
    nonneg_associated_of_mem_closedSheet (Q := Q) hpos ht hsa.1 hsa.2 hsb.1 hsb.2
  have hdeg : ∀ {c : ℝ}, rationalPoint b = c • rationalPoint a →
      {v : V | v ∈ Submodule.span ℤ (Set.range bs) ∧ Q (rationalPoint v) = -m ∧
        0 < (BQ v a : ℝ) ∧ (BQ v b : ℝ) < 0}.Finite := by
    intro c hc
    exact finite_pairSet_of_smul (Q := Q) hBQ hPsal haP hbP hc
  rcases eq_or_lt_of_le hsa.1 with hQa | hQa <;> rcases eq_or_lt_of_le hsb.1 with hQb | hQb
  · -- both isotropic
    rcases eq_or_lt_of_le hnn with h0 | hpos'
    · by_cases hra : rationalPoint a = 0
      · refine Set.Finite.subset Set.finite_empty ?_
        rintro v ⟨-, -, hx, -⟩
        rw [← hBQ v a, hra, map_zero] at hx
        simp at hx
      · exact hdeg (exists_smul_of_associated_eq_zero_of_mem_closedSheet (Q := Q) hpos hnd ht
          ⟨hQa.le, hsa.2⟩ ⟨hQb.le, hsb.2⟩ h0.symm hra).choose_spec
    · exact finite_cutting_normals_of_both_isotropic (Q := Q) hpos hBQsym hBQnd hBQ (a := a)
        (b := b) (m := m) hm hQa.symm hQb.symm hpos' hD hD (hDs a ha) (hDs b hb) hint
  · -- `a` isotropic, `b` timelike
    have hnn' : 0 ≤ (associated Q) (rationalPoint b) (rationalPoint a) := by
      rw [associated_comm]; exact hnn
    rcases eq_or_lt_of_le hnn' with h0 | hpos'
    · by_cases hra : rationalPoint a = 0
      · refine Set.Finite.subset Set.finite_empty ?_
        rintro v ⟨-, -, hx, -⟩
        rw [← hBQ v a, hra, map_zero] at hx
        simp at hx
      · exact hdeg (exists_smul_of_associated_eq_zero_of_mem_closedSheet (Q := Q) hpos hnd ht
          ⟨hQa.le, hsa.2⟩ ⟨hQb.le, hsb.2⟩ (by rw [associated_comm]; exact h0.symm) hra).choose_spec
    · rw [finite_pairSigns_iff_neg]
      exact finite_cutting_normals_of_isotropic (Q := Q) hpos hBQsym hBQnd hBQ (a := b) (b := a)
        (m := m) hm hQb hQa.symm hpos' hD (hDs a ha) hint
  · -- `a` timelike, `b` isotropic
    rcases eq_or_lt_of_le hnn with h0 | hpos'
    · by_cases hra : rationalPoint a = 0
      · refine Set.Finite.subset Set.finite_empty ?_
        rintro v ⟨-, -, hx, -⟩
        rw [← hBQ v a, hra, map_zero] at hx
        simp at hx
      · exact hdeg (exists_smul_of_associated_eq_zero_of_mem_closedSheet (Q := Q) hpos hnd ht
          ⟨hQa.le, hsa.2⟩ ⟨hQb.le, hsb.2⟩ h0.symm hra).choose_spec
    · exact finite_cutting_normals_of_isotropic (Q := Q) hpos hBQsym hBQnd hBQ (a := a) (b := b)
        (m := m) hm hQa hQb.symm hpos' hD (hDs b hb) hint
  · -- both timelike
    rcases eq_or_lt_of_le hnn with h0 | hpos'
    · by_cases hra : rationalPoint a = 0
      · refine Set.Finite.subset Set.finite_empty ?_
        rintro v ⟨-, -, hx, -⟩
        rw [← hBQ v a, hra, map_zero] at hx
        simp at hx
      · exact hdeg (exists_smul_of_associated_eq_zero_of_mem_closedSheet (Q := Q) hpos hnd ht
          ⟨hQa.le, hsa.2⟩ ⟨hQb.le, hsb.2⟩ h0.symm hra).choose_spec
    · -- the Gram determinant is positive: `c ^ 2 - Q a * Q b ≥ 0` by the key inequality
      set c : ℝ := (associated Q) (rationalPoint a) (rationalPoint b) with hcdef
      set A : ℝ := Q (rationalPoint a) with hAdef
      set B : ℝ := Q (rationalPoint b) with hBdef
      have hle := mul_self_le_associated_sq (Q := Q) hpos hQa (rationalPoint b)
      rw [associated_comm (Q := Q) (rationalPoint b) (rationalPoint a), ← hcdef, ← hAdef,
        ← hBdef] at hle
      rcases lt_or_eq_of_le (by nlinarith [hle] : (0:ℝ) ≤ c ^ 2 - A * B) with hK | hK
      · exact finite_cutting_normals_of_both_timelike (Q := Q) hpos hBQsym hBQnd hBQ (a := a)
          (b := b) (m := m) hQa hQb hpos' (by rw [← hcdef, ← hAdef, ← hBdef]; linarith)
      · -- proportional: `b - (c / A) • a` is null and orthogonal to the timelike `a`
        have hz : Q (rationalPoint b - (c / A) • rationalPoint a) = 0 := by
          rw [sub_eq_add_neg, ← neg_smul]
          have hexp := quadratic_expand (Q := Q) 1 (-(c / A)) (rationalPoint b) (rationalPoint a)
          simp only [one_smul, one_pow, one_mul] at hexp
          rw [hexp]
          rw [← associated_comm (Q := Q) (rationalPoint a) (rationalPoint b), ← hBdef, ← hAdef,
            ← hcdef]
          field_simp
          nlinarith [hK]
        have hzt : (associated Q) (rationalPoint b - (c / A) • rationalPoint a)
            (rationalPoint a) = 0 := by
          rw [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul,
            associated_self_apply, ← hAdef, ← associated_comm (Q := Q) (rationalPoint a)
            (rationalPoint b), ← hcdef]
          field_simp
          ring
        have hzero := eq_zero_of_perp_of_quadratic_eq_zero (Q := Q) (t := rationalPoint a)
          (x := rationalPoint b - (c / A) • rationalPoint a) hpos hnd hQa hzt hz
        refine hdeg (c := c / A) ?_
        rw [sub_eq_zero] at hzero
        exact hzero

set_option maxHeartbeats 1000000 in
/-- **Example 4.3 (b), the hypothesis: a finite union of `Γ`-orbits of `ℚ`-hyperplanes cuts each
rational subcone of `C₊` finitely often** (Looijenga, pp. 17-18).

`H` is the orbit family of a finite `H₀` under `Γ` (`orbitFamily`), carried by the `ℚ`-lines of its
normals, and `g ℓ` is a generator of `ℓ ⊓ Λ` for each member. The two inputs the source supplies
and this file states are the arithmeticity (`Λ` a lattice on which the form is integral, `Γ` acting
on it by isometries, so that the norm of the generator is constant on an orbit —
`finite_form_values_of_orbitFamily`) and the two cone-side hypotheses of the hyperbolic setting
(`C₊` salient, and its rational points on the closed sheet, `hsheet`). The counting per value of the
norm is `finite_pairSet_of_cutSigns` over the finitely many ordered pairs of generators of the
rational cone, and the values of one sign (`m ≥ 0`) give nothing (`one_signed_of_nonneg_quadratic`).
The identification of the cut of a hyperplane with the cut of the form of its generator is
`hyperplaneCuts_iff_generators`, and `span_singleton_of_inf_span_eq` recovers the line from the
generator, which makes `ℓ ↦ g ℓ` injective. -/
theorem cutsFinitelyOnRational_of_finiteOrbits {Q : QuadraticForm ℝ (realified V)}
    (hpos : sigPos Q = 1) (hnd : Q.Nondegenerate) {BQ : LinearMap.BilinForm ℚ V}
    (hBQsym : BQ.IsSymm) (hBQnd : BQ.Nondegenerate)
    (hBQ : ∀ u w : V, (associated Q) (rationalPoint u) (rationalPoint w) = (BQ u w : ℝ))
    {Cplus : PointedCone ℝ (realified V)}
    (hsal : (Cplus : ConvexCone ℝ (realified V)).Salient) {t : realified V} (ht : 0 < Q t)
    (hsheet : ∀ v : V, rationalPoint v ∈ Cplus →
      0 ≤ Q (rationalPoint v) ∧ 0 ≤ (associated Q) (rationalPoint v) t)
    {ι : Type*} [Fintype ι] [DecidableEq ι] {bs : Module.Basis ι ℚ V}
    (Γ : Set (V ≃ₗ[ℚ] V)) (H₀ : Finset (Submodule ℚ V))
    (hΓΛ : ∀ e ∈ Γ, Submodule.map ((e : V →ₗ[ℚ] V).restrictScalars ℤ)
      (Submodule.span ℤ (Set.range bs)) = Submodule.span ℤ (Set.range bs))
    (hΓiso : ∀ e ∈ Γ, ∀ x y, BQ (e x) (e y) = BQ x y)
    (hH₀ : ∀ ℓ₀ ∈ H₀, ∃ v : V, v ≠ 0 ∧
      Submodule.span ℤ (Set.range bs) ⊓ ℓ₀.restrictScalars ℤ = Submodule.span ℤ ({v} : Set V))
    (hint : ∀ x ∈ Submodule.span ℤ (Set.range bs), ∀ y ∈ Submodule.span ℤ (Set.range bs),
      ∃ n : ℤ, BQ x y = (n : ℚ))
    (g : ↥(orbitFamily H₀ Γ) → V)
    (hg : ∀ ℓ : ↥(orbitFamily H₀ Γ), g ℓ ≠ 0 ∧
      Submodule.span ℤ (Set.range bs) ⊓ ℓ.1.restrictScalars ℤ = Submodule.span ℤ ({g ℓ} : Set V)) :
    CutsFinitelyOnRational Cplus (fun ℓ : ↥(orbitFamily H₀ Γ) => normalForm Q (g ℓ)) := by
  classical
  intro P hP hPle
  obtain ⟨s, rfl⟩ := hP
  -- a common denominator for the generators of the cone
  choose Dg hDg using fun a : V => exists_nat_smul_mem_span bs a
  set D : ℕ := ∏ a ∈ s, Dg a with hDdef
  have hDpos : 0 < D := Finset.prod_pos fun a _ => (hDg a).1
  have hDs : ∀ a ∈ s, (D : ℤ) • a ∈ Submodule.span ℤ (Set.range bs) := by
    intro a ha
    obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem (f := fun a => Dg a) ha
    have hDcast : (D : ℤ) = (k : ℤ) * (Dg a : ℤ) := by
      rw [hDdef, hk]
      push_cast
      ring
    rw [hDcast, mul_zsmul]
    exact Submodule.smul_mem _ _ (hDg a).2
  -- the values of the norm on `H`
  obtain ⟨M, hM⟩ := finite_form_values_of_orbitFamily (Λ := Submodule.span ℤ (Set.range bs))
    BQ H₀ Γ hΓΛ hΓiso hH₀
  -- per value of the norm
  have hval : ∀ m ∈ M, {v : V | v ∈ Submodule.span ℤ (Set.range bs) ∧
      Q (rationalPoint v) = (m : ℝ) ∧ ∃ a ∈ s, ∃ b ∈ s, 0 < (BQ v a : ℝ) ∧
        (BQ v b : ℝ) < 0}.Finite := by
    intro m hm
    by_cases hmneg : m < 0
    · have hmpos : 0 < -(m : ℝ) := by
        have : (m : ℝ) < 0 := by exact_mod_cast hmneg
        linarith
      have hmain := finite_cutters_of_pair_bounds (Q := Q) (BQ := BQ) (m := -(m : ℝ))
        (Submodule.span ℤ (Set.range bs)) s (fun a ha b hb =>
          finite_pairSet_of_cutSigns (Q := Q) hpos hnd hBQsym hBQnd hBQ hsal ht hsheet hPle rfl
            hmpos hDpos hDs hint ha hb)
      simpa using hmain
    · refine Set.Finite.subset Set.finite_empty ?_
      rintro v ⟨hv, hQ, a, ha, b, hb, hx, hy⟩
      have hQv : 0 ≤ Q (rationalPoint v) := by
        rw [hQ]
        exact_mod_cast (not_lt.mp hmneg : (0:ℚ) ≤ m)
      have haP : rationalPoint a ∈ PointedCone.hull ℝ (rationalPoint '' (s : Set V)) :=
        PointedCone.subset_hull (Set.mem_image_of_mem _ (by exact_mod_cast ha))
      have hbP : rationalPoint b ∈ PointedCone.hull ℝ (rationalPoint '' (s : Set V)) :=
        PointedCone.subset_hull (Set.mem_image_of_mem _ (by exact_mod_cast hb))
      rcases one_signed_of_nonneg_quadratic (Q := Q) hpos hBQ ht hsheet hQv with hpos' | hneg'
      · exact absurd (hpos' b (hPle hbP)) (not_le.mpr hy)
      · exact absurd (hneg' a (hPle haP)) (not_le.mpr hx)
  -- the cutters inject into the union of those sets
  have hinj : Set.InjOn g
      {ℓ : ↥(orbitFamily H₀ Γ) | CutsOn (normalForm Q (g ℓ)).toLinearMap
        (PointedCone.hull ℝ (rationalPoint '' (s : Set V)))} := by
    intro ℓ _ ℓ' _ h
    have h1 : ℓ.1 = Submodule.span ℚ ({g ℓ} : Set V) :=
      span_singleton_of_inf_span_eq bs (hg ℓ).2
    have h2 : ℓ'.1 = Submodule.span ℚ ({g ℓ'} : Set V) :=
      span_singleton_of_inf_span_eq bs (hg ℓ').2
    exact Subtype.ext (by rw [h1, h2, h])
  refine Set.Finite.of_finite_image ?_ hinj
  refine (Set.Finite.biUnion M.finite_toSet fun m hm => hval m hm).subset ?_
  rintro v ⟨ℓ, hℓ, rfl⟩
  have hℓeq : ℓ.1 = Submodule.span ℚ ({g ℓ} : Set V) :=
    span_singleton_of_inf_span_eq bs (hg ℓ).2
  have hcuts : CutsOn ((associated Q) (rationalPoint (g ℓ)))
      (PointedCone.hull ℝ (rationalPoint '' (s : Set V))) := by
    rw [← normalForm_toLinearMap]
    exact hℓ
  have hpair := (hyperplaneCuts_iff_generators (Q := Q) hℓeq rfl hBQ).mp
    ((hyperplaneCuts_iff_cutsOn (Q := Q) hℓeq _).mpr hcuts)
  have hQv : Q (rationalPoint (g ℓ)) = ((BQ (g ℓ) (g ℓ) : ℚ) : ℝ) := by
    rw [← associated_self_apply]
    exact hBQ (g ℓ) (g ℓ)
  have hmem : BQ (g ℓ) (g ℓ) ∈ M :=
    hM ℓ.1 ℓ.2 (g ℓ) (hg ℓ).1 (hg ℓ).2
  have hmemΛ : g ℓ ∈ Submodule.span ℤ (Set.range bs) := by
    have h1 : g ℓ ∈ Submodule.span ℤ (Set.range bs) ⊓ ℓ.1.restrictScalars ℤ := by
      rw [(hg ℓ).2]
      exact Submodule.subset_span (Set.mem_singleton (g ℓ))
    exact h1.1
  obtain ⟨⟨a, ha, hx⟩, ⟨b, hb, hy⟩⟩ := hpair
  exact Set.mem_iUnion₂.mpr ⟨_, hmem, hmemΛ, hQv, a, ha, b, hb, by exact_mod_cast hx,
    by exact_mod_cast hy⟩

omit [Module.Finite ℚ V] in
/-- **Every member of the orbit family has a primitive generator**: the generator of an orbit
representative's intersection with the lattice, carried by the isometry that puts it in its orbit
(`map_inf_restrictScalars`). This is the `g` of `cutsFinitelyOnRational_of_finiteOrbits`; it is
determined up to sign (`eq_or_eq_neg_of_span_singleton_eq`), and `CutsOn` is unchanged by the
sign. -/
theorem exists_generator_of_orbitFamily (Λ : Submodule ℤ V) (H₀ : Finset (Submodule ℚ V))
    (Γ : Set (V ≃ₗ[ℚ] V))
    (hΓΛ : ∀ e ∈ Γ, Submodule.map ((e : V →ₗ[ℚ] V).restrictScalars ℤ) Λ = Λ)
    (hH₀ : ∀ ℓ₀ ∈ H₀, ∃ v : V, v ≠ 0 ∧
      Λ ⊓ ℓ₀.restrictScalars ℤ = Submodule.span ℤ ({v} : Set V)) :
    ∃ g : ↥(orbitFamily H₀ Γ) → V, ∀ ℓ : ↥(orbitFamily H₀ Γ), g ℓ ≠ 0 ∧
      Λ ⊓ ℓ.1.restrictScalars ℤ = Submodule.span ℤ ({g ℓ} : Set V) := by
  classical
  have key : ∀ ℓ : ↥(orbitFamily H₀ Γ), ∃ v : V, v ≠ 0 ∧
      Λ ⊓ ℓ.1.restrictScalars ℤ = Submodule.span ℤ ({v} : Set V) := by
    intro ℓ
    obtain ⟨ℓ₀, hℓ₀, e, he, hEq⟩ := mem_orbitFamily.mp ℓ.2
    obtain ⟨v₀, hv₀, hspan₀⟩ := hH₀ ℓ₀ hℓ₀
    refine ⟨e v₀, ?_, ?_⟩
    · intro h
      exact hv₀ (e.injective (by rw [h, map_zero]))
    · rw [hEq, ← map_inf_restrictScalars (Λ := Λ) (e := e) (hΓΛ e he) ℓ₀, hspan₀,
        Submodule.map_span, Set.image_singleton]
      rfl
  choose g hg using key
  exact ⟨g, hg⟩

set_option maxHeartbeats 1000000 in
/-- **Example 4.3 (b): the hypothesis for the `H` of the source**, with `H` the union of the
`Γ`-orbits of a finite `H₀` and its normals taken by `orbitGenerator`. This is
`cutsFinitelyOnRational_of_finiteOrbits` at the canonical choice of generator. -/
theorem cutsFinitelyOnRational_orbitFamily {Q : QuadraticForm ℝ (realified V)}
    (hpos : sigPos Q = 1) (hnd : Q.Nondegenerate) {BQ : LinearMap.BilinForm ℚ V}
    (hBQsym : BQ.IsSymm) (hBQnd : BQ.Nondegenerate)
    (hBQ : ∀ u w : V, (associated Q) (rationalPoint u) (rationalPoint w) = (BQ u w : ℝ))
    {Cplus : PointedCone ℝ (realified V)}
    (hsal : (Cplus : ConvexCone ℝ (realified V)).Salient) {t : realified V} (ht : 0 < Q t)
    (hsheet : ∀ v : V, rationalPoint v ∈ Cplus →
      0 ≤ Q (rationalPoint v) ∧ 0 ≤ (associated Q) (rationalPoint v) t)
    {ι : Type*} [Fintype ι] [DecidableEq ι] {bs : Module.Basis ι ℚ V}
    (Γ : Set (V ≃ₗ[ℚ] V)) (H₀ : Finset (Submodule ℚ V))
    (hΓΛ : ∀ e ∈ Γ, Submodule.map ((e : V →ₗ[ℚ] V).restrictScalars ℤ)
      (Submodule.span ℤ (Set.range bs)) = Submodule.span ℤ (Set.range bs))
    (hΓiso : ∀ e ∈ Γ, ∀ x y, BQ (e x) (e y) = BQ x y)
    (hH₀ : ∀ ℓ₀ ∈ H₀, ∃ v : V, v ≠ 0 ∧
      Submodule.span ℤ (Set.range bs) ⊓ ℓ₀.restrictScalars ℤ = Submodule.span ℤ ({v} : Set V))
    (hint : ∀ x ∈ Submodule.span ℤ (Set.range bs), ∀ y ∈ Submodule.span ℤ (Set.range bs),
      ∃ n : ℤ, BQ x y = (n : ℚ)) :
    CutsFinitelyOnRational Cplus (fun ℓ : ↥(orbitFamily H₀ Γ) =>
      normalForm Q (Classical.choose (exists_generator_of_orbitFamily
        (Submodule.span ℤ (Set.range bs)) H₀ Γ hΓΛ hH₀) ℓ)) :=
  cutsFinitelyOnRational_of_finiteOrbits (V := V) hpos hnd hBQsym hBQnd hBQ hsal ht hsheet Γ H₀
    hΓΛ hΓiso hH₀ hint _
    fun ℓ => Classical.choose_spec (exists_generator_of_orbitFamily
      (Submodule.span ℤ (Set.range bs)) H₀ Γ hΓΛ hH₀) ℓ

/-! ## Example 4.3 (b) with no finiteness hypothesis: `Σ(H)` for a `Γ`-finite `H`

Looijenga, Example 4.3 (b), pp. 17-18 (`.tmp-sources/looijenga-math0201218v2.md:491`): let `L`
carry a form of signature `(1, dim L - 1)`, let `C` be a component of `x · x > 0` and let `Γ` be an
arithmetic subgroup of `O(L(ℚ))` preserving `C`. A collection `H` of `ℚ`-hyperplanes of `L` which
meet `C` and whose image in the Grassmannian is a finite union of `Γ`-orbits "decomposes `C₊` into
the locally rational decomposition `Σ(H)`"; the preamble of Example 4.3 (p. 17, line 487) asks the
decomposition to be `Γ`-invariant.

* **Locally rational, with nothing left to assume.** `arrangementDecomposition_isLocallyRational`
  proves Definition 4.2's condition for `Σ(H)` from `CutsFinitelyOnRational`, and
  `cutsFinitelyOnRational_orbitFamily` derives that hypothesis for `H` the union of the `Γ`-orbits
  of a finite `H₀`; `arrangementDecomposition_isLocallyRational_of_orbitFamily` is the composition.
* **`Γ`-invariance.** An element `g` of `Γ` carries the hyperplane of a line `ℓ` to the hyperplane
  of `ℓ.map g`, and the generator of the lattice cut `Λ ⊓ ℓ` to `± g` of the generator of the cut
  of
  `ℓ.map g` (`orbitGenerator_eq_or_eq_neg`, from the uniqueness of the primitive generator of a
  rank-one free `ℤ`-submodule). The sign is real: `g` may reverse the chosen generator. With the
  isometry identity on `L(ℝ)` (`associated_realifiedEquiv`, transported from the rational points by
  `span_range_rationalPoint`) this makes `realifiedEquiv g` permute the forms `normalForm Q (gen ℓ)`
  up to `±1`, and since the cells of `Σ(H)` are indexed by *all* sign patterns, a sign flip of one
  form is absorbed by reindexing the patterns
  (`arrangementDecomposition_coneMap_of_equivariant`).
* `example43b_of_orbitFamily` is the two together: the setting of Example 4.3, `Σ(H)`, and the
  statement of (b) for a `Γ`-finite `H`.

`Γ` is carried as a set (`Γ : Set (V ≃ₗ[ℚ] V)`) throughout this file, so the invariance statements
take closure under composition and inverse as hypotheses — `Γ` is a subgroup of `O(L(ℚ))` in the
source. The locally rational statement needs neither. -/

section Example43b

/-- The real form of a `ℚ`-linear equivalence: the base change of `g` to `ℝ`, i.e. the action of
`g ∈ Γ` on `L(ℝ) = ℝ ⊗[ℚ] L` (Looijenga, Example 4.3, p. 17). -/
noncomputable def realifiedEquiv (g : V ≃ₗ[ℚ] V) : (realified V) ≃ₗ[ℝ] (realified V) :=
  g.baseChange ℚ ℝ

omit [Module.Finite ℚ V] in
theorem realifiedEquiv_rationalPoint (g : V ≃ₗ[ℚ] V) (v : V) :
    realifiedEquiv g (rationalPoint v) = rationalPoint (g v) := by
  rw [realifiedEquiv, rationalPoint_apply, rationalPoint_apply, LinearEquiv.baseChange_tmul]

omit [Module.Finite ℚ V] in
theorem isRationalEquiv_realifiedEquiv (g : V ≃ₗ[ℚ] V) : IsRationalEquiv (realifiedEquiv g) :=
  ⟨g, realifiedEquiv_rationalPoint g⟩

omit [Module.Finite ℚ V] in
/-- The rational points span `L(ℝ)` over `ℝ`: a pure tensor is a real multiple of a rational
point. Used to transport identities of linear forms from `L(ℚ)` to `L(ℝ)`. -/
theorem span_range_rationalPoint :
    Submodule.span ℝ (Set.range (rationalPoint (V := V))) = ⊤ := by
  refine Submodule.eq_top_iff'.2 fun x => ?_
  induction x using TensorProduct.inductionOn with
  | tmul r v =>
    rw [TensorProduct.tmul_eq_smul_one_tmul]
    exact Submodule.smul_mem _ r (Submodule.subset_span ⟨v, rfl⟩)
  | add x y hx hy => exact Submodule.add_mem _ hx hy

omit [Module.Finite ℚ V] in
/-- **An isometry of `Γ` is an isometry of the associated form on `L(ℝ)`**: both sides are linear in
the second argument and agree on the rational points (`hBQ`, `hg`), which span `L(ℝ)`. -/
theorem associated_realifiedEquiv {Q : QuadraticForm ℝ (realified V)}
    {BQ : LinearMap.BilinForm ℚ V} {g : V ≃ₗ[ℚ] V}
    (hBQ : ∀ u w : V, (associated Q) (rationalPoint u) (rationalPoint w) = (BQ u w : ℝ))
    (hg : ∀ x y : V, BQ (g x) (g y) = BQ x y) (v : V) (y : realified V) :
    (associated Q) (rationalPoint (g v)) (realifiedEquiv g y)
      = (associated Q) (rationalPoint v) y := by
  let F : (realified V) →ₗ[ℝ] ℝ :=
    ((associated Q) (rationalPoint (g v))).comp (realifiedEquiv g).toLinearMap -
      (associated Q) (rationalPoint v)
  have hF : ∀ x : V, F (rationalPoint x) = 0 := by
    intro x
    change (associated Q) (rationalPoint (g v)) (realifiedEquiv g (rationalPoint x))
      - (associated Q) (rationalPoint v) (rationalPoint x) = 0
    rw [realifiedEquiv_rationalPoint, hBQ (g v) (g x), hBQ v x, hg, sub_self]
  have hzero : F = 0 := by
    have hle : Submodule.span ℝ (Set.range (rationalPoint (V := V))) ≤ F.ker := by
      rw [Submodule.span_le]
      rintro - ⟨x, rfl⟩
      simpa using hF x
    rw [span_range_rationalPoint] at hle
    have hker : F.ker = ⊤ := top_le_iff.1 hle
    exact LinearMap.ext fun z => by
      have hz : z ∈ F.ker := by rw [hker]; exact Submodule.mem_top
      simpa using hz
  have h := congrArg (fun f : (realified V) →ₗ[ℝ] ℝ => f y) hzero
  simpa [F, sub_eq_zero] using h

omit [Module.Finite ℚ V] in
/-- **A family of forms permuted by an equivalence permutes its cells**, one direction: if
`ψ (ρ i) (e y) = d i · ψ i y`, the sign of `ψ j` at `x` is the sign of `ψ (ρ⁻¹ j)` at `e⁻¹ x`. -/
theorem cell_le_coneMap_of_equivariant {ι : Type*} {ψ : ι → (realified V) →L[ℝ] ℝ}
    {e : (realified V) ≃ₗ[ℝ] (realified V)} {ρ : ι ≃ ι} {d : ι → ℝ}
    (hψ : ∀ i (y : realified V), ψ (ρ i) (e y) = d i * ψ i y) (s : ι → SignType) :
    coneMap e (arrangementCone ψ s) ≤
      arrangementCone ψ (fun j => SignType.sign (d (ρ.symm j)) * s (ρ.symm j)) := by
  intro x hx
  rw [mem_coneMap, mem_arrangementCone_iff_specializes (φ := ψ)] at hx
  rw [mem_arrangementCone_iff_specializes (φ := ψ)]
  intro j
  have h1 : ψ j x = d (ρ.symm j) * ψ (ρ.symm j) (e.symm x) := by
    have h2 := hψ (ρ.symm j) (e.symm x)
    simpa using h2
  rw [h1, sign_mul]
  rcases hx (ρ.symm j) with h0 | h0
  · rw [h0, mul_zero]
    exact Or.inl rfl
  · rw [h0]
    exact Or.inr rfl

omit [Module.Finite ℚ V] in
/-- **An equivalence that permutes the forms up to nonzero scalars permutes the cells of the
arrangement**: the pattern's signs are carried along, `s j` becoming `sign (c j) * s j`. The
reverse inclusion is the same statement at `e.symm` with the inverse scalars. -/
theorem coneMap_arrangementCone_of_equivariant {ι : Type*} {φ : ι → (realified V) →L[ℝ] ℝ}
    {e : (realified V) ≃ₗ[ℝ] (realified V)} {ρ : ι ≃ ι} {c : ι → ℝ} (hc : ∀ i, c i ≠ 0)
    (hφ : ∀ i (y : realified V), φ (ρ i) (e y) = c i * φ i y) (s : ι → SignType) :
    coneMap e (arrangementCone φ s) =
      arrangementCone φ (fun j => SignType.sign (c (ρ.symm j)) * s (ρ.symm j)) := by
  set t : ι → SignType := fun j => SignType.sign (c (ρ.symm j)) * s (ρ.symm j) with ht
  have hpair : ∀ i, SignType.sign ((c i)⁻¹) * SignType.sign (c i) = 1 := by
    intro i
    rw [← sign_mul, inv_mul_cancel₀ (hc i)]
    simp
  refine le_antisymm (cell_le_coneMap_of_equivariant hφ s) ?_
  have hφ' : ∀ i (y : realified V),
      φ (ρ.symm i) (e.symm y) = (c (ρ.symm i))⁻¹ * φ i y := by
    intro i y
    have h2 : φ i y = c (ρ.symm i) * φ (ρ.symm i) (e.symm y) := by
      simpa using hφ (ρ.symm i) (e.symm y)
    rw [h2, inv_mul_cancel_left₀ (hc (ρ.symm i))]
  have hpat : (fun j => SignType.sign ((c (ρ.symm ((ρ.symm).symm j)))⁻¹) *
      t ((ρ.symm).symm j)) = s := by
    funext j
    simp only [Equiv.symm_symm, ht]
    rw [show ρ.symm (ρ j) = j from Equiv.symm_apply_apply ρ j, ← mul_assoc, hpair j, one_mul]
  have hle := cell_le_coneMap_of_equivariant (e := e.symm) (ρ := ρ.symm)
    (d := fun i => (c (ρ.symm i))⁻¹) hφ' t
  rw [hpat] at hle
  have hmono := coneMap_mono (e := e) hle
  rwa [coneMap_coneMap_symm] at hmono

omit [Module.Finite ℚ V] in
/-- **An equivalence permuting the forms leaves the decomposition `Σ(H)` fixed.** -/
theorem arrangementDecomposition_coneMap_of_equivariant {ι : Type*}
    {φ : ι → (realified V) →L[ℝ] ℝ} {e : (realified V) ≃ₗ[ℝ] (realified V)} {ρ : ι ≃ ι}
    {c : ι → ℝ} (hc : ∀ i, c i ≠ 0)
    (hφ : ∀ i (y : realified V), φ (ρ i) (e y) = c i * φ i y)
    {Cplus : PointedCone ℝ (realified V)} (hC : coneMap e Cplus = Cplus) :
    coneMap e '' arrangementDecomposition φ Cplus = arrangementDecomposition φ Cplus := by
  have hsq : ∀ a : SignType, a ≠ 0 → a * a = 1 := by
    rintro (_ | _ | _) h <;> simp_all
  refine Set.Subset.antisymm ?_ ?_
  · rintro - ⟨σ, ⟨s, rfl⟩, rfl⟩
    refine ⟨fun j => SignType.sign (c (ρ.symm j)) * s (ρ.symm j), ?_⟩
    rw [coneMap_inf, hC, coneMap_arrangementCone_of_equivariant hc hφ s]
  · rintro - ⟨u, rfl⟩
    have hpat : (fun j => SignType.sign (c (ρ.symm j)) * (SignType.sign (c (ρ.symm j)) *
        u (ρ (ρ.symm j)))) = u := by
      funext j
      rw [show ρ (ρ.symm j) = j from Equiv.apply_symm_apply ρ j, ← mul_assoc,
        hsq _ (fun h => hc _ (sign_eq_zero_iff.1 h)), one_mul]
    refine ⟨arrangementCone φ (fun i => SignType.sign (c i) * u (ρ i)) ⊓ Cplus,
      ⟨fun i => SignType.sign (c i) * u (ρ i), rfl⟩, ?_⟩
    rw [coneMap_inf, hC, coneMap_arrangementCone_of_equivariant hc hφ]
    rw [hpat]

omit [Module.Finite ℚ V] in
/-- The image of a hyperplane of the family under a member of `Γ`, as a hyperplane of the family:
composition of the two maps, in the order `Submodule.map_comp` states it. -/
theorem map_map_eq_map_trans {ℓ : Submodule ℚ V} {f g : V ≃ₗ[ℚ] V} :
    (ℓ.map (f : V →ₗ[ℚ] V)).map (g : V →ₗ[ℚ] V)
      = ℓ.map ((f.trans g : V ≃ₗ[ℚ] V) : V →ₗ[ℚ] V) := by
  have hcomp : ((f.trans g : V ≃ₗ[ℚ] V) : V →ₗ[ℚ] V)
      = (g : V →ₗ[ℚ] V).comp (f : V →ₗ[ℚ] V) := by
    ext x
    rfl
  rw [hcomp, ← Submodule.map_comp]

/-- **`Γ` acts on the orbit family of `H₀`** by carrying a hyperplane to its image. `Γ` is a set in
this file and a subgroup in the source, so closure under composition and inverse is carried. -/
noncomputable def orbitFamilyMap {H₀ : Finset (Submodule ℚ V)} {Γ : Set (V ≃ₗ[ℚ] V)}
    (hΓcomp : ∀ f ∈ Γ, ∀ g ∈ Γ, f.trans g ∈ Γ) (hΓinv : ∀ g ∈ Γ, g.symm ∈ Γ)
    {g : V ≃ₗ[ℚ] V} (hg : g ∈ Γ) : ↥(orbitFamily H₀ Γ) ≃ ↥(orbitFamily H₀ Γ) where
  toFun ℓ := ⟨ℓ.1.map (g : V →ₗ[ℚ] V), by
    obtain ⟨ℓ₀, h₀, f, hf, hℓ⟩ := mem_orbitFamily.1 ℓ.2
    exact mem_orbitFamily.2 ⟨ℓ₀, h₀, f.trans g, hΓcomp f hf g hg, by
      rw [hℓ]; exact map_map_eq_map_trans⟩⟩
  invFun ℓ := ⟨ℓ.1.map ((g.symm : V ≃ₗ[ℚ] V) : V →ₗ[ℚ] V), by
    obtain ⟨ℓ₀, h₀, f, hf, hℓ⟩ := mem_orbitFamily.1 ℓ.2
    exact mem_orbitFamily.2 ⟨ℓ₀, h₀, f.trans g.symm, hΓcomp f hf g.symm (hΓinv g hg), by
      rw [hℓ]; exact map_map_eq_map_trans⟩⟩
  left_inv ℓ := by
    refine Subtype.ext ?_
    change ((ℓ.1.map (g : V →ₗ[ℚ] V)).map ((g.symm : V ≃ₗ[ℚ] V) : V →ₗ[ℚ] V)) = ℓ.1
    rw [map_map_eq_map_trans]
    have hid : ((g.trans g.symm : V ≃ₗ[ℚ] V) : V →ₗ[ℚ] V) = LinearMap.id := by
      ext x
      simp
    rw [hid, Submodule.map_id]
  right_inv ℓ := by
    refine Subtype.ext ?_
    change ((ℓ.1.map ((g.symm : V ≃ₗ[ℚ] V) : V →ₗ[ℚ] V)).map (g : V →ₗ[ℚ] V)) = ℓ.1
    rw [map_map_eq_map_trans]
    have hid : ((g.symm.trans g : V ≃ₗ[ℚ] V) : V →ₗ[ℚ] V) = LinearMap.id := by
      ext x
      simp
    rw [hid, Submodule.map_id]

omit [Module.Finite ℚ V] in
/-- **The generator of a lattice cut goes to `±` the generator of the image cut**: `g ∈ Γ` with
`g(Λ) = Λ` carries `Λ ⊓ ℓ` onto `Λ ⊓ ℓ.map g`, and the generator of a rank-one free `ℤ`-submodule
is unique up to sign (Looijenga, Example 4.3 (b), p. 18). -/
theorem orbitGenerator_eq_or_eq_neg {Λ : Submodule ℤ V} {H₀ : Finset (Submodule ℚ V)}
    {Γ : Set (V ≃ₗ[ℚ] V)} {gen : ↥(orbitFamily H₀ Γ) → V}
    (hgen : ∀ ℓ, gen ℓ ≠ 0 ∧ Λ ⊓ ℓ.1.restrictScalars ℤ = Submodule.span ℤ ({gen ℓ} : Set V))
    (hΓcomp : ∀ f ∈ Γ, ∀ g ∈ Γ, f.trans g ∈ Γ) (hΓinv : ∀ g ∈ Γ, g.symm ∈ Γ)
    {g : V ≃ₗ[ℚ] V} (hg : g ∈ Γ)
    (hΛ : Submodule.map ((g : V →ₗ[ℚ] V).restrictScalars ℤ) Λ = Λ)
    (ℓ : ↥(orbitFamily H₀ Γ)) :
    gen (orbitFamilyMap hΓcomp hΓinv hg ℓ) = g (gen ℓ) ∨
      gen (orbitFamilyMap hΓcomp hΓinv hg ℓ) = -(g (gen ℓ)) := by
  have h1 : Λ ⊓ ((ℓ.1.map (g : V →ₗ[ℚ] V)).restrictScalars ℤ)
      = Submodule.span ℤ ({gen (orbitFamilyMap hΓcomp hΓinv hg ℓ)} : Set V) :=
    (hgen (orbitFamilyMap hΓcomp hΓinv hg ℓ)).2
  have h2 : Λ ⊓ ((ℓ.1.map (g : V →ₗ[ℚ] V)).restrictScalars ℤ)
      = Submodule.span ℤ ({g (gen ℓ)} : Set V) := by
    rw [← map_inf_restrictScalars (Λ := Λ) (e := g) hΛ ℓ, (hgen ℓ).2, Submodule.map_span]
    simp
  have hg0 : g (gen ℓ) ≠ 0 :=
    fun h => (hgen ℓ).1 (g.injective (by rw [h, map_zero]))
  exact eq_or_eq_neg_of_span_singleton_eq (h2.symm.trans h1) hg0

omit [Module.Finite ℚ V] in
theorem normalForm_neg (Q : QuadraticForm ℝ (realified V)) (v : V) :
    normalForm Q (-v) = -normalForm Q v := by
  ext z
  simp [normalForm_apply]

omit [Module.Finite ℚ V] in
open Classical in
/-- **`Γ` permutes the forms of `Σ(H)` up to sign**: the form of the generator of `ℓ.map g` is `±`
the form of `g (gen ℓ)`, and the latter is the form of `gen ℓ` transported along `realifiedEquiv g`
(`associated_realifiedEquiv`). -/
theorem normalForm_orbitFamily_equivariant {Q : QuadraticForm ℝ (realified V)}
    {BQ : LinearMap.BilinForm ℚ V} {Λ : Submodule ℤ V} {H₀ : Finset (Submodule ℚ V)}
    {Γ : Set (V ≃ₗ[ℚ] V)} {gen : ↥(orbitFamily H₀ Γ) → V}
    (hgen : ∀ ℓ, gen ℓ ≠ 0 ∧ Λ ⊓ ℓ.1.restrictScalars ℤ = Submodule.span ℤ ({gen ℓ} : Set V))
    (hΓcomp : ∀ f ∈ Γ, ∀ g ∈ Γ, f.trans g ∈ Γ) (hΓinv : ∀ g ∈ Γ, g.symm ∈ Γ)
    (hΓΛ : ∀ g ∈ Γ, Submodule.map ((g : V →ₗ[ℚ] V).restrictScalars ℤ) Λ = Λ)
    (hBQ : ∀ u w : V, (associated Q) (rationalPoint u) (rationalPoint w) = (BQ u w : ℝ))
    (hΓiso : ∀ g ∈ Γ, ∀ x y, BQ (g x) (g y) = BQ x y)
    {g : V ≃ₗ[ℚ] V} (hg : g ∈ Γ) (ℓ : ↥(orbitFamily H₀ Γ)) (y : realified V) :
    normalForm Q (gen (orbitFamilyMap hΓcomp hΓinv hg ℓ)) (realifiedEquiv g y)
      = (if gen (orbitFamilyMap hΓcomp hΓinv hg ℓ) = g (gen ℓ) then 1 else -1) *
        normalForm Q (gen ℓ) y := by
  classical
  have hiso : normalForm Q (g (gen ℓ)) (realifiedEquiv g y) = normalForm Q (gen ℓ) y :=
    associated_realifiedEquiv hBQ (hΓiso g hg) (gen ℓ) y
  rcases orbitGenerator_eq_or_eq_neg hgen hΓcomp hΓinv hg (hΓΛ g hg) ℓ with h | h
  · rw [ite_eq_left h, h, one_mul]
    exact hiso
  · have hne : ¬ (gen (orbitFamilyMap hΓcomp hΓinv hg ℓ) = g (gen ℓ)) := by
      intro hh
      have hneg : g (gen ℓ) = -g (gen ℓ) := hh ▸ h
      have htwice : (2 : ℚ) • g (gen ℓ) = 0 := by
        rw [two_smul]
        nth_rewrite 1 [hneg]
        exact neg_add_cancel _
      have hzero : g (gen ℓ) = 0 := by
        rcases smul_eq_zero.1 htwice with h3 | h3
        · exact absurd h3 (by norm_num)
        · exact h3
      exact (fun h0 => (hgen ℓ).1 (g.injective (by rw [h0, map_zero]))) hzero
    have hval : normalForm Q (gen (orbitFamilyMap hΓcomp hΓinv hg ℓ)) (realifiedEquiv g y)
        = -normalForm Q (g (gen ℓ)) (realifiedEquiv g y) := by
      rw [h, normalForm_neg]
      simp
    rw [ite_eq_right hne, hval, hiso]
    norm_num

/-- **Looijenga, Example 4.3 (b), pp. 17-18, with no finiteness hypothesis**: for `H` the union of
the `Γ`-orbits of finitely many `ℚ`-hyperplanes, `Σ(H)` is a locally rational decomposition of
`C₊` (`arrangementDecomposition_isLocallyRational` composed with
`cutsFinitelyOnRational_orbitFamily`, the section above). -/
theorem arrangementDecomposition_isLocallyRational_of_orbitFamily
    {Q : QuadraticForm ℝ (realified V)} (hpos : sigPos Q = 1) (hnd : Q.Nondegenerate)
    {BQ : LinearMap.BilinForm ℚ V} (hBQsym : BQ.IsSymm) (hBQnd : BQ.Nondegenerate)
    (hBQ : ∀ u w : V, (associated Q) (rationalPoint u) (rationalPoint w) = (BQ u w : ℝ))
    {Cplus : PointedCone ℝ (realified V)} (hsal : (Cplus : ConvexCone ℝ (realified V)).Salient)
    {t : realified V} (ht : 0 < Q t)
    (hsheet : ∀ v : V, rationalPoint v ∈ Cplus →
      0 ≤ Q (rationalPoint v) ∧ 0 ≤ (associated Q) (rationalPoint v) t)
    {ι : Type*} [Fintype ι] [DecidableEq ι] {bs : Module.Basis ι ℚ V}
    (Γ : Set (V ≃ₗ[ℚ] V)) (H₀ : Finset (Submodule ℚ V))
    (hΓΛ : ∀ e ∈ Γ, Submodule.map ((e : V →ₗ[ℚ] V).restrictScalars ℤ)
      (Submodule.span ℤ (Set.range bs)) = Submodule.span ℤ (Set.range bs))
    (hΓiso : ∀ e ∈ Γ, ∀ x y, BQ (e x) (e y) = BQ x y)
    (hH₀ : ∀ ℓ₀ ∈ H₀, ∃ v : V, v ≠ 0 ∧
      Submodule.span ℤ (Set.range bs) ⊓ ℓ₀.restrictScalars ℤ = Submodule.span ℤ ({v} : Set V))
    (hint : ∀ x ∈ Submodule.span ℤ (Set.range bs), ∀ y ∈ Submodule.span ℤ (Set.range bs),
      ∃ n : ℤ, BQ x y = (n : ℚ)) :
    IsLocallyRationalDecomposition Cplus
      (arrangementDecomposition (fun ℓ : ↥(orbitFamily H₀ Γ) =>
        normalForm Q (Classical.choose (exists_generator_of_orbitFamily
          (Submodule.span ℤ (Set.range bs)) H₀ Γ hΓΛ hH₀) ℓ)) Cplus) := by
  let gen : ↥(orbitFamily H₀ Γ) → V := Classical.choose
    (exists_generator_of_orbitFamily (Submodule.span ℤ (Set.range bs)) H₀ Γ hΓΛ hH₀)
  have hcut : CutsFinitelyOnRational Cplus (fun ℓ => normalForm Q (gen ℓ)) :=
    cutsFinitelyOnRational_orbitFamily hpos hnd hBQsym hBQnd hBQ hsal ht hsheet Γ H₀ hΓΛ hΓiso
      hH₀ hint
  have hφ : ∀ ℓ : ↥(orbitFamily H₀ Γ), IsRationalForm (normalForm Q (gen ℓ)).toLinearMap :=
    fun ℓ => ⟨BQ (gen ℓ), fun v => hBQ (gen ℓ) v⟩
  exact arrangementDecomposition_isLocallyRational hsal hφ hcut

omit [Module.Finite ℚ V] in
/-- **Looijenga, Example 4.3 (b), pp. 17-18: `Σ(H)` is `Γ`-invariant**, for `H` the union of the
`Γ`-orbits of finitely many `ℚ`-hyperplanes. -/
theorem isGammaInvariant_arrangementDecomposition_of_orbitFamily
    {Q : QuadraticForm ℝ (realified V)} {BQ : LinearMap.BilinForm ℚ V}
    {ι : Type*} [Fintype ι] [DecidableEq ι] {bs : Module.Basis ι ℚ V}
    (Γ : Set (V ≃ₗ[ℚ] V)) (H₀ : Finset (Submodule ℚ V))
    {gen : ↥(orbitFamily H₀ Γ) → V}
    (hgen : ∀ ℓ, gen ℓ ≠ 0 ∧
      Submodule.span ℤ (Set.range bs) ⊓ ℓ.1.restrictScalars ℤ
        = Submodule.span ℤ ({gen ℓ} : Set V))
    (hΓcomp : ∀ f ∈ Γ, ∀ g ∈ Γ, f.trans g ∈ Γ) (hΓinv : ∀ g ∈ Γ, g.symm ∈ Γ)
    (hΓΛ : ∀ e ∈ Γ, Submodule.map ((e : V →ₗ[ℚ] V).restrictScalars ℤ)
      (Submodule.span ℤ (Set.range bs)) = Submodule.span ℤ (Set.range bs))
    (hBQ : ∀ u w : V, (associated Q) (rationalPoint u) (rationalPoint w) = (BQ u w : ℝ))
    (hΓiso : ∀ e ∈ Γ, ∀ x y, BQ (e x) (e y) = BQ x y)
    {Cplus : PointedCone ℝ (realified V)}
    (hCplus : ∀ g ∈ Γ, coneMap (realifiedEquiv g) Cplus = Cplus) :
    IsGammaInvariant (realifiedEquiv '' Γ)
      (arrangementDecomposition (fun ℓ : ↥(orbitFamily H₀ Γ) =>
        normalForm Q (gen ℓ)) Cplus) := by
  classical
  intro ê hê
  obtain ⟨g, hg, rfl⟩ := hê
  exact arrangementDecomposition_coneMap_of_equivariant
    (ρ := orbitFamilyMap hΓcomp hΓinv hg)
    (c := fun ℓ => if gen (orbitFamilyMap hΓcomp hΓinv hg ℓ) = g (gen ℓ) then 1 else -1)
    (fun ℓ => by split <;> norm_num)
    (fun ℓ y => normalForm_orbitFamily_equivariant hgen hΓcomp hΓinv hΓΛ hBQ hΓiso hg ℓ y)
    (hCplus g hg)

/-- **Looijenga, Example 4.3 (b), pp. 17-18** (`.tmp-sources/looijenga-math0201218v2.md:491`; the
hypotheses are those of Example 4.3, p. 17, line 487): for a lattice of signature `(1, n - 1)`, `Γ`
preserving it, and `H` the union of the `Γ`-orbits of finitely many `ℚ`-hyperplanes, `Σ(H)` is a
`Γ`-invariant locally rational decomposition of `C₊`. -/
theorem example43b_of_orbitFamily
    {Q : QuadraticForm ℝ (realified V)} (hpos : sigPos Q = 1) (hnd : Q.Nondegenerate)
    {BQ : LinearMap.BilinForm ℚ V} (hBQsym : BQ.IsSymm) (hBQnd : BQ.Nondegenerate)
    (hBQ : ∀ u w : V, (associated Q) (rationalPoint u) (rationalPoint w) = (BQ u w : ℝ))
    {Cplus : PointedCone ℝ (realified V)} (hsal : (Cplus : ConvexCone ℝ (realified V)).Salient)
    {t : realified V} (ht : 0 < Q t)
    (hsheet : ∀ v : V, rationalPoint v ∈ Cplus →
      0 ≤ Q (rationalPoint v) ∧ 0 ≤ (associated Q) (rationalPoint v) t)
    {ι : Type*} [Fintype ι] [DecidableEq ι] {bs : Module.Basis ι ℚ V}
    (Γ : Set (V ≃ₗ[ℚ] V)) (H₀ : Finset (Submodule ℚ V))
    (hΓcomp : ∀ f ∈ Γ, ∀ g ∈ Γ, f.trans g ∈ Γ) (hΓinv : ∀ g ∈ Γ, g.symm ∈ Γ)
    (hΓΛ : ∀ e ∈ Γ, Submodule.map ((e : V →ₗ[ℚ] V).restrictScalars ℤ)
      (Submodule.span ℤ (Set.range bs)) = Submodule.span ℤ (Set.range bs))
    (hΓiso : ∀ e ∈ Γ, ∀ x y, BQ (e x) (e y) = BQ x y)
    (hH₀ : ∀ ℓ₀ ∈ H₀, ∃ v : V, v ≠ 0 ∧
      Submodule.span ℤ (Set.range bs) ⊓ ℓ₀.restrictScalars ℤ = Submodule.span ℤ ({v} : Set V))
    (hint : ∀ x ∈ Submodule.span ℤ (Set.range bs), ∀ y ∈ Submodule.span ℤ (Set.range bs),
      ∃ n : ℤ, BQ x y = (n : ℚ))
    (hCplus : ∀ g ∈ Γ, coneMap (realifiedEquiv g) Cplus = Cplus) :
    IsLocallyRationalDecomposition Cplus
        (arrangementDecomposition (fun ℓ : ↥(orbitFamily H₀ Γ) =>
          normalForm Q (Classical.choose (exists_generator_of_orbitFamily
            (Submodule.span ℤ (Set.range bs)) H₀ Γ hΓΛ hH₀) ℓ)) Cplus) ∧
      IsGammaInvariant (realifiedEquiv '' Γ)
        (arrangementDecomposition (fun ℓ : ↥(orbitFamily H₀ Γ) =>
          normalForm Q (Classical.choose (exists_generator_of_orbitFamily
            (Submodule.span ℤ (Set.range bs)) H₀ Γ hΓΛ hH₀) ℓ)) Cplus) :=
  ⟨arrangementDecomposition_isLocallyRational_of_orbitFamily hpos hnd hBQsym hBQnd hBQ hsal ht
      hsheet Γ H₀ hΓΛ hΓiso hH₀ hint,
    isGammaInvariant_arrangementDecomposition_of_orbitFamily Γ H₀
      (gen := Classical.choose (exists_generator_of_orbitFamily
        (Submodule.span ℤ (Set.range bs)) H₀ Γ hΓΛ hH₀))
      (Classical.choose_spec (exists_generator_of_orbitFamily
        (Submodule.span ℤ (Set.range bs)) H₀ Γ hΓΛ hH₀))
      hΓcomp hΓinv hΓΛ hBQ hΓiso hCplus⟩

end Example43b

end FiniteOrbits

/-! ## The support space of an isotropic half line in the facial decomposition

Looijenga, Lemma-Definition 4.5, p. 19, and the list after its proof: "the support spaces of `Σ(bb)`
are `V`, `{0}` and the hyperplanes orthogonal to a `ℚ`-isotropic line." This section carries the
isotropic item of that list in full, both inclusions.

The description the source reads off the affine model is `L_σ = I^⊥` when `σ` spans the isotropic
line `I`, and for the facial decomposition the only members above `σ` that meet `C` are the closed
sheet and `σ` itself, so `supportSpace` is taken at `τ = C₊` alone. The upper bound `L_σ ⊆ I^⊥` is
`supportSpace_le_ker_associated_of_isotropic` (the form `y ↦ e · y` is nonnegative on the sheet and
vanishes on `σ`). The lower bound is where the sheet being self-dual enters: a form nonnegative on
the whole closed sheet has `Q ≥ 0` value (`quadratic_nonneg_of_forall_mem_closedSheet_nonneg`, whose
proof is a two-dimensional construction — if `Q φ < 0` the vector `√(-Q ψ/Q t) • t + ψ`, with `ψ`
the projection of `φ` off `t`, is on the light cone of the sheet and pairs negatively with `φ`), so
it lies in the closed sheet, and a form of the sheet vanishing on the isotropic `e` is a multiple of
`e` (`exists_smul_of_associated_eq_zero_of_mem_closedSheet_self`, the general form of the rational
statement `exists_smul_of_associated_eq_zero_of_mem_closedSheet`) — hence vanishes on `I^⊥`. -/

section FacialDecompositionSupportSpace

variable {Q : QuadraticForm ℝ (realified V)} [Module.Finite ℚ V]

/-- **A form nonnegative on the closed sheet has nonnegative value.** -/
theorem quadratic_nonneg_of_forall_mem_closedSheet_nonneg (hpos : sigPos Q = 1) {t : realified V}
    (ht : 0 < Q t) {phi : realified V}
    (hphi : ∀ y ∈ closedSheet Q hpos ht, 0 ≤ (associated Q) phi y) : 0 ≤ Q phi := by
  by_contra hneg
  have hneg' : Q phi < 0 := lt_of_not_ge hneg
  have ht_mem : t ∈ closedSheet Q hpos ht :=
    (mem_closedSheet hpos ht).2 ⟨ht.le, by rw [associated_self_apply]; exact ht.le⟩
  set b : ℝ := (associated Q) phi t with hb
  have hb0 : 0 ≤ b := hphi t ht_mem
  set psi : realified V := spatialPart Q t phi with hpsi
  have hQt : Q t ≠ 0 := ht.ne'
  have hpsit : (associated Q) psi t = 0 := by
    rw [hpsi]; exact associated_spatialPart_right Q hQt phi
  have hQpsi : Q psi = Q phi - b ^ 2 / Q t := by
    rw [hpsi]; exact quadratic_spatialPart Q hQt phi
  set u : ℝ := -(Q psi) with hu_def
  have hu_eq : u = b ^ 2 / Q t - Q phi := by
    rw [hu_def, hQpsi]; ring
  have hu0 : 0 < u := by
    rw [hu_eq]
    linarith [hneg', div_nonneg (sq_nonneg b) ht.le]
  have hbsq : b ^ 2 < u * Q t := by
    have h1 : u * Q t = b ^ 2 - Q phi * Q t := by
      rw [hu_eq]; field_simp
    rw [h1]; nlinarith [hneg', ht]
  have hb_lt : b < Real.sqrt (u * Q t) := by
    calc b = Real.sqrt (b ^ 2) := (Real.sqrt_sq hb0).symm
      _ < Real.sqrt (u * Q t) := Real.sqrt_lt_sqrt (by nlinarith) hbsq
  set c : ℝ := Real.sqrt (u / Q t) with hc_def
  have hcpos : 0 < c := Real.sqrt_pos.2 (div_pos hu0 ht)
  have hcsq : c ^ 2 = u / Q t := Real.sq_sqrt (div_pos hu0 ht).le
  set v : realified V := c • t + psi with hv_def
  have hQv : Q v = 0 := by
    have hexp : Q (c • t + psi) = c ^ 2 * Q t + 2 * c * ((associated Q) psi t) + Q psi := by
      rw [show c • t + psi = c • t + (1 : ℝ) • psi by simp, quadratic_expand,
        associated_comm Q t psi]
      ring
    have hc2 : c ^ 2 * Q t = u := by rw [hcsq]; field_simp
    rw [hv_def, hexp, hpsit, hc2]
    simp only [mul_zero, add_zero]
    rw [hu_def]; ring
  have hvt : 0 ≤ (associated Q) v t := by
    have h1 : (associated Q) v t = c * Q t + (associated Q) psi t := by
      rw [hv_def]
      simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
        associated_self_apply]
    rw [h1, hpsit, add_zero]
    exact mul_nonneg hcpos.le ht.le
  have hv_mem : v ∈ closedSheet Q hpos ht := (mem_closedSheet hpos ht).2 ⟨by rw [hQv], hvt⟩
  have hpair : (associated Q) phi v = c * b + Q psi := by
    have h1 : (associated Q) phi v = c * ((associated Q) phi t) + (associated Q) phi psi := by
      rw [hv_def]
      simp only [map_add, map_smul, smul_eq_mul]
    have h2 : (associated Q) phi psi = Q psi := by
      have hdec : phi = psi + (b / Q t) • t := by
        rw [hpsi, spatialPart, hb]
        abel
      rw [hdec]
      simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
      rw [associated_comm Q t psi, hpsit, mul_zero, add_zero, associated_self_apply]
    rw [h1, h2, hb]
  have hsqrt : Real.sqrt (u / Q t) * Real.sqrt (u * Q t) = u := by
    rw [← Real.sqrt_mul (div_nonneg hu0.le ht.le)]
    have h2 : u / Q t * (u * Q t) = u ^ 2 := by field_simp
    rw [h2, Real.sqrt_sq hu0.le]
  have hcb : c * b < u := by
    have hpos_sqrt : 0 < Real.sqrt (u / Q t) := Real.sqrt_pos.2 (div_pos hu0 ht)
    calc c * b = Real.sqrt (u / Q t) * b := by rw [hc_def]
      _ < Real.sqrt (u / Q t) * Real.sqrt (u * Q t) := mul_lt_mul_of_pos_left hb_lt hpos_sqrt
      _ = u := hsqrt
  have hneg_pair : (associated Q) phi v < 0 := by
    have hQpsi' : Q psi = -u := by linarith [hu_def]
    rw [hpair, hQpsi']
    linarith
  have := hphi v hv_mem
  linarith

/-- **Two vectors of the closed sheet with vanishing pairing are proportional** — the general form
of `exists_smul_of_associated_eq_zero_of_mem_closedSheet`, which is stated for rational points. -/
theorem exists_smul_of_associated_eq_zero_of_mem_closedSheet_self (hpos : sigPos Q = 1)
    (hnd : Q.Nondegenerate) {t : realified V} (ht : 0 < Q t) {a b : realified V}
    (ha : a ∈ closedSheet Q hpos ht) (hb : b ∈ closedSheet Q hpos ht)
    (hab : (associated Q) a b = 0) (ha0 : a ≠ 0) : ∃ c : ℝ, b = c • a := by
  rcases eq_or_lt_of_le ha.1 with hQa | hQa
  · have hat : 0 < (associated Q) a t := by
      rcases eq_or_lt_of_le ha.2 with h | h
      · exact absurd (eq_zero_of_perp_of_quadratic_eq_zero hpos hnd ht h.symm hQa.symm) ha0
      · exact h
    have hQa0 : Q a = 0 := hQa.symm
    set c : ℝ := (associated Q) b t / (associated Q) a t with hc
    have hwt : (associated Q) (b - c • a) t = 0 := by
      have h1 : (associated Q) (b - c • a) t
          = (associated Q) b t - c * ((associated Q) a t) := by
        rw [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
      rw [h1, hc]
      field_simp
      ring
    have hQw_le : Q (b - c • a) ≤ 0 :=
      quadratic_nonpos_of_associated_eq_zero hpos ht hwt
    have hQw : Q (b - c • a) = Q b := by
      have hsub : b - c • a = (1 : ℝ) • b + (-c) • a := by
        rw [one_smul, sub_eq_add_neg, neg_smul]
      rw [hsub]
      have hexp := quadratic_expand Q 1 (-c) b a
      rw [hexp, associated_comm Q b a, hab, hQa0]
      ring
    have hQb : Q b = 0 := le_antisymm (hQw ▸ hQw_le) hb.1
    have hzero : b - c • a = 0 :=
      eq_zero_of_perp_of_quadratic_eq_zero hpos hnd ht hwt (by rw [hQw, hQb])
    exact ⟨c, sub_eq_zero.1 hzero⟩
  · have hat_pos : 0 < (associated Q) a t := by
      rcases eq_or_lt_of_le ha.2 with h | h
      · exfalso
        have hle := mul_self_le_associated_sq (Q := Q) hpos ht a
        rw [h.symm] at hle
        nlinarith [hQa, ht]
      · exact h
    have hb0 : b = 0 := by
      by_contra hb0
      have ha_open : a ∈ positiveCone.upper Q t := ⟨hQa, hat_pos⟩
      have h := associated_pos_of_mem_upper_of_mem_closedSheet Q hpos hnd ht ha_open hb hb0
      rw [hab] at h
      exact lt_irrefl 0 h
    exact ⟨0, by rw [hb0, zero_smul]⟩

/-- **The support space of an isotropic ray relative to the closed sheet is `I^⊥`**: the isotropic
case of Lemma-Definition 4.5 in full, for the facial decomposition `Σ(bb)` — the source's "the
hyperplanes orthogonal to a `ℚ`-isotropic line" (p. 19). -/
theorem supportSpace_closedSheet_hull_eq_ker (hpos : sigPos Q = 1) (hnd : Q.Nondegenerate)
    {t : realified V} (ht : 0 < Q t) {e : realified V} (he : Q e = 0) (he0 : e ≠ 0)
    (het : 0 ≤ (associated Q) e t) :
    supportSpace (closedSheet Q hpos ht) (PointedCone.hull ℝ ({e} : Set (realified V)))
      = LinearMap.ker (associated Q e) := by
  refine le_antisymm (supportSpace_le_ker_associated_of_isotropic hpos ht he het rfl le_rfl) ?_
  intro x hx
  refine mem_supportSpace.2 fun phi hphi => ?_
  rcases eq_or_ne phi 0 with hzero | hne
  · rw [hzero]; simp
  have ht_mem : t ∈ closedSheet Q hpos ht :=
    (mem_closedSheet hpos ht).2 ⟨ht.le, by rw [associated_self_apply]; exact ht.le⟩
  have hBnd : (associated Q).Nondegenerate :=
    QuadraticMap.nondegenerate_associated_iff.mpr hnd
  set p : realified V := (LinearMap.BilinForm.toDual (associated Q) hBnd).symm phi with hp
  have hp_app : ∀ y : realified V, (associated Q) p y = phi y := by
    intro y
    rw [hp]
    exact LinearMap.BilinForm.apply_toDual_symm_apply phi y
  have hp0 : p ≠ 0 := by
    intro h
    refine hne (LinearMap.ext fun y => ?_)
    rw [← hp_app y, h]
    simp
  have hQp : 0 ≤ Q p :=
    quadratic_nonneg_of_forall_mem_closedSheet_nonneg hpos ht fun y hy => by
      rw [hp_app]; exact hphi.1 y hy
  have hpt : 0 ≤ (associated Q) p t := by
    rw [hp_app]; exact hphi.1 t ht_mem
  have hpe : (associated Q) p e = 0 := by
    rw [hp_app]
    exact hphi.2 e (PointedCone.subset_hull (Set.mem_singleton e))
  obtain ⟨c, hc⟩ := exists_smul_of_associated_eq_zero_of_mem_closedSheet_self hpos hnd ht
    ((mem_closedSheet hpos ht).2 ⟨he.ge, het⟩) ((mem_closedSheet hpos ht).2 ⟨hQp, hpt⟩)
    (by rw [associated_comm]; exact hpe) he0
  have hxe : (associated Q) e x = 0 := hx
  rw [← hp_app x, hc]
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, hxe, mul_zero]

end FacialDecompositionSupportSpace

/-! ## Rational traces along an isotropic boundary ray

LC-09 (2026-11-19): `content:closedSheet isClosed quadratic`,
`content:isotropic ray face quadratic cone`, `content:isotropic face closed cone quadratic form`,
`content:common face recession lineal`, `content:lineal topologicalClosure common face`,
and `content:rational cone mem_nhds interior` found no competing declaration. The proofs below
use this file's `QuadraticMap.continuous_of_moduleTopology` and
`exists_smul_of_associated_eq_zero_of_mem_closedSheet_self` directly. -/

section IsotropicRationalTraces

/-- If every translate `z + r • x` belongs to a cone, then `x` belongs to its closure:
scale the translate at the real parameter `n + 1` by its inverse and take the limit. -/
theorem mem_topologicalClosure_of_forall_add_smul_mem {E : Type*} [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] [ContinuousAdd E] [ContinuousSMul ℝ E]
    {D : PointedCone ℝ E} {z x : E} (h : ∀ r : ℝ, z + r • x ∈ D) :
    x ∈ D.topologicalClosure := by
  let c : ℕ → ℝ := fun n => ((n + 1 : ℕ) : ℝ)
  let f : ℕ → E := fun n => (c n)⁻¹ • (z + c n • x)
  have hc : Filter.Tendsto c Filter.atTop Filter.atTop := by
    apply Filter.tendsto_atTop.2
    intro b
    obtain ⟨n, hn⟩ := exists_nat_ge b
    refine Filter.eventually_atTop.2 ⟨n, fun m hm => ?_⟩
    have hnm : n ≤ m + 1 := hm.trans (Nat.le_succ m)
    have hncast : (n : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by exact_mod_cast hnm
    exact hn.trans hncast
  have hinv : Filter.Tendsto (fun n => (c n)⁻¹) Filter.atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hc
  have hmem (n : ℕ) : f n ∈ D := by
    exact D.smul_mem (inv_nonneg.2 (by positivity : 0 ≤ c n)) (h (c n))
  have heq (n : ℕ) : f n = (c n)⁻¹ • z + x := by
    dsimp [f]
    rw [smul_add, smul_smul]
    have hn : c n ≠ 0 := by positivity
    rw [inv_mul_cancel₀ hn, one_smul]
  have ht : Filter.Tendsto f Filter.atTop (𝓝 x) := by
    have ht' := (hinv.smul_const z).add_const x
    rw [zero_smul, zero_add] at ht'
    exact ht'.congr' (Filter.Eventually.of_forall fun n => (heq n).symm)
  exact mem_closure_of_tendsto ht (Filter.Eventually.of_forall hmem)

variable [Module.Finite ℚ V] {Q : QuadraticForm ℝ (realified V)} {t : realified V}

set_option maxHeartbeats 600000 in
/-- The closed sheet is closed in the finite-dimensional module topology. -/
theorem isClosed_closedSheet_of_moduleTopology (Q : QuadraticForm ℝ (realified V))
    (hpos : sigPos Q = 1) {t : realified V} (ht : 0 < Q t) :
    IsClosed (closedSheet Q hpos ht : Set (realified V)) := by
  have hQ : IsClosed (Q ⁻¹' Set.Ici (0 : ℝ)) :=
    isClosed_Ici.preimage (QuadraticMap.continuous_of_moduleTopology Q)
  have hpair : Continuous (fun x : realified V => (associated Q) x t) :=
    (LinearMap.continuous_bilin_of_moduleTopology (associated Q)).comp
      (continuous_id.prodMk continuous_const)
  have hB : IsClosed ((fun x : realified V => (associated Q) x t) ⁻¹' Set.Ici (0 : ℝ)) :=
    isClosed_Ici.preimage hpair
  exact hQ.inter hB

/-- The rational closure of the closed sheet lies in the closed sheet. -/
theorem rationalClosure_le_closedSheet (hpos : sigPos Q = 1) {ht : 0 < Q t} :
    rationalClosure (closedSheet Q hpos ht) ≤ closedSheet Q hpos ht := by
  rw [rationalClosure_eq_hull]
  refine Submodule.span_le.2 ?_
  rintro x ⟨⟨v, -, rfl⟩, hx⟩
  have hclosed := isClosed_closedSheet_of_moduleTopology Q hpos ht
  rw [show (closedSheet Q hpos ht).closure = closedSheet Q hpos ht from
    hclosed.submodule_topologicalClosure_eq] at hx
  exact hx

/-- An isotropic half line contained in the rational closure of the closed sheet is a face of
it. The pairing with its generator exposes the ray: two sheet vectors with zero pairing are
proportional, and their common time orientation makes the coefficient nonnegative. -/
theorem IsIsotropicHalfLine.isFaceOf_rationalClosure (hpos : sigPos Q = 1)
    (hnd : Q.Nondegenerate) {ht : 0 < Q t} {σ : PointedCone ℝ (realified V)}
    (hσ : IsIsotropicHalfLine Q σ)
    (hσle : σ ≤ rationalClosure (closedSheet Q hpos ht)) :
    σ.IsFaceOf (rationalClosure (closedSheet Q hpos ht)) := by
  obtain ⟨e, he0, heQ, rfl⟩ := hσ
  let Cplus := rationalClosure (closedSheet Q hpos ht)
  have heC : e ∈ Cplus := hσle (PointedCone.subset_hull (Set.mem_singleton e))
  have heSheet : e ∈ closedSheet Q hpos ht := rationalClosure_le_closedSheet hpos heC
  have het : 0 < (associated Q) e t := by
    rw [associated_comm]
    exact associated_pos_of_mem_upper_of_mem_closedSheet Q hpos hnd ht
      ⟨ht, by rw [associated_self_apply]; exact ht⟩ heSheet he0
  have hnonneg : ∀ z ∈ Cplus, 0 ≤ (associated Q) e z := by
    intro z hz
    exact nonneg_associated_of_mem_closedSheet hpos ht heSheet.1 heSheet.2
      (rationalClosure_le_closedSheet hpos hz).1 (rationalClosure_le_closedSheet hpos hz).2
  have hker : Cplus ⊓ PointedCone.ofSubmodule (LinearMap.ker (associated Q e)) =
      PointedCone.hull ℝ ({e} : Set (realified V)) := by
    apply le_antisymm
    · intro z hz
      have hze : (associated Q) e z = 0 := by
        exact hz.2
      obtain ⟨c, hc⟩ := exists_smul_of_associated_eq_zero_of_mem_closedSheet_self hpos hnd ht
        heSheet (rationalClosure_le_closedSheet hpos hz.1) hze he0
      have hct : (associated Q) z t = c * (associated Q) e t := by
        rw [hc, map_smul, LinearMap.smul_apply, smul_eq_mul]
      have hc0 : 0 ≤ c := by
        have hz0 := (rationalClosure_le_closedSheet hpos hz.1).2
        rw [hct] at hz0
        exact nonneg_of_mul_nonneg_left hz0 het
      exact PointedCone.mem_hull_singleton.2 ⟨c, hc0, hc.symm⟩
    · intro z hz
      obtain ⟨c, hc0, hc⟩ := PointedCone.mem_hull_singleton.1 hz
      refine ⟨?_, ?_⟩
      · rw [← hc]
        exact Cplus.smul_mem hc0 heC
      · change (associated Q) e z = 0
        rw [← hc, map_smul, smul_eq_mul, associated_self_apply, heQ, mul_zero]
  rw [← hker]
  exact PointedCone.isFaceOf_inf_ker hnonneg

/-- An isotropic half line is a face of every subcone of the rational closure containing it. -/
theorem IsIsotropicHalfLine.isFaceOf_of_le (hpos : sigPos Q = 1) (hnd : Q.Nondegenerate)
    {ht : 0 < Q t} {σ τ : PointedCone ℝ (realified V)} (hσ : IsIsotropicHalfLine Q σ)
    (hστ : σ ≤ τ) (hτle : τ ≤ rationalClosure (closedSheet Q hpos ht)) :
    σ.IsFaceOf τ := by
  refine ⟨hστ, ?_⟩
  have hface := hσ.isFaceOf_rationalClosure hpos hnd (hστ.trans hτle)
  intro x y a hx hy ha hxy
  exact hface.mem_of_smul_add_mem (hτle hx) (hτle hy) ha hxy

omit [Module.Finite ℚ V] in
/-- Every member of a locally rational decomposition lies below its carrier. -/
theorem IsLocallyRationalDecomposition.le {C : PointedCone ℝ (realified V)}
    {S : Set (PointedCone ℝ (realified V))}
    (hS : IsLocallyRationalDecomposition (rationalClosure C) S)
    {τ : PointedCone ℝ (realified V)} (hτ : τ ∈ S) :
    τ ≤ rationalClosure C := by
  intro z hz
  have hz' : z ∈ (⋃ d ∈ S, (d : Set (realified V))) :=
    Set.mem_iUnion.2 ⟨τ, Set.mem_iUnion.2 ⟨hτ, hz⟩⟩
  rwa [hS.union_eq] at hz'

/-- An isotropic half line below a member of a locally rational decomposition is rational.
Take a rational subcone containing its generator; the ray is a face of the corresponding trace,
and Definition 4.2 makes every such face rational. -/
theorem IsIsotropicHalfLine.isRationalCone_of_le_of_mem (hpos : sigPos Q = 1)
    (hnd : Q.Nondegenerate) {ht : 0 < Q t}
    {S : Set (PointedCone ℝ (realified V))}
    (hS : IsLocallyRationalDecomposition (rationalClosure (closedSheet Q hpos ht)) S)
    {σ τ : PointedCone ℝ (realified V)} (hσ : IsIsotropicHalfLine Q σ)
    (hτ : τ ∈ S) (hστ : σ ≤ τ) : IsRationalCone σ := by
  obtain ⟨e, he0, heQ, rfl⟩ := hσ
  let Cplus := rationalClosure (closedSheet Q hpos ht)
  let ray := PointedCone.hull ℝ ({e} : Set (realified V))
  have hτle : τ ≤ Cplus := hS.le hτ
  have heτ : e ∈ τ := hστ (PointedCone.subset_hull (Set.mem_singleton e))
  have heC : e ∈ Cplus := hτle heτ
  obtain ⟨K, hKrat, hKle, heK⟩ := exists_rationalCone_le_rationalClosure_and_mem heC
  have hface : ray.IsFaceOf τ := IsIsotropicHalfLine.isFaceOf_of_le hpos hnd
    ⟨e, he0, heQ, rfl⟩ hστ hτle
  have hrayK : ray ≤ K := by
    intro z hz
    obtain ⟨c, hc0, hc⟩ := PointedCone.mem_hull_singleton.1 hz
    rw [← hc]
    exact K.smul_mem hc0 heK
  have hfaceTrace : ray.IsFaceOf (τ ⊓ K) := by
    refine ⟨le_inf hστ hrayK, ?_⟩
    intro x y a hx hy ha hxy
    exact hface.mem_of_smul_add_mem hx.1 hy.1 ha hxy
  let R := hS.restriction K hKrat hKle
  have hmem : ray ∈ faceClosure (restrictionTo S K) :=
    mem_faceClosure.2 ⟨τ ⊓ K,
      mem_restrictionTo.2 ⟨τ, hτ, rfl⟩, hfaceTrace⟩
  exact R.isRational ray hmem

/-- The pointed upper sheet lies in the rational closure of the closed sheet. -/
theorem upperZero_le_rationalClosure_closedSheet (hpos : sigPos Q = 1) {ht : 0 < Q t} :
    positiveCone.upperZero hpos ht ≤ rationalClosure (closedSheet Q hpos ht) := by
  intro z hz
  rcases hz with rfl | hz
  · exact zero_mem _
  · apply subset_rationalClosure_of_mem
      ((upperZero_le_closedSheet hpos ht).trans (Submodule.le_topologicalClosure _))
    exact upper_subset_interior_upperZero hpos ht hz

/-- Two upper-sheet points admit a common rational cone neighbourhood below `C₊`, enlarged to
contain a prescribed rational isotropic ray. The join preserves both neighbourhoods. -/
theorem exists_rationalCone_sup_mem_nhds_of_isotropic (hpos : sigPos Q = 1)
    {ht : 0 < Q t} {σ : PointedCone ℝ (realified V)} (hσle : σ ≤ rationalClosure
      (closedSheet Q hpos ht)) (hσrat : IsRationalCone σ) {x y : realified V}
    (hx : x ∈ positiveCone.upper Q t) (hy : y ∈ positiveCone.upper Q t) :
    ∃ K : PointedCone ℝ (realified V), IsRationalCone K ∧
      K ≤ rationalClosure (closedSheet Q hpos ht) ∧ σ ≤ K ∧
      (K : Set (realified V)) ∈ 𝓝 x ∧ (K : Set (realified V)) ∈ 𝓝 y := by
  have hx0 : x ≠ 0 := by
    intro h
    subst x
    have h0 : (0 : ℝ) < 0 := by simpa using hx.1
    exact lt_irrefl 0 h0
  have hy0 : y ≠ 0 := by
    intro h
    subst y
    have h0 : (0 : ℝ) < 0 := by simpa using hy.1
    exact lt_irrefl 0 h0
  obtain ⟨Kx, hKxrat, hKx, hKxle⟩ := exists_rationalCone_mem_nhds_subset_of_mem_interior
    (upper_subset_interior_upperZero hpos ht hx) hx0
  obtain ⟨Ky, hKyrat, hKy, hKyle⟩ := exists_rationalCone_mem_nhds_subset_of_mem_interior
    (upper_subset_interior_upperZero hpos ht hy) hy0
  have hKxC : Kx ≤ rationalClosure (closedSheet Q hpos ht) :=
    hKxle.trans (upperZero_le_rationalClosure_closedSheet hpos)
  have hKyC : Ky ≤ rationalClosure (closedSheet Q hpos ht) :=
    hKyle.trans (upperZero_le_rationalClosure_closedSheet hpos)
  let K := (Kx ⊔ Ky) ⊔ σ
  refine ⟨K, (hKxrat.sup hKyrat).sup hσrat, sup_le (sup_le hKxC hKyC) hσle,
    le_sup_right, ?_, ?_⟩
  · exact Filter.mem_of_superset hKx
      ((le_sup_left : Kx ≤ Kx ⊔ Ky).trans (le_sup_left : Kx ⊔ Ky ≤ K))
  · exact Filter.mem_of_superset hKy
      ((le_sup_right : Ky ≤ Kx ⊔ Ky).trans (le_sup_left : Kx ⊔ Ky ≤ K))

/-- Three upper-sheet points admit a common rational cone neighbourhood containing a prescribed
rational isotropic ray. This is the two-point construction applied twice and joined. -/
theorem exists_rationalCone_sup_mem_nhds_of_isotropic_three (hpos : sigPos Q = 1)
    {ht : 0 < Q t} {σ : PointedCone ℝ (realified V)} (hσle : σ ≤ rationalClosure
      (closedSheet Q hpos ht)) (hσrat : IsRationalCone σ) {x y z : realified V}
    (hx : x ∈ positiveCone.upper Q t) (hy : y ∈ positiveCone.upper Q t)
    (hz : z ∈ positiveCone.upper Q t) :
    ∃ K : PointedCone ℝ (realified V), IsRationalCone K ∧
      K ≤ rationalClosure (closedSheet Q hpos ht) ∧ σ ≤ K ∧
      (K : Set (realified V)) ∈ 𝓝 x ∧ (K : Set (realified V)) ∈ 𝓝 y ∧
      (K : Set (realified V)) ∈ 𝓝 z := by
  obtain ⟨K₁, hK₁rat, hK₁le, hσK₁, hK₁x, hK₁y⟩ :=
    exists_rationalCone_sup_mem_nhds_of_isotropic hpos hσle hσrat hx hy
  obtain ⟨K₂, hK₂rat, hK₂le, hσK₂, hK₂x, hK₂z⟩ :=
    exists_rationalCone_sup_mem_nhds_of_isotropic hpos hσle hσrat hx hz
  let K := K₁ ⊔ K₂
  have hK₁ : K₁ ≤ K := le_sup_left
  have hK₂ : K₂ ≤ K := le_sup_right
  exact ⟨K, hK₁rat.sup hK₂rat, sup_le hK₁le hK₂le, hσK₁.trans hK₁,
    Filter.mem_of_superset hK₁x hK₁, Filter.mem_of_superset hK₁y hK₁,
    Filter.mem_of_superset hK₂z hK₂⟩

/-- **Projected lineality passes to an adjacent member.** Let `a`, `b` contain the isotropic ray
through `e` and meet along an upper-sheet point. Every direction in the lineality of the closure
of `π_I a` belongs to the lineality of the closure of `π_I b`.

For `z` in the common projected cell and `x` in the first lineality, rational cone neighbourhoods
of upper-sheet lifts of `z`, `z + r x`, and `z - r x` reduce the two translates to one closed
finitely generated trace. Its common face contains `z`; face-ness at the midpoint puts `z + r x`
in the second projected trace. Taking `r → ∞` gives both signs of `x` in the second closure. -/
theorem lineal_topologicalClosure_map_le_of_hull_singleton (hpos : sigPos Q = 1)
    (hnd : Q.Nondegenerate) {ht : 0 < Q t}
    {S : Set (PointedCone ℝ (realified V))}
    (hS : IsLocallyRationalDecomposition (rationalClosure (closedSheet Q hpos ht)) S)
    {e : realified V} (he0 : e ≠ 0) (heQ : Q e = 0)
    {a b : PointedCone ℝ (realified V)}
    (hea : PointedCone.hull ℝ ({e} : Set (realified V)) ≤ a)
    (heb : PointedCone.hull ℝ ({e} : Set (realified V)) ≤ b)
    (ha : a ∈ S) (hb : b ∈ S)
    (habC : (((a ⊓ b : PointedCone ℝ (realified V)) : Set (realified V)) ∩
      (positiveCone.upper Q t : Set (realified V))).Nonempty) :
    let N := Submodule.span ℝ ({e} : Set (realified V))
    let _ : ContinuousAdd (realified V ⧸ N) := IsModuleTopology.toContinuousAdd ℝ _
    PointedCone.lineal (a.map N.mkQ).topologicalClosure ≤
      PointedCone.lineal (b.map N.mkQ).topologicalClosure := by
  classical
  let N := Submodule.span ℝ ({e} : Set (realified V))
  let A := a.map N.mkQ
  let B := b.map N.mkQ
  let _ : ContinuousAdd (realified V ⧸ N) := IsModuleTopology.toContinuousAdd ℝ _
  change PointedCone.lineal A.topologicalClosure ≤ PointedCone.lineal B.topologicalClosure
  obtain ⟨z, hzab, hzC⟩ := habC
  let zq : realified V ⧸ N := N.mkQ z
  have hea' : e ∈ a := hea (PointedCone.subset_hull (Set.mem_singleton e))
  have heb' : e ∈ b := heb (PointedCone.subset_hull (Set.mem_singleton e))
  have hrayle : PointedCone.hull ℝ ({e} : Set (realified V)) ≤
      rationalClosure (closedSheet Q hpos ht) := hea.trans (hS.le ha)
  have heC : e ∈ rationalClosure (closedSheet Q hpos ht) :=
    hrayle (PointedCone.subset_hull (Set.mem_singleton e))
  have heSheet : e ∈ closedSheet Q hpos ht := rationalClosure_le_closedSheet hpos heC
  have hrayrat : IsRationalCone (PointedCone.hull ℝ ({e} : Set (realified V))) :=
    IsIsotropicHalfLine.isRationalCone_of_le_of_mem hpos hnd hS
      ⟨e, he0, heQ, rfl⟩ ha hea
  have hbe : ∀ v : V, rationalPoint v ∈ (closedSheet Q hpos ht).closure →
      0 ≤ (associated Q) e (rationalPoint v) := by
    intro v hv
    have hclosed := isClosed_closedSheet_of_moduleTopology Q hpos ht
    have hvS : rationalPoint v ∈ closedSheet Q hpos ht := by
      rw [← hclosed.submodule_topologicalClosure_eq]
      exact hv
    exact nonneg_associated_of_mem_closedSheet hpos ht heSheet.1 heSheet.2 hvS.1 hvS.2
  let β := isotropicHalfspaceForm Q heQ
  have hβcont : Continuous β := IsModuleTopology.continuous_of_linearMap β
  have hclosure_nonneg {u : realified V ⧸ N} (hu : u ∈ A.topologicalClosure) : 0 ≤ β u := by
    apply closure_minimal (t := {u | 0 ≤ β u}) ?_
      (isClosed_le continuous_const hβcont) hu
    exact image_mkQ_subset_of_le_rationalClosure Q hpos ht heQ hbe (hS.le ha)
  have hzA : zq ∈ A := ⟨z, hzab.1, rfl⟩
  have hzβ : 0 < β zq := by
    have hzim : zq ∈ N.mkQ '' (positiveCone.upper Q t) := ⟨z, hzC, rfl⟩
    rw [image_mkQ_upper_eq Q hpos hnd ht he0 heQ heSheet.2] at hzim
    exact hzim
  have hzclA : zq ∈ A.topologicalClosure := Submodule.le_topologicalClosure A hzA
  intro x hx
  rw [PointedCone.mem_lineal] at hx ⊢
  have hβx : β x = 0 := by
    have hp := hclosure_nonneg hx.1
    have hn := hclosure_nonneg hx.2
    rw [map_neg] at hn
    linarith
  have hclA (r : ℝ) : zq + r • x ∈ A.topologicalClosure := by
    apply A.topologicalClosure.add_mem hzclA
    rcases le_total 0 r with hr | hr
    · exact PointedCone.smul_mem _ hr hx.1
    · have hm := PointedCone.smul_mem _ (neg_nonneg.2 hr) hx.2
      simpa only [neg_smul, smul_neg, neg_neg] using hm
  have hlift (r : ℝ) : ∃ y : realified V,
      y ∈ positiveCone.upper Q t ∧ N.mkQ y = zq + r • x := by
    have hrpos : 0 < β (zq + r • x) := by
      rw [map_add, map_smul, hβx, smul_zero, add_zero]
      exact hzβ
    have him : zq + r • x ∈ N.mkQ '' (positiveCone.upper Q t) := by
      rw [image_mkQ_upper_eq Q hpos hnd ht he0 heQ heSheet.2]
      exact hrpos
    exact him
  have htrans : ∀ r : ℝ, zq + r • x ∈ B := by
    intro r
    obtain ⟨yp, hypC, hyp⟩ := hlift r
    obtain ⟨ym, hymC, hym⟩ := hlift (-r)
    obtain ⟨K, hKrat, hKle, hrayK, hKnz, hKnp, hKnm⟩ :=
      exists_rationalCone_sup_mem_nhds_of_isotropic_three hpos hrayle hrayrat hzC hypC hymC
    have heK : e ∈ K := hrayK (PointedCone.subset_hull (Set.mem_singleton e))
    have hmapKn {y : realified V} (hy : (K : Set (realified V)) ∈ 𝓝 y) :
        (K.map N.mkQ : Set (realified V ⧸ N)) ∈ 𝓝 (N.mkQ y) :=
      N.isOpenMap_mkQ.image_mem_nhds hy
    obtain ⟨sG, hsG⟩ := hS.isLocallyRational a ha K hKrat hKle
    let T := sG.image rationalPoint
    have hAT : a ⊓ K = PointedCone.hull ℝ (T : Set (realified V)) := by
      simpa [T] using hsG
    have hFG : (a ⊓ K).FG := ⟨T, hAT.symm⟩
    have hclosedA : IsClosed (((a ⊓ K).map N.mkQ : PointedCone ℝ (realified V ⧸ N)) :
        Set (realified V ⧸ N)) :=
      PointedCone.FG.isClosed_of_moduleTopology (PointedCone.FG.map hFG N.mkQ)
    have hlocal (r' : ℝ) {y : realified V} (hyq : N.mkQ y = zq + r' • x)
        (hKny : (K : Set (realified V)) ∈ 𝓝 y) :
        zq + r' • x ∈ (a ⊓ K).map N.mkQ := by
      have hyK : (K.map N.mkQ : Set (realified V ⧸ N)) ∈ 𝓝 (zq + r' • x) := by
        rw [← hyq]
        exact hmapKn hKny
      have hmem := mem_topologicalClosure_map_inf_of_mem_nhds N (e := e)
        (A := a) (K := K) rfl hea' heK hyK (hclA r')
      rw [hclosedA.closure_eq] at hmem
      exact hmem
    have hpA : zq + r • x ∈ (a ⊓ K).map N.mkQ := hlocal r hyp hKnp
    have hmA : zq + (-r) • x ∈ (a ⊓ K).map N.mkQ := hlocal (-r) hym hKnm
    have hzK : z ∈ K := mem_of_mem_nhds hKnz
    have hzMA : zq ∈ (a ⊓ K).map N.mkQ := ⟨z, ⟨hzab.1, hzK⟩, rfl⟩
    have hzMB : zq ∈ (b ⊓ K).map N.mkQ := ⟨z, ⟨hzab.2, hzK⟩, rfl⟩
    let R := hS.restriction K hKrat hKle
    have hRA : a ⊓ K ∈ faceClosure (restrictionTo S K) :=
      mem_faceClosure.2 ⟨a ⊓ K, mem_restrictionTo.2 ⟨a, ha, rfl⟩,
        PointedCone.IsFaceOf.refl (a ⊓ K)⟩
    have hRB : b ⊓ K ∈ faceClosure (restrictionTo S K) :=
      mem_faceClosure.2 ⟨b ⊓ K, mem_restrictionTo.2 ⟨b, hb, rfl⟩,
        PointedCone.IsFaceOf.refl (b ⊓ K)⟩
    have hface := PointedCone.IsFaceOf.map_mkQ_span_singleton (e := e)
      (F := (a ⊓ K) ⊓ (b ⊓ K)) (C := a ⊓ K)
      (he := ⟨⟨hea', heK⟩, ⟨heb', heK⟩⟩) (hF := R.inf_isFaceOf_left hRA hRB)
    have hinfmap : ((a ⊓ K) ⊓ (b ⊓ K)).map N.mkQ =
        (a ⊓ K).map N.mkQ ⊓ (b ⊓ K).map N.mkQ :=
      map_inf_eq_inf_map_of_span_singleton ⟨hea', heK⟩ ⟨heb', heK⟩
    dsimp only at hface
    rw [hinfmap] at hface
    have hmid : (1 / 2 : ℝ) • (zq + r • x) + (1 / 2 : ℝ) • (zq + (-r) • x) = zq := by
      module
    have hcommon : (1 / 2 : ℝ) • (zq + r • x) + (1 / 2 : ℝ) • (zq + (-r) • x) ∈
        (a ⊓ K).map N.mkQ ⊓ (b ⊓ K).map N.mkQ := by
      rw [hmid]
      exact ⟨hzMA, hzMB⟩
    have hmhalf : (1 / 2 : ℝ) • (zq + (-r) • x) ∈ (a ⊓ K).map N.mkQ :=
      ((a ⊓ K).map N.mkQ).smul_mem (by norm_num) hmA
    have hpcommon := hface.mem_of_smul_add_mem hpA hmhalf (by norm_num : (0 : ℝ) < 1 / 2)
      hcommon
    obtain ⟨w, hw, hq⟩ := hpcommon.2
    exact ⟨w, hw.1, hq⟩
  refine ⟨mem_topologicalClosure_of_forall_add_smul_mem htrans, ?_⟩
  apply mem_topologicalClosure_of_forall_add_smul_mem (z := zq) (x := -x)
  intro r
  simpa only [neg_smul, smul_neg] using htrans (-r)

/-- **Projected closure lineality is constant along an isotropic common-face chain.** Every node
contains the quotienting ray, and consecutive members meet along an upper-sheet point. The
pairwise theorem applies in both directions at every step. -/
theorem lineal_topologicalClosure_map_eq_of_reflTransGen_of_hull_singleton
    (hpos : sigPos Q = 1) (hnd : Q.Nondegenerate) {ht : 0 < Q t}
    {S : Set (PointedCone ℝ (realified V))}
    (hS : IsLocallyRationalDecomposition (rationalClosure (closedSheet Q hpos ht)) S)
    {e : realified V} (he0 : e ≠ 0) (heQ : Q e = 0)
    {a b : PointedCone ℝ (realified V)}
    (hchain : Relation.ReflTransGen (fun a b =>
      a ∈ S ∧ b ∈ S ∧ PointedCone.hull ℝ ({e} : Set (realified V)) ≤ a ∧
      PointedCone.hull ℝ ({e} : Set (realified V)) ≤ b ∧
      (((a ⊓ b : PointedCone ℝ (realified V)) : Set (realified V)) ∩
        (positiveCone.upper Q t : Set (realified V))).Nonempty) a b) :
    let N := Submodule.span ℝ ({e} : Set (realified V))
    let _ : ContinuousAdd (realified V ⧸ N) := IsModuleTopology.toContinuousAdd ℝ _
    PointedCone.lineal (a.map N.mkQ).topologicalClosure =
      PointedCone.lineal (b.map N.mkQ).topologicalClosure := by
  induction hchain with
  | refl => rfl
  | tail _ hbc ih =>
      apply ih.trans
      apply le_antisymm
      · exact lineal_topologicalClosure_map_le_of_hull_singleton hpos hnd hS he0 heQ
          hbc.2.2.1 hbc.2.2.2.1 hbc.1 hbc.2.1 hbc.2.2.2.2
      · apply lineal_topologicalClosure_map_le_of_hull_singleton hpos hnd hS he0 heQ
          hbc.2.2.2.1 hbc.2.2.1 hbc.2.1 hbc.1
        simpa only [inf_comm] using hbc.2.2.2.2

end IsotropicRationalTraces

end LeanCategories.Lattices.Valued
