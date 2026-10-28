# Independent scalar and formed-module extensions

## Scope and provenance

These additions implement fixed mathematical questions 5, 6, 8 and 9 and the separately
proposed genuine formed-arrow lifting example. They are upstream mathematical authorship,
not independent release acceptance or evidence about any computation.

The mathematical base is `dbab309f2ee6a4da2c19e970f4d5d6460d8665a4`. Only new modules and their
documentation and validation record are added. No old mathematical object, registry schema, kernel, computational
contract, leaf, or acceptance assertion is edited. The author used the permitted mathematical
sources, public catalogue interfaces and Mathlib. The author did not inspect downstream
implementation, leaf code, acceptance output or runtime trial reports.

The independent input documents are:

- `/tmp/v1-independent-math/exit-trial-checklist.md`;
- `/tmp/v1-independent-math-review/exit-trial-mathematical-assessment.md`;
- `/tmp/v1-independent-math-review/genuine-formed-lift-proposal.md`;
- `/tmp/v1-independent-math-review/exit-trial-source-provenance.json`.

The initial immutable candidate supplied to the author was kernel
`9630f544f0b82581ba0083f7bbd49831ef5967e2` and public contract
`7c3f35762c6e64d7b0728bd7e40af8fc8bb26ffe`. Before any extension trial was counted, the owner
published kernel `8ca2615e57b7cef1de64a96394dc262984513c43` and public contract
`6780f9f0e0ac9acb7355d9281993df44f0d13b54`. These identifiers are provenance supplied by the
owner; they are not a claim that this author reviewed either implementation.

The public import root is
`LeanCategories.Catalogue.Semantics.Independent.ScalarAndFormExtensions`.

## Public inputs and registration identities

The order below is the actual order of explicit public mathematical parameters. Typeclass
arguments in the generic formed-module lift come from the selected coefficient and value
modules, rather than from computations.

| Registration | Declaration, after the `CasCatalogue` prefix | Explicit parameter order |
| --- | --- | --- |
| `obj.fields.prime_residues` | `Algebra.PrimeResidueFields.primeResidues` | `p : ℕ`, `hp : p.Prime` |
| `obj.modules_r.restricted_regular` | `Modules.IntegerResidueModules.restrictedRegularModule` | `R : RingCat`, `S : RingCat`, `q : R ⟶ S` |
| `mor.sets.successor_power_series_terms` | `Algebra.SuccessorSeries.successorTerms` | `R : CommRingCat`; output is the entire morphism `ℕ → R[[t]]` |
| `obj.sets.rectangular_matrices` | `Algebra.RectangularLinearAlgebra.rectangularMatrices` | rows, columns, `R : CommRingCat` |
| `mor.modules.rectangular_linear_map` | `Algebra.RectangularLinearAlgebra.rectangularLinearMap` | rows, columns, `R`, the rectangular matrix |
| `mor.modules.row_linear_map` | `Algebra.RectangularLinearAlgebra.rowLinearMap` | columns, `R`, the `1 × columns` matrix |
| `obj.bilin_module.ordinary_kernel_restriction` | `Modules.Bilinear.Valued.ModuleKernelRestriction.ordinaryKernelRestriction` | `R : CommRingCat`, `W : ModuleCat R`, formed source `X`, target module `Y`, ordinary arrow `f : X.carrierObj ⟶ Y` |
| `mor.bilin_module.ordinary_kernel_inclusion` | `Modules.Bilinear.Valued.ModuleKernelRestriction.ordinaryKernelInclusion` | the same five inputs |
| `obj.bilin_module.rational_diagonal_2_3` | `Modules.Bilinear.Valued.ModuleKernelRestriction.RationalProjection.diagonalSource` | none; the selected form is `diag(2,3)` on `ℚ²` |
| `lift.bilin_module.change_value_restriction` | `Modules.Bilinear.Valued.ChangeValueLifts.changeValueMonoLift` | `R`, value modules `W,W'`, selected linear map `a : W →ₗ[R] W'` |
| corresponding callable data | `Modules.Bilinear.Valued.ChangeValueLifts.changeValueMonoLiftComputation` | the same inputs; then the four `MonoLiftComputation` components |
| `obj.bilin_module.degenerate_plane` | `Modules.Bilinear.Valued.DegeneratePlaneLifts.source` | none; first form `2(a+b)(c+d)` |
| `obj.bilin_module.degenerate_plane_target` | `Modules.Bilinear.Valued.DegeneratePlaneLifts.target` | none; target form `2su+5tv` |
| `mor.bilin_module.degenerate_plane_map` | `Modules.Bilinear.Valued.DegeneratePlaneLifts.formedMap` | none; actual formed arrow `(a,b) ↦ (a+b,0)` |
| `obj.bilin_module.degenerate_plane_with_dot` | `Modules.Bilinear.Valued.DegeneratePlaneLifts.pairedSource` | none; pair of forms `(2(a+b)(c+d), ac+bd)` |
| `mor.bilin_module.degenerate_plane_cone` | `Modules.Bilinear.Valued.DegeneratePlaneFactorization.cone` | none; formed arrow `h(s,t)=(3s-2t,-3s+2t)` |
| `mor.bilin_module.degenerate_plane_paired_cone` | `Modules.Bilinear.Valued.DegeneratePlaneFactorization.pairedCone` | none; the same full map with its pulled-back second form |

The change-of-values lift registers against the existing edge
`constructMap(arrow, fun.bilin_module.change_value)`. It does not edit the existing functor
registration or turn value modules into interchangeable carriers. The first restriction
uses the existing `lift.bilin_module.restrict` and its existing callable computation.

## Question 5: the actual carrier diamond at the selected five-element ring

The new generic object is the prime-residue **field** `PrimeResidues(p,hp)`, built from
Mathlib's existing field structure on `ZMod p`. At `p=5`, forgetting the field and
commutativity gives exactly the already named ring `ZMod 5`. This supplies fresh selected
structured input without duplicating the old ring family, its operations, or cardinality.

After those first two forgetful steps, retain both complete routes:

1. `fun.rings.multiplicative_monoid`, `fun.monoids.semigroup`,
   `classifierForget(clf.magmas.associative)`,
   `classifierForget(clf.sets.binary_operation)`;
2. `fun.rings.additive_group`, `fun.additive_groups.to_groups`, `fun.groups.monoid`,
   `fun.monoids.semigroup`, `classifierForget(clf.magmas.associative)`,
   `classifierForget(clf.sets.binary_operation)`.

The identifier constants and route lists remain owned by
`Algebra/Ports.lean` and `Algebra/PortComparison.lean`. The existing
`cmp.rings.carrier` is the actual invertible natural
cell between the full composites. Its designated source is the multiplicative route.
It acts by the identity on residues. Both underlying cardinalities are five, and both functor
map actions retain the original ring homomorphism's complete function. At the earlier
operation level, `1+1=2` and `1·1=1` in `ZMod 5`, so the two ports are distinct.

For a separately specified mathematical environment omitting `cmp.rings.carrier`, retain both
route candidates. No replacement cell, endpoint-equality convention, or registration-order
tie breaker is supplied by these additions. Whether a reader correctly reports their
unresolved ambiguity is a later independent acceptance question.

Proofs are `underlying_ring`, `carrier_comparison_apply`, `carrier_routes_map`,
`five_multiplicative_cardinality`, `five_additive_cardinality`, and
`five_operations_separate` in `Algebra.PrimeResidueFields`.

## Question 6: the selected quotient and its actual reindexing

Use `R=ℤ`, `S=ZMod 5`, and the existing integer coefficient map, regarded as a ring
morphism. `quotient_is_integer_coefficients` identifies it exactly with
`RingCat.ofHom (Int.castRingHom (ZMod 5))`. Apply the new restricted-regular-module family to
these three inputs. It uses the existing module fibration's reindexing on the existing
regular module of `S`; the action is `r·m=q(r)m`.

The original regular `S`-module has dimension one. The restricted integer module retains the
five-element additive carrier. Its fixed observations are `2·3=1`, `5·1=0`, and `(-1)·2=3`.
The actual cartesian arrow lies over `q` and has identity underlying additive function.
Reindexing any actual regular-module arrow preserves its complete function; in particular,
the nonidentity map `x ↦ 2x` still takes `3` to `1` after reindexing.

The principal declarations are in `Modules.IntegerResidueModules`:
`integerResidueModule`, `reindex_selected_quotient`, `action_formula`,
`five_regular_dimension`, `five_cardinality`, `five_actions`, `five_cartesian_base`,
`five_cartesian_carrier`, `reindex_map_apply`, and `reindex_double_three`.

## Question 8: preserve the ordinary projection and the restricted form `[3]`

Use the actual `1 × 2` row `[[1,0]]` over `ℚ`. The declared `rowLinearMap` has codomain
the actual scalar regular module `ℚ`, not a square endomorphism and not an unbundled set
function. In `ModuleKernelRestriction.RationalProjection`, this is `projection`, whose
source is `diagonalSource` with form `2ac+3bd`.

The selected kernel coordinate is the linear equivalence
`kernelCoordinates : ℚ ≃ₗ[ℚ] ker(projection)`, `t ↦ (0,t)`. The restricted object and
actual defining map are `restricted` and `inclusion`. They satisfy

`inclusion(kernelCoordinates t)=(0,t)`,

`projection(inclusion(kernelCoordinates t))=0`,

`restricted.pairing(kernelCoordinates s,kernelCoordinates t)=3st`.

The kernel dimension is one and the value at `(1,1)` is three. These are proved by
`kernel_dimension`, `inclusion_coordinates`, `restricted_pairing`,
`restricted_pairing_one`, and `projection_inclusion`.

The universal theorem `projection_not_formed` excludes **every** bilinear form on the
actual target `ℚ`: no fixed-value formed arrow has this underlying projection.
The proof uses the source vector `(0,1)`, whose self-pairing is three and whose image is
zero. The new `ordinaryKernelRestriction` explicitly composes the ordinary module kernel
with the existing arbitrary-submodule restriction. It makes no formed-arrow claim about
the original projection.

## Separate genuine lifting example, with two successive stages

Use `DegeneratePlaneLifts.source`, `target`, and `formedMap`. Their independent formulas are

`B_X((a,b),(c,d))=2(a+b)(c+d)`,

`B_Y((s,t),(u,v))=2su+5tv`,

`f(a,b)=(a+b,0)`.

The selected module-kernel model is `kernelInclusion : ℚ → ℚ²`,
`i₀(t)=(2t,-2t)`. The full module-kernel property is `kernel_universal`; `kernel_range`
identifies the entire image with the actual module kernel. The first stage uses the
existing prescribed restriction lift, yielding `firstObject`, `firstInclusion`, `alpha`,
and `beta`. The defining formulas are

`alpha(a,-a)=a/2`, `beta(t)=(2t,-2t)`, `firstInclusion(a,-a)=(a,-a)`.

Both inverse identities and the defining-map factorization are theorems.
In particular `alpha(4,-4)=2`. The first restricted form is zero for every pair; this
does not replace the original projection's nonzero form `[3]`.

The second selected layer is the independently meaningful additional dot product `ac+bd`.
The existing value module `ℚ×ℚ` records the pair of chosen forms. The existing functor
`changeValue` along `fst : ℚ×ℚ →ₗ[ℚ] ℚ` forgets the second value.
`ChangeValueLifts.changeValueMonoLift` supplies the full generic cartesian restriction
for this already existing functor. Its comparison has identity carrier map and preserves
the specified first form by the given arrow's actual pairing equation.

`compositeLift := secondLift.comp firstLift` then computes its second stage on
**`firstInclusion`**, not on another independently chosen module mono. The theorems
`final_object_is_successive` and `final_inclusion_is_second` expose exactly that composition.
The output consists of `finalObject`, `finalInclusion`, `finalAlpha`, and `finalBeta`.
The final forward and backward maps retain the half-coordinate and twice-coordinate maps.
The final pairing in the selected coordinate is `(0,8st)`; at `s=t=1`, it is `(0,8)`.
The final inclusion sends `finalBeta(3/2)` to `(3,-3)`.

The first and final inverse equations and factorization equations are independently
typed at their actual endpoints. The generic composition order is the existing
`MonoLift.computation_comp_forward` and `MonoLift.computation_comp_backward`; no new
composition calculus is introduced.

The separate `DegeneratePlaneFactorization` module fixes the nonzero cone
`h(s,t)=(3s-2t,-3s+2t)` by its own matrix and the base mediator `(3s-2t)/2` by its own row.
It proves their compatibility, constructs `formedMediator` and `finalMediator`, reuses
the returned defining maps in both factorization equations, retains the composed
comparison equation, and proves uniqueness. The two fixed observations are

- at `(2,1)`, the cone and lifted mediator have vector value `(4,-4)` and the base mediator is `2`;
- at `(1,3)`, the vector value is `(-3,3)` and the base mediator is `-3/2`.

All these maps have their complete rational domains. The finite displayed observations
do not replace the full functions or the universal laws.

## Question 9: retain the infinite family and the admission proposition

`successorTerms R` is the entire function `n ↦ C(n+1)t^n` on `ℕ`.
The old summability theorem `Series.summable_of_X_pow_dvd` proves its admission in the
selected `powerSeriesTAdic R`. The old binder `bind.sets.power_series_sum` sums the admitted
function. `successorTerms_sum` proves that its complete coefficient function is `d ↦ d+1`;
`integer_degree_three` gives the fixed value four over `ℤ`.

`integer_constant_one_not_summable` uses degree-zero coefficients and Mathlib's
`summable_const_iff`. `no_constant_one_admission` therefore excludes any object of the
existing admitted-family type whose full function is constant one. An external boolean
cannot supply such a proof or replace the admission domain. The coefficient ring, selected
topology, infinite index object, family function and summability proposition remain inputs
of the old binder.

## Validation boundary

Compilation is performed only in an isolated artifact overlay, with one Lean process at a
time inside this worker and the absolute Lean 4.33.0 binary supplied by the owner. The five
module artifact components are replaced only within that private overlay after successful
compilation. Shared build artifacts are not written by this author.

The additions use ordinary Lean/Mathlib proof terms; they contain no `sorry`, new axiom,
native backend proof, or leaf-supplied certificate. Compilation verifies these mathematical
declarations and registrations. Independent source review, frozen extension execution,
and observed acceptance remain separate responsibilities.

All eight mathematical modules and the aggregate import were compiled successfully with
Lean `4.33.0`, compiler commit `d8b18978322de05a8f3dba51ef03cf5461676c17`, using `-j1`.
The final sequential compilation log has nine `PRIVATE COMPILE OK` entries and no errors.
The remaining messages are style linter suggestions. A separate Lean `#print axioms` run
checks 31 principal declarations, including the generic lift, the two composed inverse
identities, both stages' actual cone factorizations and their uniqueness. Each depends only
on the standard foundations `propext`, `Classical.choice`, and `Quot.sound`; no `sorryAx`
or native-code proof axiom occurs.

`Integration/IndependentScalarAndFormValidation.json` retains the exact compiler invocation,
source digests, registered identifiers, complete final compilation output, and complete
proof-dependency output. It records mathematical author validation only. Its source hashes
identify exactly the checked source independently of later mechanical publication commits.
