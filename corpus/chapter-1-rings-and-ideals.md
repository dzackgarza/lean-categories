---
type: reference
title: Chapter 1. Rings and ideals
description: '## Source and revision comparison'
tags:
- project
- reference
timestamp: '2026-09-10T00:00:00Z'
scope: project
source: agent
confidence: high
promotable: false
project_id: github.com__dzackgarza__lean-categories
---
# Chapter 1. Rings and ideals

## Source and revision comparison

Reconciled on 2026-09-10 against all 59 canonical C01 source IDs and the 1969 edition's printed pp. 1–10 (the source scan is identified in the main FC04 record). Source IDs were not renumbered. P is Mathlib `db584cd6d46c92f209a44c0f1c829460d327499d`, Lean v4.33.0, Apache-2.0; L is the indicated landed LeanCategories revision, also Apache-2.0. N retains the dated, scoped negative evidence in [[provenance-contract-for-c01]] where that comparison has not been defeated.

The earlier row alignment was wrong: for example U004 (ring homomorphism) pointed to Ideal, U011 (congruence) to the zero-ring condition, and U020 (prime ideal) to a field characterization. Corrections below follow the source ID and full obligation, not the old row order. Generic library constructions count only with the complete comparison; the checked code below supplies the nontrivial compositions used to supersede two former negative routes. U005 explicitly records the printed subring omission instead of claiming an equivalence to its insufficient literal checklist.

| FC04 ID | Verdict | Route | Lean target(s) | Provenance | Interface comparison |
| --- | --- | --- | --- | --- | --- |
| `FC04-C01-U001` | exact structure | `mathlib` | `Mathlib/Algebra/Ring/Defs.lean::CommRing` | P | Mathlib's `CommRing` is a commutative unital ring; as in Atiyah–Macdonald, the degenerate one-element ring is permitted unless `Nontrivial` is separately assumed. |
| `FC04-C01-U002` | exact ring convention | `mathlib` | `Mathlib/Algebra/Ring/Defs.lean::CommRing` | P | The source convention reuses the commutative unital ring structure from U001; it is not the ring-homomorphism unit U004. No nontriviality is assumed. |
| `FC04-C01-U003` | zero-ring predicate and model | `mathlib` | `Mathlib/Algebra/GroupWithZero/Basic.lean::subsingleton_iff_zero_eq_one`; `subsingleton_of_zero_eq_one`; `Mathlib/Algebra/Ring/PUnit.lean::PUnit.commRing` | P | For an existing ring, 0=1 is equivalent to subsingletonness. PUnit with its canonical commutative ring structure supplies the one-element model. This row is the zero ring, not Subring. |
| `FC04-C01-U004` | exact homomorphism structure | `mathlib` | `Mathlib/Algebra/Ring/Hom/Defs.lean::RingHom` | P | Between commutative rings, the bundled map preserves addition, multiplication and 1. Preservation of zero and additive inverses follows from additivity, so the extra stored zero law does not strengthen the source. |
| `FC04-C01-U005` | standard subring; printed omission identified | `mathlib` | `Mathlib/Algebra/Ring/Subring/Defs.lean::Subring` | P | Subring extends Subsemiring and AddSubgroup, and therefore includes additive-inverse closure. Printed p. 2 lists only closure under addition/multiplication and membership of 1, an insufficient condition: the nonnegative integers in Z satisfy it but omit -1. This is NOT an equivalence with that literal checklist. The candidate realizes the ring with inherited operations and inclusion ring homomorphism asserted by the following source sentence; the printed omission is recorded explicitly, not silently attributed to Lean. |
| `FC04-C01-U006` | exact ideal structure | `mathlib` | `Mathlib/RingTheory/Ideal/Defs.lean::Ideal`; `Mathlib/Algebra/Module/Submodule/Defs.lean::Submodule` | P | An ideal is the additive submodule of the ring acting on itself. Additive-subgroup closure and absorption by arbitrary ring elements are exactly the source laws; Ideal.span is a construction on sets, not this definition. |
| `FC04-C01-U007` | exact quotient-ring construction | `mathlib` | `Mathlib/RingTheory/Ideal/Quotient/Defs.lean::Ideal.Quotient`; `Mathlib/RingTheory/Ideal/Quotient/Basic.lean` | P | The quotient by the ideal congruence has the induced ring operations on cosets. Commutativity makes every ideal two-sided. A principal ideal is not the requested quotient. |
| `FC04-C01-U008` | exact canonical quotient map | `mathlib` | `Mathlib/RingTheory/Ideal/Quotient/Defs.lean::Ideal.Quotient.mk`; `Ideal.Quotient.mk_surjective` | P | The bundled ring homomorphism maps x to its coset and is surjective. Its domain is the original ring. |
| `FC04-C01-U009` | exact correspondence | `mathlib` | `Mathlib/RingTheory/Ideal/Maps.lean::Ideal.relIsoOfSurjective`; `Ideal.Quotient.mk_surjective`; `Ideal.Quotient.mk_ker` | P | Applying the surjective correspondence order-isomorphism to `R → R/I` identifies ideals of the quotient with ideals of `R` containing `I`. |
| `FC04-C01-U010` | kernel, image and first-isomorphism bundle | `mathlib` | `Mathlib/RingTheory/Ideal/Maps.lean::RingHom.ker`; `Mathlib/Algebra/Ring/Subring/Basic.lean::RingHom.range`; `Mathlib/RingTheory/Ideal/Quotient/Operations.lean::RingHom.quotientKerEquivRange` | P | The kernel is an ideal, the image is a subring, and quotientKerEquivRange constructs the ring equivalence from the kernel quotient to that image. All three source clauses are represented. |
| `FC04-C01-U011` | exact congruence comparison | `mathlib` | `Mathlib/RingTheory/Ideal/Quotient/Defs.lean::Ideal.Quotient.eq` | P | Equality of the quotient classes of x and y is equivalent to x-y belonging to I. This is congruence modulo I, not the zero-ring predicate. |
| `FC04-C01-U012` | exact equivalent definition | `mathlib` | `Mathlib/Algebra/GroupWithZero/NonZeroDivisors.lean::nonZeroDivisors`; `notMem_nonZeroDivisors_iff_left` | P | The complement of `nonZeroDivisors` is exactly the elements annihilating some nonzero element; in a nontrivial ring this includes `0`, matching the source convention. |
| `FC04-C01-U013` | exact structure | `mathlib` | `Mathlib/Algebra/Ring/Defs.lean::IsDomain` | P | `IsDomain R` combines nontriviality with the no-zero-divisors property, exactly the integral-domain definition. |
| `FC04-C01-U014` | nilpotence with equivalent exponent convention | `mathlib` | `Mathlib/Algebra/GroupWithZero/Basic.lean::IsNilpotent` | P | Mathlib uses existence of a natural exponent, whereas the source requires a positive exponent. If x^n=0 then x^(n+1)=x^n*x=0; the converse drops positivity. Thus the predicates agree even in the zero ring. The checked comparison below records both directions. |
| `FC04-C01-U015` | unit and its inverse | `mathlib` | `Mathlib/Algebra/Group/Units/Defs.lean::IsUnit`; `Units`; `isUnit_iff_exists_inv` | P | IsUnit x supplies a unit with underlying value x; its inverse is unit data. In a commutative ring this is equivalent to existence of y with xy=1. If xy=xz=1 then y=y(xz)=(yx)z=z, giving the source uniqueness. Nilpotence is U014, not this row. |
| `FC04-C01-U016` | principal ideal construction | `mathlib` | `Mathlib/RingTheory/Ideal/Span.lean::Ideal.span`; `Ideal.mem_span_singleton`; `Ideal.span_singleton_eq_top` | P | The value Ideal.span {x} consists precisely of multiples of x. The source notation (x)=Ax names this generic construction; its equality to the unit ideal is equivalent to IsUnit x. |
| `FC04-C01-U017` | zero-ideal notation | `mathlib` | `Mathlib/RingTheory/Ideal/Span.lean::Ideal.span_singleton_zero`; bottom ideal in `Mathlib/RingTheory/Ideal/Lattice.lean` | P | The ideal generated by 0 is the bottom ideal. This is a notational convention, not a new local declaration or the unit predicate. |
| `FC04-C01-U018` | field predicate and field structure | `mathlib` | `Mathlib/Algebra/Field/Defs.lean::Field`; `Mathlib/Algebra/Field/IsField.lean::IsField.toField` | P | A field is a nontrivial commutative ring in which each nonzero element has a multiplicative inverse. For a ring already supplied, IsField and its toField construction avoid replacing its carrier. |
| `FC04-C01-U019` | field-characterization bundle by canonical comparisons | `mathlib` | `Mathlib/RingTheory/Ideal/Basic.lean::Ring.isField_iff_isSimpleOrder_ideal`; `Mathlib/RingTheory/Ideal/Maps.lean::RingHom.injective_iff_ker_eq_bot`; `Mathlib/RingTheory/SimpleRing/Basic.lean::RingHom.injective`; `Ideal.Quotient.mk_ker`; `Ideal.Quotient.mk` | P | The simple ideal lattice gives the field/only-two-ideals equivalence. Field-source homomorphisms into nonzero rings are injective. Conversely, apply the asserted injectivity to R→R/I for each proper I; its kernel is I, so I=0. This recovers the simple ideal lattice and hence IsField. The last argument is a complete comparison, not a claim that Field alone proves all three clauses. |
| `FC04-C01-U020` | exact prime-ideal predicate | `mathlib` | `Mathlib/RingTheory/Ideal/Prime.lean::Ideal.IsPrime`; `Ideal.isPrime_iff` | P | The fields are I≠top and xy∈I implies x∈I or y∈I. The field-characterization theorem belongs to U019, not this source unit. |
| `FC04-C01-U021` | exact definition | `mathlib` | `Mathlib/RingTheory/Ideal/Maximal.lean::Ideal.IsMaximal`; `Ideal.isMaximal_iff` | P | This is maximality among proper ideals under inclusion. |
| `FC04-C01-U022` | exact iff pair | `mathlib` | `Mathlib/RingTheory/Ideal/Quotient/Basic.lean::Ideal.Quotient.isDomain_iff_prime`; `Ideal.Quotient.maximal_ideal_iff_isField_quotient` | P | The quotient is a domain exactly when the ideal is prime, and a field exactly when it is maximal. |
| `FC04-C01-U023` | maximal-prime and zero-prime comparisons | `mathlib` | `Mathlib/RingTheory/Ideal/Maximal.lean::Ideal.IsMaximal.isPrime`; `Mathlib/RingTheory/Ideal/Prime.lean::Ideal.isPrime_bot`; `IsDomain.of_bot_isPrime` | P | The first declaration gives maximal implies prime. The latter two give both directions between primality of the zero ideal and the domain property; the converse is not inferred merely from the forward instance. |
| `FC04-C01-U024` | prime contraction and explicit maximality counterexample | `mathlib` | `Mathlib/RingTheory/Ideal/Maps.lean::Ideal.IsPrime.comap`; `Ideal.comap_bot_of_injective`; `Mathlib/RingTheory/Ideal/Maximal.lean::Ideal.bot_isMaximal`; `Ideal.IsMaximal.eq_of_le`; `Ideal.span_singleton_eq_top` | P | Prime contraction is direct. For Z→Q, (0) in Q is maximal and contracts to (0) in Z. The ideal (2) is nonzero and proper, so that contraction is not maximal. The anonymous Lean example below checks the entire counterexample from the pinned declarations; the earlier unmatched finding is superseded by this complete composition. |
| `FC04-C01-U025` | maximal-ideal existence and source order vocabulary | `mathlib` | `Mathlib/RingTheory/Ideal/Maximal.lean::Ideal.exists_maximal`; `Mathlib/Order/Zorn.lean::zorn_le_nonempty`; `IsChain` | P | exists_maximal supplies the maximal ideal for a nonzero commutative ring. The source footnote is also retained: IsChain (·≤·) is pairwise comparability in a partially ordered set, and zorn_le_nonempty gives a maximal element from upper bounds for nonempty chains in a nonempty order. |
| `FC04-C01-U026` | exact existence theorem | `mathlib` | `Mathlib/RingTheory/Ideal/Maximal.lean::Ideal.exists_le_maximal` | P | Every proper ideal is contained in a maximal ideal. |
| `FC04-C01-U027` | exact theorem | `mathlib` | `Mathlib/RingTheory/Ideal/Nonunits.lean::exists_max_ideal_of_mem_nonunits`; `coe_subset_nonunits` | P | Every nonunit lies in a maximal ideal, while every proper ideal consists only of nonunits; together these identify the nonunits with the union of maximal ideals. |
| `FC04-C01-U028` | exact equivalent definitions | `mathlib` | `Mathlib/RingTheory/LocalRing/Defs.lean::IsLocalRing`; `Mathlib/RingTheory/LocalRing/Basic.lean::IsLocalRing.of_unique_max_ideal`; `Mathlib/RingTheory/LocalRing/MaximalIdeal/Basic.lean::IsLocalRing.maximal_ideal_unique`; `IsLocalRing.of_nonunits_add` | P | Mathlib proves equivalence between the local-ring unit criterion, a unique maximal ideal, and additive closure of the nonunits. |
| `FC04-C01-U029` | exact construction | `mathlib` | `Mathlib/RingTheory/LocalRing/ResidueField/Basic.lean::IsLocalRing.ResidueField`; `IsLocalRing.residue` | P | The residue field is the quotient by the unique maximal ideal, with its canonical residue map. |
| `FC04-C01-U030` | both local-ring criteria through the unique-maximal-ideal constructor | `mathlib` | `Mathlib/RingTheory/LocalRing/Basic.lean::IsLocalRing.of_unique_max_ideal`; `Mathlib/RingTheory/Ideal/Maximal.lean::Ideal.exists_le_maximal`; `Ideal.IsMaximal.eq_of_le`; `Ideal.IsMaximal.exists_inv`; `isUnit_of_mul_isUnit_right` | P | For (i), every proper ideal consists of nonunits and hence lies in m; a maximal ideal containing m is therefore m and is the unique maximal ideal. For (ii), when x∉m, maximality gives yx+t=1 with t∈m; 1-t is a unit by the hypothesis on 1+m, so yx and then x are units, reducing to (i). These are construction criteria for locality, not just properties assuming locality. The checked comparisons below retain both input hypotheses and m≠top. |
| `FC04-C01-U031` | exact property | `mathlib` | `[Finite (MaximalSpectrum R)]` as used throughout `Mathlib/RingTheory/LocalProperties/Semilocal.lean` | P | Mathlib's semilocal hypotheses are exactly finiteness of the maximal spectrum, i.e. finitely many maximal ideals. |
| `FC04-C01-U032` | complete polynomial/integer ideal examples | `project-existing` | `LeanCategories/ForMathlib/MvPolynomialIdealOfVars.lean::MvPolynomial.mem_idealOfVars_iff_constantCoeff_eq_zero`; `MvPolynomial.idealOfVars_isMaximal`; `MvPolynomial.card_le_card_of_span_eq_idealOfVars`; `MvPolynomial.idealOfVars_not_isPrincipal`; P `Ideal.isPrime_span_singleton_of_prime`; `UniqueFactorizationMonoid.irreducible_iff_prime`; `Int.ideal_span_isMaximal_of_prime`; `PrincipalIdealRing.isMaximal_of_irreducible` | P; L: `f355dc345c6cd1507871f57e3dd52d874d492b1b` | For irreducible f in a multivariable polynomial ring over a field, use the canonical UFD instance from Mathlib/RingTheory/Polynomial/UniqueFactorization.lean and the prime-principal-ideal theorem. For a natural prime p, Mathlib/RingTheory/Ideal/Int.lean gives maximality of (p) in Z via the quotient ZMod p; irreducible polynomials in one variable give maximal ideals by the PID criterion. The integrated owner proves that the ideal generated by all variables is exactly the kernel of constantCoeff and is maximal over a field. For every finite generating family g, evaluating partial derivatives at zero makes D(g) span the coordinate vector space, proving card(variables) ≤ card(g); in particular the ideal is not principal when there are at least two variables. This also retains the sharper printed p. 5 generator-count claim. The focused build and complete normal commit gate passed. No field-of-characteristic-zero hypothesis is imposed. |
| `FC04-C01-U033` | principal-ideal domain and its nonzero prime ideals | `mathlib` | `Mathlib/Algebra/Ring/Defs.lean::IsDomain`; `Mathlib/RingTheory/Ideal/Span.lean::IsPrincipalIdealRing`; `Mathlib/RingTheory/PrincipalIdealDomain.lean::Ideal.IsPrime.to_maximal_ideal` | P | Use the conjunction of the domain property and the assertion that every ideal is principal. Ideal.IsPrime.to_maximal_ideal requires both and the nonzero-prime hypothesis. IsPrincipalIdealRing alone would admit rings that are not domains. |
| `FC04-C01-U034` | exact construction and quotient criterion | `mathlib` | `Mathlib/RingTheory/Nilpotent/Lemmas.lean::nilradical`; `mem_nilradical`; `nilradical_eq_bot_iff`; `Mathlib/RingTheory/Ideal/Quotient/Nilpotent.lean::Ideal.isRadical_iff_quotient_reduced` | P | The nilpotent elements form `nilradical R`; quotienting by this radical ideal is reduced, matching the source construction. |
| `FC04-C01-U035` | exact identification | `mathlib` | `Mathlib/RingTheory/Nilpotent/Lemmas.lean::nilradical`; `mem_nilradical` | P | `mem_nilradical` identifies the nilradical with the nilpotent elements, and Mathlib's ideal radical specializes at `⊥` to the same ideal. |
| `FC04-C01-U036` | exact theorem | `mathlib` | `Mathlib/RingTheory/Nilpotent/Lemmas.lean::nilradical_eq_sInf` | P | The nilradical is exactly the infimum/intersection of all prime ideals. |
| `FC04-C01-U037` | exact definition | `mathlib` | `Mathlib/RingTheory/Jacobson/Ideal.lean::Ideal.jacobson`; `Ideal.jacobson_bot` | P | `Ideal.jacobson ⊥` is the intersection of all maximal ideals, exactly the Jacobson radical of the ring. |
| `FC04-C01-U038` | exact iff | `mathlib` | `Mathlib/RingTheory/Jacobson/Ideal.lean::Ideal.mem_jacobson_bot` | P | Mathlib characterizes Jacobson-radical membership by unitness of `1+xy` for all `y`; replacing `y` by `-y` is exactly `1-xy` in the source. |
| `FC04-C01-U039` | exact constructions | `mathlib` | `Mathlib/RingTheory/Ideal/Operations.lean::Ideal.add_eq_sup`; `Mathlib/RingTheory/Ideal/Span.lean::Ideal.iSup_eq_span`; `Ideal.span_iUnion` | P | Binary ideal sum is lattice supremum, and arbitrary sums are the least ideal containing the union. |
| `FC04-C01-U040` | complete lattice of ideals | `mathlib` | `Mathlib/RingTheory/Ideal/Lattice.lean::Ideal.mem_iInf`; `Ideal.mem_sInf`; complete-lattice instance on `Ideal R` | P | Arbitrary intersections have pointwise membership, and the canonical complete lattice orders ideals by inclusion. The ideal structure supplies closure, not merely a set intersection. |
| `FC04-C01-U041` | exact constructions | `mathlib` | `Mathlib/RingTheory/Ideal/Operations.lean` ideal multiplication and power instances; `Ideal.mul_assoc`; `Ideal.prod_mem_prod` | P | Ideal multiplication is generated by finite sums of products, with finite products and powers and `I^0=⊤=(1)`. |
| `FC04-C01-U042` | exact laws | `mathlib` | `Ideal.mul_assoc`; `Ideal.mul_sup`; `Ideal.sup_mul`; `Ideal.mul_le_inf`; `Mathlib/Order/ModularLattice.lean::sup_inf_assoc_of_le`; `Ideal.mul_eq_inf_of_isCoprime` | P | These give associativity/distributivity, the modular lattice identity under the source containment, `ab≤a∩b`, and equality for comaximal ideals. |
| `FC04-C01-U043` | coprimality at the generic owner | `mathlib` | `Mathlib/RingTheory/Coprime/Basic.lean::IsCoprime`; `Mathlib/RingTheory/Ideal/Operations.lean::Ideal.isCoprime_iff_sup_eq`; `Ideal.isCoprime_iff_add`; `Ideal.isCoprime_iff_exists` | P | The generic IsCoprime predicate on ideals is equivalent to I+J=top, and then to 1=x+y with x∈I and y∈J. There is no separate Ideal.IsCoprime declaration. |
| `FC04-C01-U044` | finite product and coordinate projections | `mathlib` | `Mathlib/Algebra/Ring/Pi.lean::Pi.commRing`; `Pi.evalRingHom`; `Mathlib/Algebra/Ring/Prod.lean::Prod.instCommRing`; `RingHom.fst`; `RingHom.snd` | P | Pi.commRing gives componentwise operations for the indexed family; evaluation at each index is the required ring homomorphism. Binary products and projections are the special two-factor case. |
| `FC04-C01-U045` | source CRT comparison before factoring through the kernel | `mathlib` | `Mathlib/Algebra/Ring/Pi.lean::RingHom.pi`; `Mathlib/RingTheory/Ideal/Quotient/Defs.lean::Ideal.Quotient.mk` | P | Use RingHom.pi (fun i => Ideal.Quotient.mk (I i)), with domain R. Ideal.quotientInfToPiQuotient instead has domain R/(intersection I) and is the induced injective map, not the source map itself. |
| `FC04-C01-U046` | complete CRT criteria for the source map | `mathlib` | `Mathlib/RingTheory/Ideal/Operations.lean::Ideal.prod_eq_iInf_of_pairwise_isCoprime`; `Mathlib/RingTheory/Ideal/Quotient/Operations.lean::Ideal.pi_quotient_surjective`; `Ideal.ker_Pi_Quotient_mk`; `Mathlib/RingTheory/Ideal/Maps.lean::RingHom.injective_iff_ker_eq_bot`; `Ideal.isCoprime_iff_exists` | P | For finitely many ideals, pairwise coprimality gives product=intersection and surjectivity of the map in U045. Conversely lift the tuple with 1 at i and 0 elsewhere; then 1-r∈I_i and r∈I_j for j≠i, proving coprimality. Its kernel is the intersection, so injectivity is equivalent to zero intersection. Both iff statements are checked below. The already-quotiented map is always injective and cannot replace this domain-sensitive claim. |
| `FC04-C01-U047` | exact prime-avoidance theorems | `mathlib` | `Mathlib/RingTheory/Ideal/Operations.lean::Ideal.subset_union_prime`; `Ideal.subset_union_prime_finite`; `Ideal.IsPrime.prod_le` | P | Mathlib supplies finite prime avoidance and the prime-containing-a-finite-product/intersection consequence used in Proposition 1.11. |
| `FC04-C01-U048` | colon at the submodule owner | `mathlib` | `Mathlib/RingTheory/Ideal/Colon.lean::Submodule.colon`; `Submodule.mem_colon` | P | For ideals I,J take I.colon (J : Set R). The membership theorem says precisely that r*x∈I for every x∈J. The stored ideal laws give additive closure and absorption; the old Ideal.mem_colon name was incorrect. |
| `FC04-C01-U049` | annihilator and principal-colon notation | `mathlib` | `Mathlib/RingTheory/Ideal/Colon.lean::Submodule.bot_colon`; `Ideal.mem_colon_span_singleton`; `Mathlib/RingTheory/Ideal/Maps.lean::Module.annihilator` | P | The colon of zero by the ideal is its annihilator; with the ideal viewed as a module, Module.annihilator has the same all-elements annihilation condition. The singleton-span colon gives r*x∈I, realizing (I:x). |
| `FC04-C01-U050` | radical and quotient-nilradical comparison | `mathlib` | `Mathlib/RingTheory/Ideal/Operations.lean::Ideal.radical`; `Ideal.mem_radical_iff`; `Mathlib/RingTheory/Ideal/Maps.lean::Ideal.comap_radical`; `Ideal.Quotient.mk_ker`; `Mathlib/RingTheory/Nilpotent/Lemmas.lean::nilradical` | P | The radical is an ideal. A natural power in I can be replaced by its successor by multiplying by x, so its membership condition agrees with the positive-exponent source convention even for I=top. Apply comap_radical to the quotient map and the zero ideal, using mk_ker and nilradical=(bottom).radical, for the quotient characterization. |
| `FC04-C01-U051` | exact theorem | `mathlib` | `Mathlib/RingTheory/Ideal/Operations.lean::Ideal.radical_eq_sInf` | P | The radical is the infimum/intersection of all prime ideals containing the ideal. |
| `FC04-C01-U052` | integrated subset radical and intrinsic comparisons | `project-existing` | `LeanCategories/Algebra/AtiyahMacdonald/SubsetRadical.lean::LeanCategories.Algebra.subsetRadical`; `LeanCategories.Algebra.subsetRadical_iUnion`; `LeanCategories.Algebra.subsetRadical_coe_ideal` | L: `3523c95` | The definition uses a positive power for an arbitrary subset, without ideal closure. The union law and agreement with Ideal.radical on ideals are proved. Checked examples show 2 lies in the radical of {4} in Z, that radical is not an ideal (zero is absent), and allowing exponent zero would wrongly admit 2 over {1}. |
| `FC04-C01-U053` | unmatched theorem | `unmatched` | partial: `Module.annihilator`; `Ideal.radical`; `nonZeroDivisors`; Noetherian associated-prime results | N | No checked P/H or external declaration proves the source-general identity `D = ⋃_{x≠0} radical(Ann(x))`; the available associated-prime description of zero divisors has stronger finiteness/Noetherian hypotheses and is not this theorem. |
| `FC04-C01-U054` | complete implication by pinned radical identities | `mathlib` | `Mathlib/RingTheory/Ideal/Operations.lean::Ideal.isCoprime_iff_sup_eq`; `Ideal.radical_eq_top`; `Ideal.radical_sup`; `Ideal.radical_top` | P | Rewrite coprimality as supremum=top. The hypothesis makes radical(radical I sup radical J)=top; radical_sup identifies this with radical(I sup J), and radical_eq_top gives I sup J=top. The checked Lean composition below discharges the complete source implication, replacing the earlier exact-name-based unmatched conclusion. |
| `FC04-C01-U055` | exact construction | `mathlib` | `Mathlib/RingTheory/Ideal/Maps.lean::Ideal.map`; `Ideal.map_span` | P | `I.map f` is the ideal generated by the image `f(I)`, exactly extension `Iᵉ`. |
| `FC04-C01-U056` | exact construction and theorem | `mathlib` | `Mathlib/RingTheory/Ideal/Maps.lean::Ideal.comap`; `Ideal.IsPrime.comap` | P | `J.comap f` is inverse image/contraction, and prime ideals contract to prime ideals. |
| `FC04-C01-U057` | range factorization with the ring-valued image | `mathlib` | `Mathlib/Algebra/Ring/Subring/Basic.lean::RingHom.range`; `RingHom.rangeRestrict`; `RingHom.rangeRestrict_surjective`; `Mathlib/RingTheory/Ideal/Maps.lean::Ideal.relIsoOfSurjective`; `Ideal.map`; `Ideal.comap` | P | The map factors through its subring-valued range using rangeRestrict and the inclusion. The surjective factor has the ideal-correspondence order equivalence. General extension and contraction apply to the inclusion. rangeSRestrict targets the subsemiring-valued range and is not the ring-image owner requested here. |
| `FC04-C01-U058` | complete Gaussian prime-ideal example | `project-existing` | `LeanCategories/ForMathlib/GaussianPrimeIdeals.lean::GaussianInt.ramification_two`; `GaussianInt.exists_prime_ideal_factorization_of_mod_four_eq_one`; `GaussianInt.inert_prime_of_mod_four_eq_three`; `GaussianInt.not_associated_star_of_prime_norm`; `GaussianInt.associated_or_associated_star_of_norm_eq_prime`; P `Nat.Prime.sq_add_sq` | Project `ef6fc9c04c0a284a3a01c91a0fc7e5352a59d70a`; P; Apache-2.0, Lean 4.33.0 | Source printed p. 10: the actual extension of `(2)` is `(1+i)^2` with prime base; for p=1 mod 4 the extension is the product of two distinct conjugate prime ideals, with a generator of norm p from the canonical sum-of-two-squares theorem; for p=3 mod 4 the extension is prime. Prime-norm factors are unique up to units and conjugation. Distinctness is proved from norm divisibility, not inferred from the product equation. The p=5 example and the failure of distinct conjugate factors at p=2 are checked. Focused module build and unchanged full commit gate passed. |
| `FC04-C01-U059` | Galois connection and its fixed-point equivalence | `mathlib` | `Mathlib/RingTheory/Ideal/Maps.lean::Ideal.gc_map_comap`; `Ideal.le_comap_map`; `Ideal.map_comap_le`; `Ideal.map_comap_map`; `Ideal.comap_map_comap` | P | The unit/counit inequalities are I≤comap(map I) and map(comap J)≤J; the last two equalities prove ec/ce stabilization. Restrict map and comap to their fixed-point subtypes: their composites are the identity by the subtype defining equations. A contracted ideal is fixed by comap_map_comap and a fixed ideal is the contraction of its extension; dually for extended ideals. Thus all image/fixed-point and bijection clauses are retained. |

## Checked composite comparisons

The following complete Lean block was checked against P on 2026-09-10 with `lake env lean` (exit 0, no warnings). It exhibits the exact compositions used in the rows above. These are comparison proofs inside the mapping record, not new project aliases or replacement library definitions. The public owner names and their input hypotheses remain the library's.

```lean
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Ideal.Basic
import Mathlib.RingTheory.LocalRing.Basic
import Mathlib.RingTheory.Jacobson.Ideal
import Mathlib.Data.Rat.Cast.CharZero
import Mathlib.Tactic.NormNum

-- FC04-C01-U014: the natural and positive exponent conventions agree.
example {R : Type*} [CommRing R] (x : R) :
    IsNilpotent x ↔ ∃ n : ℕ, 0 < n ∧ x ^ n = 0 := by
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨n + 1, Nat.succ_pos n, by rw [pow_succ, hn, zero_mul]⟩
  · rintro ⟨n, _, hn⟩
    exact ⟨n, hn⟩

-- FC04-C01-U024: maximal ideals do not generally contract to maximal ideals.
example : (⊥ : Ideal ℚ).IsMaximal ∧
    ¬ (Ideal.comap (Int.castRingHom ℚ) (⊥ : Ideal ℚ)).IsMaximal := by
  refine ⟨Ideal.bot_isMaximal, ?_⟩
  have hc : Ideal.comap (Int.castRingHom ℚ) (⊥ : Ideal ℚ) = ⊥ :=
    Ideal.comap_bot_of_injective (f := Int.castRingHom ℚ) Int.cast_injective
  rw [hc]
  intro h
  have hproper : Ideal.span ({2} : Set ℤ) ≠ ⊤ := by
    intro ht
    have hu : IsUnit (2 : ℤ) := Ideal.span_singleton_eq_top.mp ht
    obtain ⟨k, hk⟩ := hu.exists_right_inv
    omega
  have he := h.eq_of_le hproper bot_le
  have h2 : (2 : ℤ) ∈ (⊥ : Ideal ℤ) := he.symm ▸ Ideal.subset_span (by simp)
  norm_num at h2

-- FC04-C01-U030(i): units outside a proper ideal determine the local ring.
private theorem localCriterion {R : Type*} [CommRing R] (m : Ideal R) (hm : m ≠ ⊤)
    (h : ∀ x : R, x ∉ m → IsUnit x) : IsLocalRing R ∧ m.IsMaximal := by
  obtain ⟨M, hM, hmM⟩ := Ideal.exists_le_maximal m hm
  have below : ∀ J : Ideal R, J ≠ ⊤ → J ≤ m := by
    intro J hJ x hx
    by_contra hxm
    exact hJ (J.eq_top_of_isUnit_mem hx (h x hxm))
  have hMm : M = m := le_antisymm (below M hM.ne_top) hmM
  have hu : ∃! J : Ideal R, J.IsMaximal :=
    ⟨m, hMm ▸ hM, fun J hJ => hJ.eq_of_le hm (below J hJ.ne_top)⟩
  exact ⟨IsLocalRing.of_unique_max_ideal hu, hMm ▸ hM⟩

-- FC04-C01-U030(ii): the maximal-ideal 1+m criterion.
example {R : Type*} [CommRing R] (m : Ideal R) (hm : m.IsMaximal)
    (h : ∀ t : R, t ∈ m → IsUnit (1+t)) : IsLocalRing R := by
  refine (localCriterion m hm.ne_top ?_).1
  intro x hx
  obtain ⟨y, t, ht, hyt⟩ := hm.exists_inv hx
  have hyx : y*x = 1-t := eq_sub_of_add_eq hyt
  have hu : IsUnit (y*x) := by
    rw [hyx]
    simpa only [sub_eq_add_neg] using h (-t) (m.neg_mem ht)
  exact isUnit_of_mul_isUnit_right hu

-- FC04-C01-U046: the source map has domain R, not R/(intersection I).
example {R ι : Type*} [CommRing R] [Finite ι] (I : ι → Ideal R) :
    Function.Surjective (RingHom.pi fun i => Ideal.Quotient.mk (I i)) ↔
      Pairwise (fun i j => IsCoprime (I i) (I j)) := by
  classical
  constructor
  · intro h i j hij
    obtain ⟨r, hr⟩ := h (Pi.single i 1)
    have hi : Ideal.Quotient.mk (I i) r = 1 := by
      simpa using congrFun hr i
    have hj : Ideal.Quotient.mk (I j) r = 0 := by
      simpa [hij.symm] using congrFun hr j
    apply Ideal.isCoprime_iff_exists.mpr
    refine ⟨1-r, ?_, r, Ideal.Quotient.eq_zero_iff_mem.mp hj, sub_add_cancel 1 r⟩
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    rw [map_sub, map_one, hi, sub_self]
  · intro h y
    obtain ⟨r, hr⟩ := Ideal.pi_quotient_surjective h y
    exact ⟨r, funext hr⟩

example {R ι : Type*} [CommRing R] (I : ι → Ideal R) :
    Function.Injective (RingHom.pi fun i => Ideal.Quotient.mk (I i)) ↔
      (⨅ i, I i) = ⊥ := by
  rw [RingHom.injective_iff_ker_eq_bot, Ideal.ker_Pi_Quotient_mk]

-- FC04-C01-U054 is a composition of the pinned radical/sup equivalences.
example {R : Type*} [CommRing R] (I J : Ideal R)
    (h : IsCoprime I.radical J.radical) : IsCoprime I J := by
  rw [Ideal.isCoprime_iff_sup_eq] at h ⊢
  apply Ideal.radical_eq_top.mp
  rw [Ideal.radical_sup, h, Ideal.radical_top]
```



