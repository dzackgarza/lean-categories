---
title: "Hartshorne schemes definition catalogue"
---

# Algebraic Geometry

Title: *Algebraic Geometry*

Author: Robin Hartshorne

Zotero key: `6K3TGVE6`

Citekey: `Har10a`

Source attachment: `/home/dzack/Zotero/storage/AMY5NQZM/[Hartshorne 2008] Algebraic geometry.md`

## Chapter I. Varieties

- [x] Affine algebraic set — §1, Affine Varieties, pp. 1–7
  - `PrimeSpectrum.zeroLocus` — `Mathlib/RingTheory/Spectrum/Prime/Basic.lean`
- [x] Ideal of an affine algebraic set — §1, Affine Varieties, pp. 1–7
  - `PrimeSpectrum.vanishingIdeal` — `Mathlib/RingTheory/Spectrum/Prime/Basic.lean`
- [x] Affine variety — §1, Affine Varieties, pp. 1–7
  - `AlgebraicGeometry.AffineScheme` — `Mathlib/AlgebraicGeometry/AffineScheme.lean`
- [x] Coordinate ring of an affine variety — §1, Affine Varieties, pp. 1–7
  - `Scheme.Γ` — `Mathlib/AlgebraicGeometry/Scheme.lean`
- [x] Dimension of a variety — §1, Affine Varieties, pp. 1–7
  - `topologicalKrullDim` — `Mathlib/Topology/KrullDimension.lean`
- [x] Projective space — §2, Projective Varieties, pp. 8–13
  - `Projectivization` — `Mathlib/LinearAlgebra/Projectivization/Basic.lean`
- [x] Homogeneous ideal — §2, Projective Varieties, pp. 8–13
  - `HomogeneousIdeal` — `Mathlib/RingTheory/GradedAlgebra/Homogeneous/Ideal.lean`
- [x] Projective algebraic set — §2, Projective Varieties, pp. 8–13
  - `ProjectiveSpectrum.zeroLocus` — `Mathlib/AlgebraicGeometry/ProjectiveSpectrum/Topology.lean`
- [x] Projective variety — §2, Projective Varieties, pp. 8–13
  - `Proj` — `Mathlib/AlgebraicGeometry/ProjectiveSpectrum/Scheme.lean`
- [x] Regular function — §3, Morphisms, pp. 14–23
  - `Scheme.Γ` — `Mathlib/AlgebraicGeometry/Scheme.lean`
- [x] Morphism of varieties — §3, Morphisms, pp. 14–23
  - `Scheme.Hom` — `Mathlib/AlgebraicGeometry/Scheme.lean`
- [x] Isomorphism of varieties — §3, Morphisms, pp. 14–23
  - `CategoryTheory.Iso` — `Mathlib/CategoryTheory/Iso.lean`
- [x] Rational function — §4, Rational Maps, pp. 24–30
  - `Scheme.functionField` — `Mathlib/AlgebraicGeometry/FunctionField.lean`
- [x] Rational map — §4, Rational Maps, pp. 24–30
  - `AlgebraicGeometry.Scheme.RationalMap` — `Mathlib/AlgebraicGeometry/Birational/RationalMap.lean`
- [x] Birational map — §4, Rational Maps, pp. 24–30
  - `AlgebraicGeometry.Birational` — `Mathlib/AlgebraicGeometry/Birational/Birational.lean`
- [x] Function field of a variety — §4, Rational Maps, pp. 24–30
  - `Scheme.functionField` — `Mathlib/AlgebraicGeometry/FunctionField.lean`
- [x] Tangent space — §5, Nonsingular Varieties, pp. 31–38
  - `TauCeti.AlgebraicGeometry.ZariskiTangentSpace` — `TauCeti/AlgebraicGeometry/TangentSpace/Basic.lean` (TauCeti)
- [x] Nonsingular point — §5, Nonsingular Varieties, pp. 31–38
  - `Scheme.IsSmoothAtPoint` — `Atlas/AlgebraicGeometryI/code/SmoothPointVariety.lean` (atlas-lean)
  - `Scheme.isSmoothAtPoint_iff_isRegularLocalRing` ties it to regular local rings — `Atlas/AlgebraicGeometryI/code/SmoothPointVariety.lean`
- [x] Singular point — §5, Nonsingular Varieties, pp. 31–38
  - `Scheme.IsSingularAtPoint` — `Atlas/AlgebraicGeometryI/code/SmoothPointVariety.lean` (atlas-lean)
- [x] Nonsingular variety — §5, Nonsingular Varieties, pp. 31–38
  - `Scheme.IsSmooth` — `Atlas/AlgebraicGeometryI/code/SmoothPointVariety.lean` (atlas-lean)
  - Mathlib morphism class: `AlgebraicGeometry.Smooth` — `Mathlib/AlgebraicGeometry/Morphisms/Smooth.lean`
- [x] Local parameter on a nonsingular curve — §6, Nonsingular Curves, pp. 39–46
  - `intValuation.Uniformizer`, `valuation_exists_uniformizer` (uniformizer of a DVR local ring) — `Mathlib/RingTheory/DedekindDomain/AdicValuation.lean`
- [ ] Intersection multiplicity of a curve and a hypersurface — §7, Intersections in Projective Space, pp. 47–54
  - Partial reference: `intersectionMultiplicity` treats affine plane curves only — `Atlas/AlgebraicGeometryI/code/Lec5BezoutPascal.lean`
  - Partial reference: `projIntersectionMultiplicity` treats projective plane curves only — `Atlas/AlgebraicGeometryI/code/IntersectionMultSingular.lean`; `totalIntersectionNumber`/`bezout_theorem` — `Atlas/AlgebraicGeometryI/code/BezoutIntersection.lean`
- [ ] Degree of a projective variety — §7, Intersections in Projective Space, pp. 47–54

## Chapter II. Schemes

- [x] Presheaf — §1, Sheaves, pp. 60–68
  - `TopCat.Presheaf` — `Mathlib/Topology/Sheaves/Presheaf.lean`
- [x] Sheaf — §1, Sheaves, pp. 60–68
  - `TopCat.Sheaf` — `Mathlib/Topology/Sheaves/Sheaf.lean`
- [x] Stalk of a sheaf — §1, Sheaves, pp. 60–68
  - `TopCat.Presheaf.stalk` — `Mathlib/Topology/Sheaves/Stalks.lean`
- [x] Germ of a section — §1, Sheaves, pp. 60–68
  - `TopCat.Presheaf.germ` — `Mathlib/Topology/Sheaves/Stalks.lean`
- [x] Morphism of sheaves — §1, Sheaves, pp. 60–68
  - `CategoryTheory.NatTrans` — `Mathlib/CategoryTheory/NatTrans.lean`
- [x] Direct image sheaf — §1, Sheaves, pp. 60–68
  - `TopCat.Sheaf.pushforward` — `Mathlib/Topology/Sheaves/Functors.lean`
- [x] Inverse image sheaf — §1, Sheaves, pp. 60–68
  - `TopCat.Sheaf.pullback` — `Mathlib/Topology/Sheaves/Functors.lean`
- [x] Sheafification — §1, Sheaves, pp. 60–68
  - `TopCat.Presheaf.sheafify` — `Mathlib/Topology/Sheaves/Sheafify.lean`
- [x] Locally ringed space — §2, Schemes, pp. 69–81
  - `LocallyRingedSpace` — `Mathlib/Geometry/RingedSpace/LocallyRingedSpace.lean`
- [x] Spectrum of a ring — §2, Schemes, pp. 69–81
  - `PrimeSpectrum` — `Mathlib/RingTheory/Spectrum/Prime/Basic.lean`
- [x] Structure sheaf of an affine scheme — §2, Schemes, pp. 69–81
  - `Spec.structureSheaf` — `Mathlib/AlgebraicGeometry/StructureSheaf.lean`
- [x] Affine scheme — §2, Schemes, pp. 69–81
  - `AlgebraicGeometry.AffineScheme` — `Mathlib/AlgebraicGeometry/AffineScheme.lean`
- [x] Scheme — §2, Schemes, pp. 69–81
  - `AlgebraicGeometry.Scheme` — `Mathlib/AlgebraicGeometry/Scheme.lean`
- [x] Morphism of schemes — §2, Schemes, pp. 69–81
  - `AlgebraicGeometry.Scheme.Hom` — `Mathlib/AlgebraicGeometry/Scheme.lean`
- [x] Fibre of a morphism — §3, First Properties of Schemes, pp. 82–94
  - `Scheme.Hom.fiber` — `Mathlib/AlgebraicGeometry/Fiber.lean`
- [x] Reduced scheme — §3, First Properties of Schemes, pp. 82–94
  - `AlgebraicGeometry.IsReduced` — `Mathlib/AlgebraicGeometry/Properties.lean`
- [x] Integral scheme — §3, First Properties of Schemes, pp. 82–94
  - `AlgebraicGeometry.IsIntegral` — `Mathlib/AlgebraicGeometry/Properties.lean`
- [x] Noetherian scheme — §3, First Properties of Schemes, pp. 82–94
  - `AlgebraicGeometry.IsNoetherian` — `Mathlib/AlgebraicGeometry/Noetherian.lean`
- [x] Scheme locally of finite type — §3, First Properties of Schemes, pp. 82–94
  - `AlgebraicGeometry.LocallyOfFiniteType` — `Mathlib/AlgebraicGeometry/Morphisms/FiniteType.lean`
- [x] Scheme of finite type — §3, First Properties of Schemes, pp. 82–94
  - Mathlib: `AlgebraicGeometry.LocallyOfFiniteType` — `Mathlib/AlgebraicGeometry/Morphisms/FiniteType.lean`
- [x] Dimension of a scheme — §3, First Properties of Schemes, pp. 82–94
  - Mathlib: `topologicalKrullDim` — `Mathlib/Topology/KrullDimension.lean`
- [x] Separated morphism — §4, Separated and Proper Morphisms, pp. 95–107
  - `AlgebraicGeometry.IsSeparated` — `Mathlib/AlgebraicGeometry/Morphisms/Separated.lean`
- [x] Proper morphism — §4, Separated and Proper Morphisms, pp. 95–107
  - `AlgebraicGeometry.IsProper` — `Mathlib/AlgebraicGeometry/Morphisms/Proper.lean`
- [ ] Abstract variety — §4, Separated and Proper Morphisms, pp. 95–107
  - Partial reference: `AlgebraicGeometry.Scheme.IsAlgebraicVariety` imposes a finite affine-cover scheme presentation — `Atlas/AlgebraicGeometryI/code/Lec2AlgebraicVariety.lean`
- [x] Sheaf of modules — §5, Sheaves of Modules, pp. 108–128
  - `SheafOfModules` — `Mathlib/Algebra/Category/ModuleCat/Sheaf.lean`
- [x] Quasi-coherent sheaf — §5, Sheaves of Modules, pp. 108–128
  - `SheafOfModules.IsQuasicoherent` — `Mathlib/Algebra/Category/ModuleCat/Sheaf/Quasicoherent.lean`
- [x] Coherent sheaf — §5, Sheaves of Modules, pp. 108–128
  - `CoherentModuleCat` — `LeanCategories/Schemes/Coherent.lean` (lean-categories-schemes)
- [x] Locally free sheaf — §5, Sheaves of Modules, pp. 108–128
  - `SheafOfModules.IsLocallyFree` — `Mathlib/Algebra/Category/ModuleCat/Sheaf/LocallyFree.lean`
- [x] Invertible sheaf — §5, Sheaves of Modules, pp. 108–128
  - `Module.Invertible` — `Mathlib/RingTheory/PicardGroup.lean`
- [x] Weil divisor — §6, Divisors, pp. 129–148
  - `IsDedekindDomain.Divisor` — `vaca22/riemann-roch-function-fields:RiemannRoch/Divisor.lean`
- [x] Principal divisor — §6, Divisors, pp. 129–148
  - `FractionalIdeal.principalDivisor` — `vaca22/riemann-roch-function-fields:RiemannRoch/Divisor.lean`
- [x] Divisor class group — §6, Divisors, pp. 129–148
  - `ClassGroup` — `Mathlib/RingTheory/ClassGroup.lean`
- [x] Cartier divisor — §6, Divisors, pp. 129–148
  - `CartierDivisorGroup (X : Scheme) : Type u := X.carrier → ℤ` (arbitrary scheme) — `Atlas/AlgebraicGeometryI/code/AlgebraicEquivalence.lean` (atlas-lean)
  - Units-of-fractional-ideals model for 1-dim: `CartierDivisorGroup` — `Atlas/AlgebraicGeometryI/code/CartierDivisorGroup.lean`
  - `CartierDivisorScheme.CartierDivisorDatum` is defined only for integral schemes — `Atlas/AlgebraicGeometryI/code/CartierDivisorScheme.lean`
- [x] Cartier divisor class group — §6, Divisors, pp. 129–148
  - `picardEquiv` — `Atlas/AlgebraicGeometryI/code/CartierDivisorGroup.lean` (atlas-lean)
  - Mathlib: `CommRing.Pic` — `Mathlib/RingTheory/PicardGroup.lean`
- [x] Picard group — §6, Divisors, pp. 129–148
  - `CommRing.Pic` — `Mathlib/RingTheory/PicardGroup.lean`
- [x] Proj of a graded ring — §7, Projective Morphisms, pp. 149–171
  - `Proj` — `Mathlib/AlgebraicGeometry/ProjectiveSpectrum/Scheme.lean`
- [ ] Projective morphism — §7, Projective Morphisms, pp. 149–171
  - Partial reference: `ProjectiveRatMap.ProjectiveMorphism` is a map between subsets of finite projective spaces — `Atlas/ArithmeticGeometry/code/ProjectiveMorphisms.lean`
- [ ] Very ample invertible sheaf — §7, Projective Morphisms, pp. 149–171
  - Partial reference: complex-Kähler analog only: `IsVeryAmple` — `Atlas/GeometryOfManifolds/code/AdvancedKahler.lean` (atlas-lean)
- [ ] Ample invertible sheaf — §7, Projective Morphisms, pp. 149–171
  - Partial reference: complex-Kähler analog only: `IsAmple` — `Atlas/GeometryOfManifolds/code/AdvancedKahler.lean` (atlas-lean)
- [x] Derivation — §8, Differentials, pp. 172–189
  - `Derivation` — `Mathlib/RingTheory/Derivation/Basic.lean`
- [x] Module of Kähler differentials — §8, Differentials, pp. 172–189
  - `KaehlerDifferential` — `Mathlib/RingTheory/Kaehler/Basic.lean`
- [x] Sheaf of relative differentials — §8, Differentials, pp. 172–189
  - Mathlib: `KaehlerDifferential` on affine charts — `Mathlib/RingTheory/Kaehler/Basic.lean`
- [ ] Formal completion of a scheme along a closed subscheme — §9, Formal Schemes, pp. 190–200
- [ ] Formal scheme — §9, Formal Schemes, pp. 190–200

## Chapter III. Cohomology

- [x] Additive functor — §1, Derived Functors, pp. 201–204
  - `Functor.Additive` — `Mathlib/CategoryTheory/Preadditive/AdditiveFunctor.lean`
- [x] Left exact functor — §1, Derived Functors, pp. 201–204
  - `CategoryTheory.LeftExactFunctor` — `Mathlib/CategoryTheory/Limits/ExactFunctor.lean`
- [x] Right derived functor — §1, Derived Functors, pp. 201–204
  - `CategoryTheory.Functor.rightDerived` — `Mathlib/CategoryTheory/Abelian/RightDerived.lean`
- [x] Injective object — §1, Derived Functors, pp. 201–204
  - `CategoryTheory.Injective` — `Mathlib/CategoryTheory/Preadditive/Injective/Basic.lean`
- [x] Injective resolution — §1, Derived Functors, pp. 201–204
  - `CategoryTheory.InjectiveResolution` — `Mathlib/CategoryTheory/Abelian/Injective/Resolution.lean`
- [x] Cohomology of a sheaf — §2, Cohomology of Sheaves, pp. 205–211
  - `cohomologyPresheafFunctor` — `Mathlib/CategoryTheory/Sites/SheafCohomology/Basic.lean`
- [x] Acyclic sheaf — §2, Cohomology of Sheaves, pp. 205–211
  - `CategoryTheory.Functor.IsRightAcyclic` — `reservoir-sources/Vilin97__Clawristotle/coherent-cohomology-finite/CoherentCohomologyFinite/AcyclicResolution.lean` (Clawristotle; right-`G`-acyclic objects, `(RⁿG)(J) = 0` for all `n ≥ 1`; the acyclic-sheaf notion is the `G = Γ` instance)
  - Partial reference: affine-coherence vanishing theorems, not the definition: `higherDirectImageVanishing` — `Atlas/AlgebraicGeometryI/code/AffinePushforwardHigher.lean`; `prop44_higher_direct_image_vanishing` — `Atlas/AlgebraicGeometryI/code/AffinePushforwardCohomology.lean` (atlas-lean)
- [x] Flasque sheaf — §2, Cohomology of Sheaves, pp. 205–211
  - `TopCat.Sheaf.IsFlasque` — `Mathlib/Topology/Sheaves/Flasque.lean`
- [x] Čech complex — §4, Čech Cohomology, pp. 218–224
  - `cechComplexFunctor` — `Mathlib/CategoryTheory/Sites/SheafCohomology/Cech.lean`
- [x] Čech cohomology — §4, Čech Cohomology, pp. 218–224
  - `cechComplexFunctor` — `Mathlib/CategoryTheory/Sites/SheafCohomology/Cech.lean`
- [x] Ext functor — §6, Ext Groups and Sheaves, pp. 233–238
  - `CategoryTheory.extFunctor` — `Mathlib/Algebra/Homology/DerivedCategory/Ext/Basic.lean`
- [ ] Sheaf Ext — §6, Ext Groups and Sheaves, pp. 233–238
  - Partial reference: abelian-category Ext, not sheaf-specific: `def Ext (n : ℕ) : Cᵒᵖ ⥤ C ⥤ ModuleCat R` — `Mathlib/CategoryTheory/Abelian/Ext.lean`
- [ ] Dualizing sheaf — §7, The Serre Duality Theorem, pp. 239–249
- [ ] Higher direct image sheaf — §8, Higher Direct Images of Sheaves, pp. 250–252
  - Partial reference: `higherDirectImageVanishing`, `affinePushforwardCohomologyIso` — `Atlas/AlgebraicGeometryI/code/AffinePushforwardHigher.lean`; `prop44_higher_direct_image_vanishing` — `Atlas/AlgebraicGeometryI/code/AffinePushforwardCohomology.lean` (atlas-lean)
- [x] Flat module — §9, Flat Morphisms, pp. 253–267
  - `Module.Flat` — `Mathlib/RingTheory/Flat/Basic.lean`
- [x] Flat morphism — §9, Flat Morphisms, pp. 253–267
  - `AlgebraicGeometry.Flat` — `Mathlib/AlgebraicGeometry/Morphisms/Flat.lean`
- [x] Faithfully flat morphism — §9, Flat Morphisms, pp. 253–267
  - `RingHom.FaithfullyFlat` — `Mathlib/RingTheory/RingHom/FaithfullyFlat.lean`
- [x] Smooth morphism — §10, Smooth Morphisms, pp. 268–275
  - `AlgebraicGeometry.Smooth` — `Mathlib/AlgebraicGeometry/Morphisms/Smooth.lean`
- [x] Unramified morphism — §10, Smooth Morphisms, pp. 268–275
  - `RingHom.Unramified` — `Mathlib/RingTheory/RingHom/Unramified.lean`
- [x] Étale morphism — §10, Smooth Morphisms, pp. 268–275
  - `AlgebraicGeometry.Etale` — `Mathlib/AlgebraicGeometry/Morphisms/Etale.lean`
- [x] Upper semicontinuous function — §12, The Semicontinuity Theorem, pp. 281–292
  - `UpperSemicontinuous` — `Mathlib/Topology/Semicontinuity/Defs.lean`

## Chapter IV. Curves

- [x] Curve — §1, Riemann–Roch Theorem, pp. 294–298
  - `SmoothCompleteCurve` (structure; `chi_eq_rr` Riemann–Roch, `serre_duality_chi_canonical`) — `Atlas/AlgebraicGeometryI/code/CanonicalSheafCurves.lean` (atlas-lean)
- [x] Genus of a curve — §1, Riemann–Roch Theorem, pp. 294–298
  - `FunctionField.Chart.genus` — `RiemannRoch/Genus/Basic.lean` (riemann-roch-function-fields)
- [x] Canonical divisor — §1, Riemann–Roch Theorem, pp. 294–298
  - `FunctionField.Chart.WeilDifferential.IsCanonical` — `RiemannRoch/WeilDifferential/Basic.lean` (riemann-roch-function-fields)
- [x] Complete linear system — §1, Riemann–Roch Theorem, pp. 294–298
  - `FunctionField.Chart.RRspace` — `RiemannRoch/RRspace/Basic.lean` (riemann-roch-function-fields)
- [x] Ramification index — §2, Hurwitz’s Theorem, pp. 299–306
  - `Ideal.ramificationIdx` — `Mathlib/RingTheory/RamificationInertia/Basic.lean`
- [x] Ramification divisor — §2, Hurwitz’s Theorem, pp. 299–306
  - `CurveMorphismData.ramificationDivisor` — `Atlas/AlgebraicGeometryI/code/RamificationDivisor.lean` (atlas-lean)
  - `ramificationDivisorDegreeAt` — `Atlas/AlgebraicGeometryI/code/RiemannHurwitzFormula.lean`; `globalRamification` — `Atlas/AlgebraicGeometryI/code/CanonicalDivisorDecomposition.lean`
- [ ] Base point of a linear system — §3, Embeddings in Projective Space, pp. 307–315
  - Partial reference: linear systems exist: `completeLinearSystem` — `TauCeti/AlgebraicGeometry/WeilDivisor/LinearSystem/Basic.lean` (TauCeti); no base-point def
- [ ] Base-point-free linear system — §3, Embeddings in Projective Space, pp. 307–315
- [x] Elliptic curve — §4, Elliptic Curves, pp. 316–339
  - `WeierstrassCurve` — `Mathlib/AlgebraicGeometry/EllipticCurve/Weierstrass.lean`
- [x] Isogeny of elliptic curves — §4, Elliptic Curves, pp. 316–339
  - `EllipticCurveIsogeny` — `Atlas/ArithmeticGeometry/code/Isogenies.lean`
- [x] Frobenius morphism of an elliptic curve — §4, Elliptic Curves, pp. 316–339
  - `frobeniusIsogeny` — `Atlas/EllipticCurves/code/WeilPairing.lean` (atlas-lean)
  - `frobeniusPointMap` — `Atlas/EllipticCurves/code/FrobeniusEndomorphism.lean`
  - Mathlib ring-endomorphism: `LinearMap.frobenius` — `Mathlib/Algebra/CharP/Frobenius.lean`
- [ ] Canonical map of a curve — §5, The Canonical Embedding, pp. 340–348
  - Partial reference: canonical sheaf/class exist, the map does not: `canonicalSheafClass`/`canonicalDeg` — `Atlas/AlgebraicGeometryI/code/CanonicalSheafCurves.lean`; `canonicalDivisorClass_dedekind` — `Atlas/AlgebraicGeometryI/code/CanonicalDivisorCurves.lean`; `canonicalModule` — `Atlas/AlgebraicGeometryI/code/CanonicalSheafDef.lean` (atlas-lean)
- [x] Hyperelliptic curve — §5, The Canonical Embedding, pp. 340–348
  - `hyperellipticData` (degree-two cover with branch data) — `Atlas/AlgebraicGeometryI/code/RiemannHurwitzFormula.lean` (atlas-lean)
  - `genus_hyperelliptic_from_curves`/`hyperelliptic_genus_from_branch_points` — `Atlas/AlgebraicGeometryI/code/RiemannHurwitzDegree.lean`

## Chapter V. Surfaces

- [ ] Surface — §1, Geometry on a Surface, pp. 357–368
- [ ] Intersection number of divisors on a surface — §1, Geometry on a Surface, pp. 357–368
  - Partial reference: projective plane curves only: `localIntersectionMultiplicity`/`totalIntersectionNumber`/`bezout_theorem` — `Atlas/AlgebraicGeometryI/code/BezoutIntersection.lean` (atlas-lean)
- [ ] Numerical equivalence of divisors — §1, Geometry on a Surface, pp. 357–368
  - Partial reference: algebraic equivalence via `SPoint`/`ConnectedVariety` — `Atlas/AlgebraicGeometryI/code/AlgebraicEquivalence.lean` (atlas-lean); no numerical-equivalence def
- [ ] Néron–Severi group — §1, Geometry on a Surface, pp. 357–368
- [ ] Arithmetic genus of a surface — §1, Geometry on a Surface, pp. 357–368
  - Partial reference: `arithmeticGenusP1` (ℙ¹ only) — `Atlas/AlgebraicGeometryI/code/ArithmeticGeometricGenus.lean` (atlas-lean)
- [ ] Geometric genus of a surface — §1, Geometry on a Surface, pp. 357–368
  - Partial reference: `geometricGenusP1` (ℙ¹ only) — `Atlas/AlgebraicGeometryI/code/ArithmeticGeometricGenus.lean` (atlas-lean)
- [ ] Irregularity of a surface — §1, Geometry on a Surface, pp. 357–368
- [ ] Ruled surface — §2, Ruled Surfaces, pp. 369–385
- [ ] Geometrically ruled surface — §2, Ruled Surfaces, pp. 369–385
- [ ] Normalized locally free sheaf on a curve — §2, Ruled Surfaces, pp. 369–385
- [x] Monoidal transformation — §3, Monoidal Transformations, pp. 386–394
  - `blowupScheme`/`blowupProjection`/`blowupAtPoint` — `Atlas/AlgebraicGeometryI/code/BlowupAtPoint.lean` (atlas-lean)
  - Affine case: `Blowup.blowupAlong` — `Atlas/AlgebraicGeometryI/code/BlowupDefinition.lean`
- [x] Exceptional curve — §3, Monoidal Transformations, pp. 386–394
  - `exceptionalLocus`/`blowupExceptionalLocus` — `Atlas/AlgebraicGeometryI/code/BlowupAtPoint.lean` (atlas-lean)
- [x] Birational transformation of surfaces — §5, Birational Transformations, pp. 409–420
  - `IsBirational` — `Atlas/AlgebraicGeometryI/code/ChowsLemma.lean` (atlas-lean)
  - Mathlib: `AlgebraicGeometry.Birational` — `Mathlib/AlgebraicGeometry/Birational/Birational.lean`
- [ ] Contractible curve — §5, Birational Transformations, pp. 409–420
- [ ] Relatively minimal model — §5, Birational Transformations, pp. 409–420
- [ ] Minimal model — §5, Birational Transformations, pp. 409–420
- [ ] Kodaira dimension — §6, Classification of Surfaces, pp. 421–423
- [ ] Surface of general type — §6, Classification of Surfaces, pp. 421–423
