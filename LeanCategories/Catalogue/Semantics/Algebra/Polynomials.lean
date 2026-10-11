/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Catalogue.Semantics.Algebra.Semirings
public import LeanCategories.Catalogue.Semantics.Foundation.FiniteSubsets
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.RingTheory.Polynomial.UniqueFactorization
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.Data.Int.CharZero
public import Mathlib.Algebra.Category.Ring.Under.Basic
public import LeanCategories.Catalogue.Semantics.Algebra.PolynomialEvidence
public import Mathlib.Tactic.ComputeDegree
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Tactic.Ring
public meta import LeanCategories.Catalogue.Registry.Semantic
public meta import LeanCategories.Catalogue.Semantics.Foundation.Evidence
public meta import LeanCategories.Catalogue.Semantics.Algebra.Units

@[expose] public section

/-!
# Polynomials (SPEC.md, "Polynomials")

For a commutative ring `R`, `R[x]` is the set of polynomials over `R` (Mathlib `Polynomial R`),
refined by the ring `R[x]`, with
* its generator `x : 1 → R[x]` (Mathlib `Polynomial.X`), its constants
  `R ↪ R[x]` (Mathlib `Polynomial.C`), and
* its application `R[x] × A → A` at an `R`-algebra `A`, `(p, a) ↦ p(a)` (Mathlib
  `Polynomial.aeval`).

Functions of polynomials, as named morphism families of `Sets` over their rings:
* `deg : R[x] → ℕ ∪ {-∞}` (Mathlib `Polynomial.degree`; `deg 0 = -∞`);
* `R[x] ∖ {0} ↪ R[x]`, the nonzero polynomials; a polynomial is in `R[x] ∖ {0}` only with the
  evidence that it is nonzero;
* `factors : R[x] ∖ {0} → 𝒫_fin(R[x])`, the normalized irreducible factors over a unique
  factorization domain (Mathlib `UniqueFactorizationMonoid.normalizedFactors`). The zero
  polynomial has no factorization into irreducibles, so `0` is not in the domain (Mathlib's
  `normalizedFactors 0 = 0` is a convention, LC-14);
* `roots : R[x] ∖ {0} → 𝒫_fin(R)`, the roots in a domain `R` (Mathlib `Polynomial.roots`),
  finitely many for a nonzero polynomial. Every element of `R` is a root of `0`, so `0` is not in
  the domain (Mathlib's `roots 0 = ∅` is a convention, LC-14);
* `map : R[x] → S[x]` along an `R`-algebra `S` (Mathlib `Polynomial.map f.hom`).
-/

open CategoryTheory Polynomial

namespace CasCatalogue.Algebra.Polynomials

open CasCatalogue.Foundation.PowerSets CasCatalogue.Foundation.Objects

/-- `R[x]`. -/
abbrev polynomials (R : CommRingCat.{0}) : SetsCat.{0} := Polynomial R

/-- The variable `x ∈ R[x]`. -/
noncomputable def generator (R : CommRingCat.{0}) : fin 1 ⟶ polynomials R :=
  TypeCat.ofHom fun _ => X

/-- The constants `R ↪ R[x]` (Mathlib `Polynomial.C`), injective. -/
noncomputable def coefficients (R : CommRingCat.{0}) : (R : SetsCat.{0}) ⟶ polynomials R :=
  TypeCat.ofHom (C : R →+* Polynomial R)

/-- `(p, a) ↦ p(a)`, `R[x] × A → A`. -/
noncomputable def evaluation (R : CommRingCat.{0}) (A : Under R) :
    (polynomials R × A : SetsCat.{0}) ⟶ (A : SetsCat.{0}) :=
  TypeCat.ofHom fun p => aeval p.2 p.1

/-- Evaluation in the selected coefficient ring itself, using its identity map.
No further algebra structure or coefficient homomorphism is inferred from a carrier. -/
noncomputable def ownEvaluation (R : CommRingCat.{0}) :
    (polynomials R × R : SetsCat.{0}) ⟶ (R : SetsCat.{0}) :=
  TypeCat.ofHom fun pa => pa.1.eval pa.2

/-- Evaluation along an explicitly selected coefficient map. An endomorphism of the
same ring is retained just as any other map; it is not replaced by the identity. -/
noncomputable def evaluationAlong (R A : CommRingCat.{0}) (f : R ⟶ A) :
    (polynomials R × A : SetsCat.{0}) ⟶ (A : SetsCat.{0}) :=
  TypeCat.ofHom fun pa => pa.1.eval₂ f.hom pa.2

/-- The existing algebra application uses precisely the selected coefficient map. -/
theorem evaluation_selected (R : CommRingCat.{0}) (A : Under R) :
    evaluation R A = evaluationAlong R A.right A.hom := rfl

/-- Canonical coefficient-ring evaluation is exactly the identity-map specialization. -/
theorem evaluationAlong_identity (R : CommRingCat.{0}) :
    evaluationAlong R R (𝟙 R) = ownEvaluation R := rfl

/-- The canonical selected algebra for own-ring evaluation has identity coefficient map. -/
theorem evaluation_own (R : CommRingCat.{0}) :
    evaluation R (Under.mk (𝟙 R)) = ownEvaluation R := rfl

@[simp] theorem ownEvaluation_constant (R : CommRingCat.{0}) (c a : R) :
    ownEvaluation R (C c, a) = c := Polynomial.eval_C

@[simp] theorem evaluationAlong_constant (R A : CommRingCat.{0}) (f : R ⟶ A)
    (c : R) (a : A) : evaluationAlong R A f (C c, a) = f.hom c := Polynomial.eval₂_C f.hom a

@[simp] theorem evaluationAlong_variable (R A : CommRingCat.{0}) (f : R ⟶ A) (a : A) :
    evaluationAlong R A f (X, a) = a := Polynomial.eval₂_X f.hom a

/-- Polynomial operations and their results can be evaluated along the same selected map. -/
theorem evaluationAlong_mul (R A : CommRingCat.{0}) (f : R ⟶ A)
    (p q : Polynomial R) (a : A) :
    evaluationAlong R A f (p * q, a) =
      evaluationAlong R A f (p, a) * evaluationAlong R A f (q, a) :=
  Polynomial.eval₂_mul f.hom a

/-- Distinct maps on one carrier give distinct coefficient evaluations. -/
example :
    let R := CommRingCat.of (ℤ × ℤ)
    let swap : R ⟶ R :=
      CommRingCat.ofHom (RingEquiv.prodComm : (ℤ × ℤ) ≃+* (ℤ × ℤ)).toRingHom
    evaluationAlong R R swap (C (1, 0), (0, 0)) = (0, 1) ∧
      ownEvaluation R (C (1, 0), (0, 0)) = (1, 0) := by
  constructor <;> simp [evaluationAlong, ownEvaluation]

/-- Evaluation transports along a composite of the actual selected coefficient maps. -/
theorem evaluationAlong_composition (R A B : CommRingCat.{0}) (f : R ⟶ A) (g : A ⟶ B)
    (p : Polynomial R) (a : A) :
    g.hom (evaluationAlong R A f (p, a)) =
      evaluationAlong R B (f ≫ g) (p, g.hom a) :=
  Polynomial.hom_eval₂ p f.hom g.hom a

/-- `R[x]` as a ring. -/
noncomputable abbrev ringPolynomials (R : CommRingCat.{0}) : LeanCategories.Algebra.Rings.{0} :=
  RingCat.of (Polynomial R)

/-- The underlying set of the ring `R[x]` is `R[x]`. -/
def ringPolynomialsIdentification (R : CommRingCat.{0}) :
    (polynomials R : SetsCat.{0}) ≅ polynomials R :=
  Iso.refl _

/-- `ℕ ∪ {-∞}`, the degrees. -/
abbrev degrees : SetsCat.{0} := WithBot ℕ

/-- `k ∈ ℕ ∪ {-∞}`. -/
def naturalsDegrees : naturals ⟶ degrees := TypeCat.ofHom (fun k : ℕ => (k : WithBot ℕ))

theorem naturalsDegrees_mono : Mono naturalsDegrees :=
  NumberSystems.mono_of_injective _ WithBot.coe_injective

/-- `deg : R[x] → ℕ ∪ {-∞}`. -/
noncomputable def degree (R : CommRingCat.{0}) : (polynomials R : SetsCat.{0}) ⟶ degrees :=
  TypeCat.ofHom Polynomial.degree

/-- `R[x] ∖ {0}`, the nonzero polynomials. -/
abbrev nonzeroPolynomials (R : CommRingCat.{0}) : SetsCat.{0} := {p : Polynomial R // p ≠ 0}

/-- `R[x] ∖ {0} ↪ R[x]`. -/
def nonzeroPolynomialsInclusion (R : CommRingCat.{0}) :
    nonzeroPolynomials R ⟶ polynomials R :=
  TypeCat.ofHom Subtype.val

/-- The nonzero polynomial `p`, with the evidence that `p ≠ 0`. -/
def admitNonzeroPolynomial (R : CommRingCat.{0}) (p : Polynomial R) (h : p ≠ 0) :
    fin 1 ⟶ nonzeroPolynomials R :=
  TypeCat.ofHom fun _ => ⟨p, h⟩

open Classical in
/-- The normalized irreducible factors `R[x] ∖ {0} → 𝒫_fin(R[x])`. -/
noncomputable def factors (R : CommRingCat.{0}) [IsDomain R] [NormalizationMonoid R]
    [UniqueFactorizationMonoid R] :
    nonzeroPolynomials R ⟶ Foundation.FiniteSubsets.finiteSubsets (Polynomial R) :=
  TypeCat.ofHom fun p => (UniqueFactorizationMonoid.normalizedFactors p.1).toFinset

/-- Reusable factorization data over the selected coefficient ring. Multiplicities and the
unit are data. Product and irreducibility laws are specifications, not fields to be supplied
by a computational implementation. -/
abbrev factorizationData (R : CommRingCat.{0}) : SetsCat.{0} :=
  (Polynomial R)ˣ × Multiset (Polynomial R)

/-- Polynomial multisets retain repeated factors. -/
abbrev factorMultisets (R : CommRingCat.{0}) : SetsCat.{0} := Multiset (Polynomial R)

/-- Full factorization, unlike `factors`, retains multiplicity and the unit. -/
noncomputable def factorization (R : CommRingCat.{0}) [IsDomain R] [NormalizationMonoid R]
    [UniqueFactorizationMonoid R] : nonzeroPolynomials R ⟶ factorizationData R :=
  TypeCat.ofHom fun p =>
    ⟨Classical.choose (UniqueFactorizationMonoid.prod_normalizedFactors p.2),
      UniqueFactorizationMonoid.normalizedFactors p.1⟩

/-- The unit as a polynomial, immediately usable by polynomial operations. -/
def factorizationUnit (R : CommRingCat.{0}) : factorizationData R ⟶ polynomials R :=
  TypeCat.ofHom fun d => (d.1 : Polynomial R)

/-- The factors with their multiplicities. -/
def factorizationFactors (R : CommRingCat.{0}) : factorizationData R ⟶ factorMultisets R :=
  TypeCat.ofHom Prod.snd

/-- Reconstruct a polynomial from reusable data; this operation is defined for every datum. -/
noncomputable def factorizationProduct (R : CommRingCat.{0}) :
    factorizationData R ⟶ polynomials R :=
  TypeCat.ofHom fun d => d.2.prod * (d.1 : Polynomial R)

/-- The full factorization reconstructs the actual input polynomial. -/
theorem factorization_product (R : CommRingCat.{0}) [IsDomain R] [NormalizationMonoid R]
    [UniqueFactorizationMonoid R] (p : nonzeroPolynomials R) :
    (factorization R ≫ factorizationProduct R) p = p.1 :=
  Classical.choose_spec (UniqueFactorizationMonoid.prod_normalizedFactors p.2)

/-- The factor entries of the canonical result are irreducible. This law is not a
proof-producing component of the computational result. -/
theorem factorization_irreducible (R : CommRingCat.{0}) [IsDomain R]
    [NormalizationMonoid R] [UniqueFactorizationMonoid R] (p : nonzeroPolynomials R)
    (q : Polynomial R) (hq : q ∈ (factorization R p).2) : Irreducible q :=
  (UniqueFactorizationMonoid.prime_of_normalized_factor q hq).irreducible

/-- Repeated factors survive reconstruction and can be reused by ordinary evaluation. -/
example :
    let R := CommRingCat.of ℤ
    let d : factorizationData R := (1, {X - 1, X - 1})
    (factorizationProduct R d).eval 3 = 4 := by
  simp [factorizationProduct, Polynomial.eval_sub, Polynomial.eval_X]

/-- Change coefficients of reusable data, preserving its unit and repeated factors.
The mapped factors need not remain irreducible over the new ring. -/
noncomputable def factorizationMap (R S : CommRingCat.{0}) (f : R ⟶ S) :
    factorizationData R ⟶ factorizationData S :=
  TypeCat.ofHom fun d =>
    ⟨Units.map (Polynomial.mapRingHom f.hom).toMonoidHom d.1,
      d.2.map (Polynomial.map f.hom)⟩


open Classical in
/-- The roots `R[x] ∖ {0} → 𝒫_fin(R)`, finitely many for a nonzero polynomial over a domain `R`
(Mathlib `Polynomial.roots`, `Polynomial.mem_roots`). -/
noncomputable def roots (R : CommRingCat.{0}) [IsDomain R] :
    nonzeroPolynomials R ⟶ Foundation.FiniteSubsets.finiteSubsets R :=
  TypeCat.ofHom fun p => p.1.roots.toFinset

/-- The roots of a nonzero `p` are exactly the `a` with `p(a) = 0`. -/
theorem mem_roots (R : CommRingCat.{0}) [IsDomain R] (p : nonzeroPolynomials R) (a : R) :
    a ∈ ConcreteCategory.hom (C := Type) (roots R) p ↔ IsRoot p.1 a := by
  simp [roots, Polynomial.mem_roots p.2]

/-- The existing finite root operation retains precisely its defining comprehension.
It is the same extent admitted by `FiniteSubsets.admit`, rather than a new root set. -/
theorem roots_extent (R : CommRingCat.{0}) [IsDomain R] (p : nonzeroPolynomials R) :
    (ConcreteCategory.hom (C := Type) (roots R) p : Set R) =
      {a | p.1.eval a = 0} := by
  ext a
  exact mem_roots R p a

/-- Admitting the root comprehension recovers exactly the existing finite-root value. -/
theorem admit_roots (R : CommRingCat.{0}) [IsDomain R] (p : nonzeroPolynomials R)
    (x : CasCatalogue.Foundation.Objects.fin 1) :
    ConcreteCategory.hom (C := Type)
      (Foundation.FiniteSubsets.admit R {a | p.1.eval a = 0}
        (Foundation.FiniteSubsets.finite_polynomial_zeros p.1 p.2)) x =
      ConcreteCategory.hom (C := Type) (roots R) p := by
  apply Finset.coe_injective
  exact (Set.Finite.coe_toFinset _).trans (roots_extent R p).symm

/-- `map : R[x] → S[x]` along `R → S`. -/
noncomputable def map (R S : CommRingCat.{0}) (f : R ⟶ S) :
    (polynomials R : SetsCat.{0}) ⟶ polynomials S :=
  TypeCat.ofHom (Polynomial.map f.hom)

/-- Coefficient change followed by own-ring evaluation equals evaluation along that
actual selected coefficient map, including nonidentity same-carrier maps. -/
theorem evaluationAlong_map (R A : CommRingCat.{0}) (f : R ⟶ A)
    (p : Polynomial R) (a : A) :
    evaluationAlong R A f (p, a) = ownEvaluation A (map R A f p, a) :=
  Polynomial.eval₂_eq_eval_map f.hom

/-- Reconstruction commutes with coefficient change. -/
theorem factorizationMap_product (R S : CommRingCat.{0}) (f : R ⟶ S)
    (d : factorizationData R) :
    (factorizationMap R S f ≫ factorizationProduct S) d =
      (factorizationProduct R ≫ map R S f) d := by
  change (d.2.map (Polynomial.mapRingHom f.hom)).prod *
      (Polynomial.mapRingHom f.hom) (d.1 : Polynomial R) =
    (Polynomial.mapRingHom f.hom) (d.2.prod * (d.1 : Polynomial R))
  rw [map_mul, map_multiset_prod]

end CasCatalogue.Algebra.Polynomials

namespace CasCatalogue

normalized_registry .object
  { id := ⟨"obj.sets.polynomials"⟩, category := CategoryId.sets, name := "Poly"
    declaration := `CasCatalogue.Algebra.Polynomials.polynomials
    generator := some `CasCatalogue.Algebra.Polynomials.generator
    application := some `CasCatalogue.Algebra.Polynomials.evaluation
    constants := some `CasCatalogue.Algebra.Polynomials.coefficients }

normalized_registry .object
  { id := ⟨"obj.rings.polynomials"⟩, category := CategoryId.rings, name := "Poly"
    declaration := `CasCatalogue.Algebra.Polynomials.ringPolynomials
    refines := some
      { base := ⟨"obj.sets.polynomials"⟩, route := ringsToSets
        identification := `CasCatalogue.Algebra.Polynomials.ringPolynomialsIdentification } }

normalized_registry .object
  { id := ⟨"obj.sets.degrees"⟩, category := CategoryId.sets, name := "ℕ∪{-∞}"
    declaration := `CasCatalogue.Algebra.Polynomials.degrees }

normalized_registry .inclusion
  { id := ⟨"incl.sets.naturals_degrees"⟩, category := CategoryId.sets
    sub := ⟨"obj.sets.naturals"⟩, super := ⟨"obj.sets.degrees"⟩
    declaration := `CasCatalogue.Algebra.Polynomials.naturalsDegrees
    mono := `CasCatalogue.Algebra.Polynomials.naturalsDegrees_mono }

normalized_registry .morphism
  { id := ⟨"mor.sets.polynomial_degree"⟩, category := CategoryId.sets, name := "deg"
    declaration := `CasCatalogue.Algebra.Polynomials.degree }

normalized_registry .object
  { id := ⟨"obj.sets.nonzero_polynomials"⟩, category := CategoryId.sets, name := "Poly∖0"
    declaration := `CasCatalogue.Algebra.Polynomials.nonzeroPolynomials
    inclusion := some `CasCatalogue.Algebra.Polynomials.nonzeroPolynomialsInclusion
    admission := some `CasCatalogue.Algebra.Polynomials.admitNonzeroPolynomial
    evidence := some `CasCatalogue.Algebra.Polynomials.nonzeroPolynomialEvidence }

normalized_registry .morphism
  { id := ⟨"mor.sets.polynomial_factors"⟩, category := CategoryId.sets, name := "factors"
    declaration := `CasCatalogue.Algebra.Polynomials.factors }

normalized_registry .object
  { id := ⟨"obj.sets.polynomial_factorization_data"⟩, category := CategoryId.sets
    name := "PolynomialFactorization"
    declaration := `CasCatalogue.Algebra.Polynomials.factorizationData }

normalized_registry .object
  { id := ⟨"obj.sets.polynomial_factor_multisets"⟩, category := CategoryId.sets
    name := "PolynomialFactorMultiset"
    declaration := `CasCatalogue.Algebra.Polynomials.factorMultisets }

normalized_registry .morphism
  { id := ⟨"mor.sets.polynomial_factorization"⟩, category := CategoryId.sets
    name := "factorization", declaration := `CasCatalogue.Algebra.Polynomials.factorization }

normalized_registry .morphism
  { id := ⟨"mor.sets.polynomial_factorization_unit"⟩, category := CategoryId.sets
    name := "unit", declaration := `CasCatalogue.Algebra.Polynomials.factorizationUnit }

normalized_registry .morphism
  { id := ⟨"mor.sets.polynomial_factorization_factors"⟩, category := CategoryId.sets
    name := "factors_with_multiplicity"
    declaration := `CasCatalogue.Algebra.Polynomials.factorizationFactors }

normalized_registry .morphism
  { id := ⟨"mor.sets.polynomial_factorization_product"⟩, category := CategoryId.sets
    name := "product", declaration := `CasCatalogue.Algebra.Polynomials.factorizationProduct }

normalized_registry .morphism
  { id := ⟨"mor.sets.polynomial_factorization_map"⟩, category := CategoryId.sets
    name := "map_factorization", declaration := `CasCatalogue.Algebra.Polynomials.factorizationMap }

normalized_registry .morphism
  { id := ⟨"mor.sets.polynomial_roots"⟩, category := CategoryId.sets, name := "roots"
    declaration := `CasCatalogue.Algebra.Polynomials.roots }

normalized_registry .morphism
  { id := ⟨"mor.sets.polynomial_map"⟩, category := CategoryId.sets, name := "map"
    declaration := `CasCatalogue.Algebra.Polynomials.map }

normalized_registry .morphism
  { id := ⟨"mor.sets.polynomial_own_evaluation"⟩, category := CategoryId.sets
    name := "evaluate", declaration := `CasCatalogue.Algebra.Polynomials.ownEvaluation }

normalized_registry .morphism
  { id := ⟨"mor.sets.polynomial_selected_evaluation"⟩, category := CategoryId.sets
    name := "evaluate_along", declaration := `CasCatalogue.Algebra.Polynomials.evaluationAlong }

end CasCatalogue
