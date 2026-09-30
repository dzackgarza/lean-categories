/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Algebra.Concrete.RingElements
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Algebra.Polynomial.FieldDivision
public import Mathlib.RingTheory.Polynomial.UniqueFactorization
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

@[expose] public section

/-!
# Polynomials as elements, and their operations

`R ↦ R[X]` is a functor on commutative rings (`Polynomial.mapRingHom`). It restricts to domains,
to unique factorization domains (`R[X]` is a UFD when `R` is) and sends fields to euclidean domains
(`K[X]` is euclidean). The points of each (`IsoElements` of the underlying set of `R[X]`) are
polynomials over a ring of that class, up to isomorphism of the coefficient ring:

* `PolyPoints`: over commutative rings; `derivative`, `antiderivatives`, `degree`,
  `companionMatrices`;
* `DomainPolyPoints`: over domains; `roots`;
* `UFDPolyPoints`: over UFDs, with an edge to the elements of UFDs (`R[X]` is one);
* `FieldPolyPoints`: over fields, with edges to the elements of euclidean domains and to the
  polynomials over domains.

Operations whose answer is a choice take as value the set of admissible answers: the
antiderivatives of `p` (those `F` with `F' = p`, empty when there is none), and the matrices of
size `deg p` with characteristic polynomial `p` (the companion matrices are among them).
-/

open CategoryTheory LeanCategories.Foundation Polynomial

namespace LeanCategories.Algebra

universe u

noncomputable section

/-! ### The polynomial functors -/

/-- `R ↦ R[X]` on commutative rings. -/
def polynomialFunctor : CommRingCat.{u} ⥤ CommRingCat.{u} where
  obj R := CommRingCat.of R[X]
  map f := CommRingCat.ofHom (mapRingHom f.hom)
  map_id R := CommRingCat.hom_ext Polynomial.mapRingHom_id
  map_comp f g := CommRingCat.hom_ext (Polynomial.mapRingHom_comp g.hom f.hom).symm

/-- The underlying set of `R[X]`. -/
abbrev polyCarrier : CommRingCat.{u} ⥤ Type u := polynomialFunctor ⋙ ringCarrier

/-- A domain as a commutative ring. -/
abbrev domainToCommRing : DomainCat.{u} ⥤ CommRingCat.{u} := ObjectProperty.ι _

/-- The underlying set of `R[X]` for a domain `R`. -/
abbrev domainPolyCarrier : DomainCat.{u} ⥤ Type u := domainToCommRing ⋙ polyCarrier

/-- A UFD is a domain. -/
def ufdToDomain : UniqueFactorizationDomains.{u} ⥤ DomainCat.{u} :=
  ObjectProperty.ιOfLE fun _ h => h.1

/-- A field is a domain. -/
def fieldToDomain : FieldCat.{u} ⥤ DomainCat.{u} :=
  ObjectProperty.ιOfLE fun _ h => h.isDomain

/-- `R ↦ R[X]` on unique factorization domains. -/
def ufdPolynomial : UniqueFactorizationDomains.{u} ⥤ UniqueFactorizationDomains.{u} :=
  ObjectProperty.lift _ (ufdToCommRing ⋙ polynomialFunctor) fun R => by
    obtain ⟨_, _⟩ := R.property
    exact ⟨inferInstanceAs (IsDomain R.obj[X]), inferInstanceAs (UniqueFactorizationMonoid R.obj[X])⟩

theorem polynomial_isEuclideanRing (K : FieldCat.{u}) :
    IsEuclideanRing (polynomialFunctor.obj K.obj) := by
  exact ⟨@Polynomial.instEuclideanDomain K.obj K.property.toField, rfl⟩

/-- `K ↦ K[X]` sends fields to euclidean domains. -/
def fieldPolynomial : FieldCat.{u} ⥤ EuclideanRings.{u} :=
  ObjectProperty.lift _ (ObjectProperty.ι _ ⋙ polynomialFunctor) polynomial_isEuclideanRing

/-! ### Points -/

/-- Polynomials over commutative rings, up to isomorphism of the coefficient ring. -/
abbrev PolyPoints := IsoElements polyCarrier.{u}
/-- Polynomials over domains. -/
abbrev DomainPolyPoints := IsoElements domainPolyCarrier.{u}
/-- Polynomials over unique factorization domains. -/
abbrev UFDPolyPoints := IsoElements (ufdPolynomial.{u} ⋙ ufdCarrier)
/-- Polynomials over fields. -/
abbrev FieldPolyPoints := IsoElements (fieldPolynomial.{u} ⋙ euclideanCarrier)

/-- A polynomial over a domain is a polynomial over a commutative ring. -/
def domainPolyToPoly : DomainPolyPoints.{u} ⥤ PolyPoints.{u} :=
  IsoElements.restrict domainToCommRing polyCarrier
/-- A polynomial over a UFD is a polynomial over a domain. -/
def ufdPolyToDomainPoly : UFDPolyPoints.{u} ⥤ DomainPolyPoints.{u} :=
  IsoElements.restrict ufdToDomain domainPolyCarrier
/-- A polynomial over a UFD is an element of the UFD `R[X]`. -/
def ufdPolyToUFDPoints : UFDPolyPoints.{u} ⥤ UFDPoints.{u} :=
  IsoElements.restrict ufdPolynomial ufdCarrier
/-- A polynomial over a field is a polynomial over a domain. -/
def fieldPolyToDomainPoly : FieldPolyPoints.{u} ⥤ DomainPolyPoints.{u} :=
  IsoElements.restrict fieldToDomain domainPolyCarrier
/-- A polynomial over a field is an element of the euclidean domain `K[X]`. -/
def fieldPolyToEuclideanPoints : FieldPolyPoints.{u} ⥤ EuclideanPoints.{u} :=
  IsoElements.restrict fieldPolynomial euclideanCarrier

/-! ### Operations -/

namespace Poly

/-- The ring isomorphism underlying an isomorphism of commutative rings. -/
abbrev ringEquiv {R S : CommRingCat.{u}} (φ : R ≅ S) : R ≃+* S := φ.commRingCatIsoToRingEquiv

theorem map_symm_map {R S : Type u} [CommRing R] [CommRing S] (e : R ≃+* S) (p : R[X]) :
    (p.map e.toRingHom).map e.symm.toRingHom = p := by
  rw [Polynomial.map_map, RingEquiv.symm_toRingHom_comp_toRingHom, Polynomial.map_id]

theorem map_map_symm {R S : Type u} [CommRing R] [CommRing S] (e : R ≃+* S) (p : S[X]) :
    (p.map e.symm.toRingHom).map e.toRingHom = p := by
  rw [Polynomial.map_map, RingEquiv.toRingHom_comp_symm_toRingHom, Polynomial.map_id]

theorem polyCarrier_map_apply {R S : CommRingCat.{u}} (f : R ⟶ S) (p : R[X]) :
    polyCarrier.map f p = p.map f.hom := rfl

/-- `derivative`, natural under isomorphisms of the coefficient ring. -/
def derivativeMethod : PolyPoints.{u} ⥤ (Core.inclusion _ ⋙ polyCarrier.{u}).Elements :=
  IsoElements.isoNatural polyCarrier (Core.inclusion _ ⋙ polyCarrier)
    (fun _ p => Polynomial.derivative p) fun φ p => by
      change Polynomial.derivative (p.map φ.iso.hom.hom) =
        (Polynomial.derivative p).map φ.iso.hom.hom
      exact derivative_map p φ.iso.hom.hom

/-- `degree`, invariant under isomorphisms of the coefficient ring. -/
def degreeMethod : PolyPoints.{u} ⥤ Discrete (WithBot ℕ) :=
  IsoElements.isoInvariant polyCarrier (fun _ p => Polynomial.degree p) fun φ p =>
    degree_map_eq_of_injective (ringEquiv φ).injective p

/-- The antiderivatives of `p`: the `F` with `F' = p`. -/
def antiderivativeSet (R : CommRingCat.{u}) (p : R[X]) : Set R[X] :=
  {F | Polynomial.derivative F = p}

/-- `antiderivatives`, natural under isomorphisms of the coefficient ring. -/
def antiderivativesMethod :
    PolyPoints.{u} ⥤ (Core.inclusion _ ⋙ polyCarrier.{u} ⋙ powersetFunctor).Elements :=
  IsoElements.isoNatural polyCarrier (Core.inclusion _ ⋙ polyCarrier ⋙ powersetFunctor)
    (fun R p => antiderivativeSet R p) fun {X Y} φ p => by
      change antiderivativeSet Y.of (p.map φ.iso.hom.hom) =
        (fun F => F.map φ.iso.hom.hom) '' antiderivativeSet X.of p
      set e := ringEquiv φ.iso
      ext F
      constructor
      · intro hF
        change Polynomial.derivative F = p.map e.toRingHom at hF
        refine ⟨F.map e.symm.toRingHom, ?_, ?_⟩
        · change Polynomial.derivative (F.map e.symm.toRingHom) = p
          rw [derivative_map, hF]
          exact map_symm_map e p
        · change (F.map e.symm.toRingHom).map e.toRingHom = F
          exact map_map_symm e F
      · rintro ⟨G, hG, rfl⟩
        change Polynomial.derivative G = p at hG
        change Polynomial.derivative (G.map e.toRingHom) = p.map e.toRingHom
        rw [derivative_map, hG]

/-- Square matrices of any size over `R`, transported entrywise. -/
def squareMatrices : CommRingCat.{u} ⥤ Type u :=
  typeFunctor (fun R => Σ n : ℕ, Matrix (Fin n) (Fin n) R) (fun f M => ⟨M.1, M.2.map f.hom⟩)
    (fun _ M => by cases M; rfl)
    (fun f g M => by cases M; simp [Matrix.map_map])

/-- The matrices of size `natDegree p` whose characteristic polynomial is `p` (for monic `p`, the
companion matrices are among them; for non-monic `p` there are none). -/
def companionSet (R : CommRingCat.{u}) (p : R[X]) : Set (Σ n : ℕ, Matrix (Fin n) (Fin n) R) :=
  {M | M.1 = p.natDegree ∧ M.2.charpoly = p}

/-- `companion_matrix`, natural under isomorphisms of the coefficient ring. -/
def companionMethod :
    PolyPoints.{u} ⥤ (Core.inclusion _ ⋙ squareMatrices.{u} ⋙ powersetFunctor).Elements :=
  IsoElements.isoNatural polyCarrier (Core.inclusion _ ⋙ squareMatrices ⋙ powersetFunctor)
    (fun R p => companionSet R p) fun {X Y} φ p => by
      change companionSet Y.of (p.map φ.iso.hom.hom) =
        (fun M => ⟨M.1, M.2.map φ.iso.hom.hom⟩) '' companionSet X.of p
      set e := ringEquiv φ.iso
      have hdeg : (p.map e.toRingHom).natDegree = p.natDegree :=
        natDegree_map_eq_of_injective e.injective p
      ext ⟨n, M⟩
      constructor
      · rintro ⟨hn, hM⟩
        change n = (p.map e.toRingHom).natDegree at hn
        change M.charpoly = p.map e.toRingHom at hM
        refine ⟨⟨n, M.map e.symm⟩, ⟨?_, ?_⟩, ?_⟩
        · change n = p.natDegree
          rw [hn, hdeg]
        · change (M.map e.symm.toRingHom).charpoly = p
          rw [Matrix.charpoly_map, hM]
          exact map_symm_map e p
        · change (⟨n, (M.map e.symm).map e⟩ : Σ n : ℕ, Matrix (Fin n) (Fin n) Y.of) = ⟨n, M⟩
          congr 1
          ext i j; simp
      · rintro ⟨⟨m, N⟩, ⟨hm, hN⟩, h⟩
        change m = p.natDegree at hm
        change N.charpoly = p at hN
        cases h
        refine ⟨?_, ?_⟩
        · change m = (p.map e.toRingHom).natDegree
          rw [hm, hdeg]
        · change (N.map e.toRingHom).charpoly = p.map e.toRingHom
          rw [Matrix.charpoly_map, hN]

instance (R : DomainCat.{u}) : IsDomain R.obj := R.property
instance (R : DomainCat.{u}) : IsDomain (domainToCommRing.obj R) := R.property

/-- The roots of `p`, with multiplicity. -/
def rootsOf (R : DomainCat.{u}) (p : R.obj[X]) : Multiset R.obj := p.roots

/-- `roots`, natural under isomorphisms of the coefficient domain. -/
def rootsMethod : DomainPolyPoints.{u} ⥤ (Core.inclusion _ ⋙ domainToCommRing ⋙ ringCarrier ⋙
    multisetFunctor).Elements :=
  IsoElements.isoNatural domainPolyCarrier
    (Core.inclusion _ ⋙ domainToCommRing ⋙ ringCarrier ⋙ multisetFunctor)
    (fun R p => rootsOf R p) fun {X Y} φ p => by
      change (p.map φ.iso.hom.hom.hom).roots = p.roots.map φ.iso.hom.hom.hom
      set e := ringEquiv (domainToCommRing.mapIso φ.iso)
      change (p.map e.toRingHom).roots = p.roots.map e.toRingHom
      apply le_antisymm
      · have h := map_roots_le_of_injective (f := e.symm.toRingHom) (p.map e.toRingHom)
          e.symm.injective
        rw [map_symm_map e p] at h
        have h' := Multiset.map_le_map (f := e.toRingHom) h
        rwa [Multiset.map_map, show (e.toRingHom : _ → _) ∘ e.symm.toRingHom = id from
          funext e.apply_symm_apply, Multiset.map_id] at h'
      · exact map_roots_le_of_injective p e.injective

end Poly

end

end LeanCategories.Algebra
