/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Algebra.Concrete.Rings
public import LeanCategories.Foundation.IsoElements
public import Mathlib.RingTheory.PrincipalIdealDomain
public import Mathlib.RingTheory.UniqueFactorizationDomain.Basic
public import Mathlib.Algebra.EuclideanDomain.Field

@[expose] public section

/-!
# Elements of factorial rings and their divisibility operations

The chain of classes of commutative rings

  `EuclideanDomainCat ⊆ PrincipalIdealDomainCat ⊆ UniqueFactorizationDomainCat ⊆ CommRingCat`

(full subcategories; every euclidean domain is a PID, every PID a UFD), and the points of each
class up to isomorphism, `IsoElements` of its underlying-set functor. A point of a smaller class is
a point of the larger one (`IsoElements.restrict` along the inclusion).

Operations on elements of a UFD `R`, each iso-natural (`IsoElements.isoInvariant` /
`IsoElements.isoNatural`):

* `isPrime x`: `Prime x`;
* `factorizations x`: the set of factorizations `x = u · p₁ ⋯ pₖ` with `u` a unit and each `pᵢ`
  irreducible — a factorization is determined only up to units and order, so the operation's
  value is the set of them and a computation returns one member;
* `gcds x`: `y ↦` the set of greatest common divisors of `x` and `y` (all associated).
-/

open CategoryTheory LeanCategories.Foundation

namespace LeanCategories.Algebra

universe u

/-! ### The classes and their inclusions -/

/-- Commutative rings whose own ring structure extends to a euclidean domain. -/
def IsEuclideanRing : ObjectProperty CommRingCat.{u} := fun R =>
  ∃ E : EuclideanDomain R, E.toCommRing = inferInstanceAs (CommRing R)

/-- Principal ideal domains. -/
def IsPrincipalIdealDomain : ObjectProperty CommRingCat.{u} := fun R =>
  IsDomain R ∧ IsPrincipalIdealRing R

/-- Unique factorization domains. -/
def IsUniqueFactorizationDomain : ObjectProperty CommRingCat.{u} := fun R =>
  IsDomain R ∧ UniqueFactorizationMonoid R

theorem isPrincipalIdealDomain_of_euclidean {R : CommRingCat.{u}} (h : IsEuclideanRing R) :
    IsPrincipalIdealDomain R := by
  obtain ⟨E, hE⟩ := h
  have hDomain : @IsDomain R (@CommRing.toRing R E.toCommRing).toSemiring := inferInstance
  have hPID := @EuclideanDomain.to_principal_ideal_domain R E
  rw [hE] at hDomain hPID
  exact ⟨hDomain, hPID⟩

theorem isUniqueFactorizationDomain_of_pid {R : CommRingCat.{u}}
    (h : IsPrincipalIdealDomain R) : IsUniqueFactorizationDomain R := by
  obtain ⟨_, _⟩ := h
  exact ⟨inferInstance, inferInstance⟩

/-- Euclidean domains, as a full subcategory. -/
abbrev EuclideanRings : Type (u + 1) := IsEuclideanRing.{u}.FullSubcategory
/-- Principal ideal domains, as a full subcategory. -/
abbrev PrincipalIdealDomains : Type (u + 1) := IsPrincipalIdealDomain.{u}.FullSubcategory
/-- Unique factorization domains, as a full subcategory. -/
abbrev UniqueFactorizationDomains : Type (u + 1) :=
  IsUniqueFactorizationDomain.{u}.FullSubcategory

/-- Every euclidean domain is a principal ideal domain. -/
def euclideanToPID : EuclideanRings.{u} ⥤ PrincipalIdealDomains.{u} :=
  ObjectProperty.ιOfLE fun _ h => isPrincipalIdealDomain_of_euclidean h

/-- Every principal ideal domain is a unique factorization domain. -/
def pidToUFD : PrincipalIdealDomains.{u} ⥤ UniqueFactorizationDomains.{u} :=
  ObjectProperty.ιOfLE fun _ h => isUniqueFactorizationDomain_of_pid h

/-- A unique factorization domain is a commutative ring. -/
def ufdToCommRing : UniqueFactorizationDomains.{u} ⥤ CommRingCat.{u} :=
  ObjectProperty.ι _

/-! ### Underlying sets and points -/

/-- The underlying set of a commutative ring. -/
abbrev ringCarrier : CommRingCat.{u} ⥤ Type u := forget CommRingCat
/-- The underlying set of a unique factorization domain. -/
abbrev ufdCarrier : UniqueFactorizationDomains.{u} ⥤ Type u := ufdToCommRing ⋙ ringCarrier
/-- The underlying set of a principal ideal domain. -/
abbrev pidCarrier : PrincipalIdealDomains.{u} ⥤ Type u := pidToUFD ⋙ ufdCarrier
/-- The underlying set of a euclidean domain. -/
abbrev euclideanCarrier : EuclideanRings.{u} ⥤ Type u := euclideanToPID ⋙ pidCarrier

/-- Elements of commutative rings, up to isomorphism. -/
abbrev RingPoints := IsoElements ringCarrier.{u}
/-- Elements of unique factorization domains, up to isomorphism. -/
abbrev UFDPoints := IsoElements ufdCarrier.{u}
/-- Elements of principal ideal domains, up to isomorphism. -/
abbrev PIDPoints := IsoElements pidCarrier.{u}
/-- Elements of euclidean domains, up to isomorphism. -/
abbrev EuclideanPoints := IsoElements euclideanCarrier.{u}

/-- An element of a euclidean domain is an element of a principal ideal domain. -/
def euclideanPointsToPID : EuclideanPoints.{u} ⥤ PIDPoints.{u} :=
  IsoElements.restrict euclideanToPID pidCarrier
/-- An element of a principal ideal domain is an element of a unique factorization domain. -/
def pidPointsToUFD : PIDPoints.{u} ⥤ UFDPoints.{u} :=
  IsoElements.restrict pidToUFD ufdCarrier
/-- An element of a unique factorization domain is an element of a commutative ring. -/
def ufdPointsToRing : UFDPoints.{u} ⥤ RingPoints.{u} :=
  IsoElements.restrict ufdToCommRing ringCarrier

/-! ### Operations on elements of a UFD -/

namespace UFD

variable {R S : UniqueFactorizationDomains.{u}}

instance (R : UniqueFactorizationDomains.{u}) : IsDomain R.obj := R.property.1
instance (R : UniqueFactorizationDomains.{u}) : UniqueFactorizationMonoid R.obj := R.property.2

/-- The ring isomorphism underlying an isomorphism of UFDs. -/
def ringEquiv (φ : R ≅ S) : R.obj ≃+* S.obj := (ufdToCommRing.mapIso φ).commRingCatIsoToRingEquiv

theorem ringEquiv_apply (φ : R ≅ S) (x : R.obj) : ringEquiv φ x = ufdCarrier.map φ.hom x := rfl

/-- The factorizations of `x`: a unit and a multiset of irreducibles with product `x`. -/
def factorizationSet (R : UniqueFactorizationDomains.{u}) (x : R.obj) :
    Set (R.objˣ × Multiset R.obj) :=
  {f | (∀ p ∈ f.2, Irreducible p) ∧ (f.1 : R.obj) * f.2.prod = x}

/-- Sets of factorizations, transported along ring isomorphisms. -/
def factorizationSets : Core UniqueFactorizationDomains.{u} ⥤ Type u :=
  typeFunctor (fun R => Set (R.of.objˣ × Multiset R.of.obj))
    (fun φ F => (fun f => (Units.map (ringEquiv φ.iso).toMonoidHom f.1,
      f.2.map (ringEquiv φ.iso))) '' F)
    (fun R F => by
      have h : ∀ f : R.of.objˣ × Multiset R.of.obj,
          (Units.map (ringEquiv (𝟙 R : R ⟶ R).iso).toMonoidHom f.1,
            f.2.map (ringEquiv (𝟙 R : R ⟶ R).iso)) = f :=
        fun f => Prod.ext (Units.ext rfl) (Multiset.map_id' f.2)
      simp only [h, Set.image_id'])
    (fun φ ψ F => by
      rw [Set.image_image]
      congr 1
      funext f
      exact Prod.ext (Units.ext rfl) (by rw [Multiset.map_map]; rfl))

theorem factorizationSet_map (φ : R ≅ S) (x : R.obj) :
    factorizationSet S (ringEquiv φ x) =
      (fun f => (Units.map (ringEquiv φ).toMonoidHom f.1, f.2.map (ringEquiv φ))) ''
        factorizationSet R x := by
  set e := ringEquiv φ
  ext ⟨v, m⟩
  constructor
  · rintro ⟨hirr, hprod⟩
    refine ⟨(Units.map e.symm.toMonoidHom v, m.map e.symm), ⟨?_, ?_⟩, ?_⟩
    · intro p hp
      obtain ⟨q, hq, rfl⟩ := Multiset.mem_map.1 hp
      exact (MulEquiv.irreducible_iff e.symm.toMulEquiv).2 (hirr q hq)
    · apply e.injective
      rw [map_mul, map_multiset_prod, Multiset.map_map]
      simpa using hprod
    · ext <;> simp [Multiset.map_map]
  · rintro ⟨⟨u, l⟩, ⟨hirr, hprod⟩, h⟩
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨?_, ?_⟩
    · intro p hp
      obtain ⟨q, hq, rfl⟩ := Multiset.mem_map.1 hp
      exact (MulEquiv.irreducible_iff e.toMulEquiv).2 (hirr q hq)
    · simp only [Units.coe_map]
      rw [← hprod, map_mul, map_multiset_prod]
      rfl

/-- `factor`: the factorizations of an element of a UFD, iso-naturally. -/
def factor : UFDPoints.{u} ⥤ factorizationSets.{u}.Elements :=
  IsoElements.isoNatural ufdCarrier factorizationSets (fun R x => factorizationSet R x)
    fun φ x => factorizationSet_map φ.iso x

/-- The greatest common divisors of `x` and `y`. -/
def gcdSet (R : UniqueFactorizationDomains.{u}) (x y : R.obj) : Set R.obj :=
  {d | d ∣ x ∧ d ∣ y ∧ ∀ e, e ∣ x → e ∣ y → e ∣ d}

/-- Families of subsets indexed by the ring, transported along ring isomorphisms. -/
def gcdSets : Core UniqueFactorizationDomains.{u} ⥤ Type u :=
  typeFunctor (fun R => R.of.obj → Set R.of.obj)
    (fun φ g y => ringEquiv φ.iso '' g ((ringEquiv φ.iso).symm y))
    (fun R g => funext fun y => Set.image_id _)
    (fun φ ψ g => funext fun y => by rw [Set.image_image]; rfl)

theorem gcdSet_map (φ : R ≅ S) (x : R.obj) (y : S.obj) :
    gcdSet S (ringEquiv φ x) y = ringEquiv φ '' gcdSet R x ((ringEquiv φ).symm y) := by
  set e := ringEquiv φ
  have hd : ∀ a b : R.obj, e a ∣ e b ↔ a ∣ b := fun a b => map_dvd_iff e
  ext d
  constructor
  · rintro ⟨hx, hy, hmax⟩
    refine ⟨e.symm d, ⟨?_, ?_, ?_⟩, by simp⟩
    · rw [← hd]; simpa using hx
    · rw [← hd]; simpa using hy
    · intro c hcx hcy
      rw [← hd]
      simpa using hmax (e c) ((hd c x).2 hcx) (by simpa using (hd c _).2 hcy)
  · rintro ⟨d, ⟨hx, hy, hmax⟩, rfl⟩
    refine ⟨(hd _ _).2 hx, by simpa using (hd _ _).2 hy, ?_⟩
    intro c hcx hcy
    have := hmax (e.symm c) (by rw [← hd]; simpa using hcx) (by rw [← hd]; simpa using hcy)
    simpa using (hd _ _).2 this

/-- `gcd`: for an element `x` of a UFD, `y ↦` the greatest common divisors of `x` and `y`. -/
def gcd : UFDPoints.{u} ⥤ gcdSets.{u}.Elements :=
  IsoElements.isoNatural ufdCarrier gcdSets (fun R x y => gcdSet R x y) fun φ x => by
    funext y
    change gcdSet _ (ringEquiv φ.iso x) y =
      ringEquiv φ.iso '' gcdSet _ x ((ringEquiv φ.iso).symm y)
    exact gcdSet_map φ.iso x y

/-- `is_prime`: primality of an element of a UFD, an isomorphism invariant. -/
def isPrime : UFDPoints.{u} ⥤ Discrete Prop :=
  IsoElements.isoInvariant ufdCarrier (fun (R : UniqueFactorizationDomains) (x : R.obj) =>
    Prime x) fun φ _ => propext (MulEquiv.prime_iff (ringEquiv φ).toMulEquiv)

end UFD

end LeanCategories.Algebra
