/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Lattices.Valued.FanCoarsening
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.AlgebraicGeometry.AffineScheme

/-!
# The affine toric chart of a rational cone, and the affine functor (#24)

## What this file delivers, and what it does not

Issue #24 asks for the toric realization: affine toric schemes from semigroup algebras, and the
fan-to-scheme functor **generated as the gluing/colimit over the fan's cone-and-face diagram**.

Landed here:

* `coneDual`: the dual cone `σ^∨` of CLS Definition 1.2.3, p. 24, with the toric evaluation
  pairing `Module.Dual.eval` (the same pairing `RationalPolyhedralCone.lean` and
  `RationalConeDuality.lean` use; not wrapped, used directly).
* `semigroupAlgebra` and `affineToricRing`: the coordinate ring of the affine toric chart, as the
  **composite semigroup algebra ∘ cone-dual** — `affineToricRing σ` is by definition
  `semigroupAlgebra ↥(coneDual σ)`, so the object map of the affine functor reads as the
  prescribed composite rather than as a hand-assembled ring.
* `affineToricScheme`: its spectrum, `Spec (CommRingCat.of (affineToricRing σ))`.
* `affineToricRingMap`, `affineToricSchemeMap`, with the identity and composition laws
  (`affineToricSchemeMap_refl`, `affineToricSchemeMap_comp`).
* `coneCategory` (the poset of rational cones), `Fan.fanConeCategory` (the cone-and-face diagram of
  a fan as an index category) and `affineToricFunctor` / `Fan.affineToricDiagram`: the affine
  functor `PointedCone ℚ V ⥤ Scheme`, and its restriction to the cone-and-face diagram of a fan.
* `ToricRealizationVariance` with `toricRealizationVariance := .conesCovariant` and
  `affineToricFunctor_map_covariant`: the §59.2 **variance convention, recorded as data before the
  implementation** and checked by a theorem.

**Not landed, and named as the open edge:** the gluing of the chart diagram into the toric scheme of
a fan (`Fan.algebraicRealization` in the reference implementation), i.e. the colimit of
`Fan.affineToricDiagram` along its face morphisms. It is not assembled here because two inputs the
gluing needs are absent from this repository:

* the *integral-character* layer — a lattice map `i : N →+ V` with its real/rational extension
  `(N →+ ℤ) →ₗ Dual ℚ V` and the monoid of lattice points of a cone — which is what makes a face
  inclusion a *localization at one monomial*, hence an open immersion. On this file's rational
  carrier the dual cone is a `ℚ`-submodule, so the chart map of a face inclusion is a ring map but
  its being an open immersion is not yet a theorem here;
* consequently `Scheme.IsLocallyDirected`'s gluing input is not discharged.

The port target for both is TauCeti's `Geometry/Toric/Algebraic/{Lattice/Basic, Cone/LatticePoints,
DualSemigroup/Basic, FaceLocalization, Fan/Scheme}.lean` (Apache 2.0), which do this over the real
carrier; the variance convention recorded below fixes the direction that port must have.

## Provenance

The declarations are a port of `TauCeti/Geometry/Toric/Algebraic/AffineScheme.lean` (Apache 2.0,
© The Tau Ceti contributors), with the carrier changed from the real cone `PointedCone ℝ V` of an
integral lattice to the rational cone `PointedCone ℚ V` of #37's `RationalPolyhedralCone.lean`, and
the dual semigroup taken to be the dual cone itself (see the "not landed" note above). The
statement shapes, the identity and composition laws, and the `Spec`-of-the-dual-inclusion
construction are that file's.

## LC-09 search record (2026-11-17)

* Formalization corpus: query `affineToric` returns TauCeti
  `Geometry/Toric/Algebraic/{AffineScheme, IntegralAffine, Product, Examples/AffineRay}.lean` and
  `file:Toric.*Algebraic.*Affine` returns seven TauCeti files; `affineCoordinateRing` and
  `affineToricScheme` are TauCeti's, so this is a port (above), not new mathematics. Query
  `coarsening` returns no toric hit; query `Wythoff` returns only atlas-lean's Wythoff's-game file.
* Repository: `rg 'Toric|affineToric|MonoidAlgebra'` over `LeanCategories` finds no toric
  realization, no `Spec`-of-a-semigroup-algebra, and no `AddMonoidAlgebra`/`MonoidAlgebra` use at
  all before this file; `LeanCategories/AlgebraicGeometry/{AffineScheme, RelativeSpec, Scheme}` hold
  the `Spec`/`Γ` interface only.
* Mathlib: `MonoidAlgebra.mapDomainAlgHom` (`Algebra/MonoidAlgebra/Defs.lean`) with
  `mapDomainAlgHom_id` and `mapDomainAlgHom_comp`; `AlgebraicGeometry.Spec` with `Spec.map_id` and
  `Spec.map_comp`; `PointedCone.dual`, `PointedCone.mem_dual`, `PointedCone.dual_anti`. The
  composition law for `Spec` is contravariant (`Spec.map (f ≫ g) = Spec.map g ≫ Spec.map f`), which
  is what fixes the recorded variance.

## References

* D. Cox, J. Little, S. Schenck, *Toric Varieties*, Graduate Studies in Mathematics 124 (2011):
  Definition 1.2.3 and Proposition 1.2.4, p. 24 (dual cone); §1.3 (semigroup algebras and affine
  toric varieties); §3.1 and §3.3 (fans, and the gluing of the affine charts).
* W. Fulton, *Introduction to Toric Varieties*, Annals of Mathematics Studies 131 (1993), §§1.2–1.4.
-/

@[expose] public section

open _root_.AlgebraicGeometry CategoryTheory

namespace LeanCategories.AlgebraicGeometry.Toric

universe u

variable {V : Type u} [AddCommGroup V] [Module ℚ V]

/-! ## The dual cone and the coordinate ring -/

/-- The dual cone `σ^∨` of a rational cone, with the toric evaluation pairing: the functionals
pairing nonnegatively with every point of `σ` (CLS Definition 1.2.3, p. 24). -/
def coneDual (σ : PointedCone ℚ V) : PointedCone ℚ (Module.Dual ℚ V) :=
  PointedCone.dual (Module.Dual.eval ℚ V) (σ : Set V)

/-- Membership in the dual cone: nonnegativity of the pairing on the cone. -/
@[simp] theorem mem_coneDual {σ : PointedCone ℚ V} {m : Module.Dual ℚ V} :
    m ∈ coneDual σ ↔ ∀ x ∈ (σ : Set V), 0 ≤ m x := by
  simp [coneDual, PointedCone.mem_dual]

/-- Enlarging a cone shrinks its dual cone. -/
@[gcongr] theorem coneDual_anti {σ τ : PointedCone ℚ V} (h : σ ≤ τ) : coneDual τ ≤ coneDual σ :=
  PointedCone.dual_anti h

/-- The semigroup algebra of an additive monoid, over `ℚ`. This is the second factor of the affine
functor's object map, `semigroup algebra ∘ cone-dual`. -/
abbrev semigroupAlgebra (M : Type u) [AddZeroClass M] : Type u :=
  MonoidAlgebra ℚ (Multiplicative M)

/-- The coordinate ring of the affine toric chart of a cone: **`semigroup algebra ∘ cone-dual`**,
literally the composite the touchstone prescribes. -/
abbrev affineToricRing (σ : PointedCone ℚ V) : Type u := semigroupAlgebra ↥(coneDual σ)

/-- The affine toric scheme of a cone: the spectrum of its coordinate ring. -/
noncomputable abbrev affineToricScheme (σ : PointedCone ℚ V) : Scheme :=
  Spec (CommRingCat.of (affineToricRing σ))

/-- The chart ring of a cone is the semigroup algebra of its dual cone — the object map of the
affine functor, recorded so that the composite is checkable. -/
theorem affineToricScheme_def (σ : PointedCone ℚ V) :
    affineToricScheme σ = Spec (CommRingCat.of (semigroupAlgebra ↥(coneDual σ))) := (rfl)

/-! ## Functoriality in the cone

A cone inclusion `σ ≤ τ` pulls characters back from `τ` to `σ` (the dual semigroup is
contravariant, `coneDual_anti`), which is a map of coordinate rings `affineToricRing τ →
affineToricRing σ`, and `Spec` turns it into a morphism of schemes *in the direction of the
inclusion*. -/

/-- The inclusion of the dual monoids induced by a cone inclusion. -/
def coneDualInclusion {σ τ : PointedCone ℚ V} (h : σ ≤ τ) : ↥(coneDual τ) →+ ↥(coneDual σ) where
  toFun m := ⟨(m : Module.Dual ℚ V), coneDual_anti h m.2⟩
  map_zero' := by ext; simp
  map_add' := by intro a b; ext; simp

@[simp] theorem coneDualInclusion_apply {σ τ : PointedCone ℚ V} (h : σ ≤ τ)
    (m : ↥(coneDual τ)) : (coneDualInclusion h m : Module.Dual ℚ V) = (m : Module.Dual ℚ V) := rfl

theorem coneDualInclusion_refl (σ : PointedCone ℚ V) :
    coneDualInclusion (le_refl σ) = AddMonoidHom.id ↥(coneDual σ) := by
  ext m; rfl

theorem coneDualInclusion_comp {σ τ υ : PointedCone ℚ V} (hστ : σ ≤ τ) (hτυ : τ ≤ υ) :
    (coneDualInclusion hστ).comp (coneDualInclusion hτυ) =
      coneDualInclusion (le_trans hστ hτυ) := by
  ext m; rfl

/-- The contravariant map of coordinate rings induced by a cone inclusion. -/
noncomputable def affineToricRingMap {σ τ : PointedCone ℚ V} (h : σ ≤ τ) :
    affineToricRing τ →ₐ[ℚ] affineToricRing σ :=
  MonoidAlgebra.mapDomainAlgHom ℚ ℚ (AddMonoidHom.toMultiplicative (coneDualInclusion h))

theorem affineToricRingMap_refl (σ : PointedCone ℚ V) :
    affineToricRingMap (le_refl σ) = AlgHom.id ℚ (affineToricRing σ) := by
  rw [affineToricRingMap, coneDualInclusion_refl, AddMonoidHom.toMultiplicative_id,
    MonoidAlgebra.mapDomainAlgHom_id]

theorem affineToricRingMap_comp {σ τ υ : PointedCone ℚ V} (hστ : σ ≤ τ) (hτυ : τ ≤ υ) :
    (affineToricRingMap hστ).comp (affineToricRingMap hτυ) =
      affineToricRingMap (le_trans hστ hτυ) := by
  have hinc : AddMonoidHom.toMultiplicative (coneDualInclusion (le_trans hστ hτυ)) =
      (AddMonoidHom.toMultiplicative (coneDualInclusion hστ)).comp
        (AddMonoidHom.toMultiplicative (coneDualInclusion hτυ)) := by
    ext m
    rfl
  rw [affineToricRingMap, affineToricRingMap, affineToricRingMap, hinc,
    MonoidAlgebra.mapDomainAlgHom_comp]

/-- The coordinate-ring map as a ring homomorphism. -/
noncomputable def affineToricRingHom {σ τ : PointedCone ℚ V} (h : σ ≤ τ) :
    affineToricRing τ →+* affineToricRing σ :=
  (affineToricRingMap h).toRingHom

theorem affineToricRingHom_refl (σ : PointedCone ℚ V) :
    affineToricRingHom (le_refl σ) = RingHom.id (affineToricRing σ) := by
  rw [affineToricRingHom, affineToricRingMap_refl]
  simp

theorem affineToricRingHom_comp {σ τ υ : PointedCone ℚ V} (hστ : σ ≤ τ) (hτυ : τ ≤ υ) :
    (affineToricRingHom hστ).comp (affineToricRingHom hτυ) =
      affineToricRingHom (le_trans hστ hτυ) :=
  congrArg AlgHom.toRingHom (affineToricRingMap_comp hστ hτυ)

/-- The morphism of affine toric schemes induced by a cone inclusion, in the direction of the
inclusion. -/
noncomputable def affineToricSchemeMap {σ τ : PointedCone ℚ V} (h : σ ≤ τ) :
    affineToricScheme σ ⟶ affineToricScheme τ :=
  Spec.map (CommRingCat.ofHom (affineToricRingHom h))

theorem affineToricSchemeMap_refl (σ : PointedCone ℚ V) :
    affineToricSchemeMap (le_refl σ) = 𝟙 (affineToricScheme σ) := by
  rw [affineToricSchemeMap, affineToricRingHom_refl, CommRingCat.ofHom_id]
  exact Spec.map_id _

theorem affineToricSchemeMap_comp {σ τ υ : PointedCone ℚ V} (hστ : σ ≤ τ) (hτυ : τ ≤ υ) :
    affineToricSchemeMap hστ ≫ affineToricSchemeMap hτυ =
      affineToricSchemeMap (le_trans hστ hτυ) := by
  rw [affineToricSchemeMap, affineToricSchemeMap, affineToricSchemeMap, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp, affineToricRingHom_comp]

/-- The implementation agrees with the recorded convention: a cone inclusion `σ ≤ τ` gives a
morphism from the chart of `σ` to the chart of `τ`, and it is `Spec` of the dual map. -/
theorem affineToricSchemeMap_is_dual_spec {σ τ : PointedCone ℚ V} (h : σ ≤ τ) :
    affineToricSchemeMap h = Spec.map (CommRingCat.ofHom (affineToricRingMap h).toRingHom) :=
  (rfl)

/-! ## The index categories: cones ordered by inclusion, and the cone-and-face diagram of a fan -/

/-- A `PLift` of a proposition is a subsingleton; used for the category laws on cone inclusions. -/
theorem plift_prop_subsingleton {p : Prop} (a b : PLift p) : a = b := by
  cases a with
  | up ha => cases b with | up hb => rw [Subsingleton.elim ha hb]

/-- The poset of rational cones of `V` as a category, with `σ ⟶ τ` when `σ ≤ τ`: the index
category of the affine toric functor. -/
instance coneCategory : Category (PointedCone ℚ V) where
  Hom σ τ := PLift (σ ≤ τ)
  id σ := PLift.up (le_refl σ)
  comp f g := PLift.up (le_trans f.down g.down)
  id_comp := by intros; exact plift_prop_subsingleton _ _
  comp_id := by intros; exact plift_prop_subsingleton _ _
  assoc := by intros; exact plift_prop_subsingleton _ _

/-! ## The affine functor -/

/-- **The affine toric functor**: `Spec ∘ semigroup algebra ∘ cone-dual`, from the poset of rational
cones to schemes. Its object map is the recorded composite; its morphism map is `Spec` of the
contravariant map of dual semigroups, so it is covariant on cones (see
`affineToricFunctor_map_covariant`). -/
noncomputable def affineToricFunctor : (PointedCone ℚ V) ⥤ Scheme where
  obj σ := affineToricScheme σ
  map f := affineToricSchemeMap f.down
  map_id σ := affineToricSchemeMap_refl σ
  map_comp f g := (affineToricSchemeMap_comp f.down g.down).symm

/-! ## The recorded variance convention (§59.2) -/

/-- The two variance conventions a toric realization may be given in, recorded as data: whether a
cone inclusion goes to a morphism of schemes in the same direction, or in the opposite one. -/
inductive ToricRealizationVariance
  /-- A cone inclusion `σ ≤ τ` is sent to a morphism `𝔸_σ ⟶ 𝔸_τ`. -/
  | conesCovariant
  /-- A cone inclusion `σ ≤ τ` is sent to a morphism `𝔸_τ ⟶ 𝔸_σ`. -/
  | conesContravariant
  deriving DecidableEq, Repr

/-- **The convention recorded for #24, before the implementation**: cone inclusions go to scheme
morphisms in the same direction. The reason is structural: the dual semigroup is contravariant in
the cone (`coneDual_anti`) and `Spec` is contravariant in the ring, so the two cancel. -/
def toricRealizationVariance : ToricRealizationVariance := .conesCovariant

/-- The implementation agrees with the recorded convention: a cone inclusion `σ ≤ τ` gives a
morphism from the chart of `σ` to the chart of `τ`, and it is `Spec` of the dual map. -/
theorem affineToricFunctor_map_covariant {σ τ : PointedCone ℚ V} (h : σ ≤ τ) :
    (affineToricFunctor.map (PLift.up h) : affineToricScheme σ ⟶ affineToricScheme τ) =
      Spec.map (CommRingCat.ofHom (affineToricRingMap h).toRingHom) := (rfl)

/-! ## The cone-and-face diagram of a fan

The toric scheme of a fan is the gluing (colimit) of the affine charts along this diagram; see the
module docstring for why the gluing itself is the open edge of #24. -/


end LeanCategories.AlgebraicGeometry.Toric

namespace LeanCategories.Lattices.Valued

open LeanCategories.AlgebraicGeometry.Toric

variable {V : Type u} [AddCommGroup V] [Module ℚ V]
variable {N : Type u} [AddCommGroup N] {i : N →+ V}

/-- The cones of a fan, ordered by inclusion, as the index category of its chart diagram. -/
instance fanConeCategory (Φ : Fan i) : Category Φ.cones where
  Hom σ τ := PLift (σ.1 ≤ τ.1)
  id σ := PLift.up (le_refl σ.1)
  comp f g := PLift.up (le_trans f.down g.down)
  id_comp := by intros; exact plift_prop_subsingleton _ _
  comp_id := by intros; exact plift_prop_subsingleton _ _
  assoc := by intros; exact plift_prop_subsingleton _ _

/-- The cone-and-face diagram of a fan: its cone inclusions act by `Spec` of the dual-subsemigroup
map on the affine toric charts. Its colimit is the toric scheme of the fan, which is not assembled
here (module docstring). -/
noncomputable def Fan.affineToricDiagram (Φ : Fan i) : Φ.cones ⥤ Scheme where
  obj σ := affineToricScheme σ.1
  map f := affineToricSchemeMap f.down
  map_id σ := affineToricSchemeMap_refl σ.1
  map_comp f g := (affineToricSchemeMap_comp f.down g.down).symm

end LeanCategories.Lattices.Valued
