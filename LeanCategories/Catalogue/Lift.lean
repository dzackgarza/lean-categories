/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.CategoryTheory.Iso

@[expose] public section

/-!
# Lifts of subobjects along a functor (CC-LIFT)

An operation computed on `U(x)` that must return to the source side — a subobject of the
*original* structured object — needs `U` to lift subobjects: for every monomorphism
`i : K ↪ U(X)` an object `X'` over `K` and a map `X' → X` over `i`, with the full
cartesian universal property of FOUNDATIONS Definition 31.1. These are the cartesian lifts
of monomorphisms (for the forgetful functor of formed modules, restriction of the form). A
`MonoLift U` is that data; a registered `.lift` row supplies it for one route step, and without
one the operation reports the missing lift instead of returning the bare `U`-side result.
-/

open CategoryTheory

namespace CasCatalogue

universe v₁ v₂ v₃ u₁ u₂ u₃

/-- Required callable data for lifting a selected monomorphism. The input's monicity
is a formal domain condition; implementations compute the object, defining map and
both comparison maps. They do not supply factorization, inverse or universal proofs.
These functions may have infinite domains and are called at inputs, never enumerated. -/
structure MonoLiftComputation {C : Type u₁} [Category.{v₁} C]
    {D : Type u₂} [Category.{v₂} D] (U : C ⥤ D) where
  obj : (X : C) → {K : D} → (i : K ⟶ U.obj X) → [Mono i] → C
  hom : (X : C) → {K : D} → (i : K ⟶ U.obj X) → [Mono i] → obj X i ⟶ X
  forward : (X : C) → {K : D} → (i : K ⟶ U.obj X) → [Mono i] → U.obj (obj X i) ⟶ K
  backward : (X : C) → {K : D} → (i : K ⟶ U.obj X) → [Mono i] → K ⟶ U.obj (obj X i)

/-- Cartesian lifts of monomorphisms along `U`, with a specified isomorphism over the base.
Merely lying over a monomorphism does not make a map a subobject or a cartesian lift. -/
structure MonoLift {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    (U : C ⥤ D) where
  /-- The lifted object over `K`. -/
  obj : (X : C) → {K : D} → (i : K ⟶ U.obj X) → [Mono i] → C
  /-- Its map to `X`. -/
  hom : (X : C) → {K : D} → (i : K ⟶ U.obj X) → [Mono i] → obj X i ⟶ X
  /-- It lies over `K`. -/
  iso : (X : C) → {K : D} → (i : K ⟶ U.obj X) → [Mono i] → U.obj (obj X i) ≅ K
  /-- Its map lies over `i`. -/
  fac : ∀ (X : C) {K : D} (i : K ⟶ U.obj X) [Mono i], U.map (hom X i) = (iso X i).hom ≫ i
  /-- The pullback universal bijection of FOUNDATIONS Definition 31.1, retaining
  the specified identification of the lifted base with `K`. This is the arbitrary-base-arrow
  convention called `IsStronglyCartesian` in Mathlib's `FiberedCategory/Cartesian.lean`. -/
  universal : ∀ (X : C) {K : D} (i : K ⟶ U.obj X) [Mono i]
    {Y : C} (g : U.obj Y ⟶ K) (f : Y ⟶ X), U.map f = g ≫ i →
    ∃! h : Y ⟶ obj X i, U.map h ≫ (iso X i).hom = g ∧ h ≫ hom X i = f

namespace MonoLift

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {U : C ⥤ D} (L : MonoLift U)

/-- Public computation signature obtained from the specified mathematical lift.
Only callable data crosses this interface; `fac` and `universal` remain formal laws. -/
def computation : MonoLiftComputation U where
  obj X _ i _ := L.obj X i
  hom X _ i _ := L.hom X i
  forward X _ i _ := (L.iso X i).hom
  backward X _ i _ := (L.iso X i).inv

/-- Compatibility of the callable defining map with its retained base comparison. -/
theorem computation_fac (X : C) {K : D} (i : K ⟶ U.obj X) [Mono i] :
    U.map (L.computation.hom X i) = L.computation.forward X i ≫ i := L.fac X i

/-- The callable comparison directions are inverse: this is a formal law, not a
proof-producing computational component. -/
theorem computation_forward_backward (X : C) {K : D} (i : K ⟶ U.obj X) [Mono i] :
    L.computation.forward X i ≫ L.computation.backward X i = 𝟙 _ :=
  (L.iso X i).hom_inv_id

/-- The reverse inverse law at the actual selected base object. -/
theorem computation_backward_forward (X : C) {K : D} (i : K ⟶ U.obj X) [Mono i] :
    L.computation.backward X i ≫ L.computation.forward X i = 𝟙 K :=
  (L.iso X i).inv_hom_id

/-- A cartesian lift of a monomorphism is itself a defining subobject map.
No faithfulness assumption on the functor is needed. -/
instance hom_mono (X : C) {K : D} (i : K ⟶ U.obj X) [Mono i] : Mono (L.hom X i) where
  right_cancellation {Y} a b eq := by
    have base : U.map a ≫ (L.iso X i).hom = U.map b ≫ (L.iso X i).hom := by
      apply (cancel_mono i).mp
      simpa only [Category.assoc, ← L.fac, ← U.map_comp] using congrArg U.map eq
    obtain ⟨h, _, unique⟩ := L.universal X i
      (U.map a ≫ (L.iso X i).hom) (a ≫ L.hom X i) (by
        rw [U.map_comp, L.fac, Category.assoc])
    exact (unique a ⟨rfl, rfl⟩).trans (unique b ⟨base.symm, eq.symm⟩).symm

/-- Monicity of the extracted defining map is a formal law, rather than a result field. -/
instance computation_hom_mono (X : C) {K : D} (i : K ⟶ U.obj X) [Mono i] :
    Mono (L.computation.hom X i) :=
  inferInstanceAs (Mono (L.hom X i))

end MonoLift

namespace MonoLift

/-- The identity route lifts a subobject to its original defining map. -/
def id (C : Type u₁) [Category.{v₁} C] : MonoLift (𝟭 C) where
  obj _ K _ _ := K
  hom _ _ i _ := i
  iso _ K _ _ := Iso.refl K
  fac _ _ _ _ := (Category.id_comp _).symm
  universal X K i hi Y g f hf := by
    refine ⟨g, ⟨Category.comp_id _, hf.symm⟩, ?_⟩
    intro h hh
    have eq : h ≫ 𝟙 K = g := hh.1
    exact (Category.comp_id h).symm.trans eq

/-- Prescribed subobject lifts compose along a route. The defining map is the second
lift's actual map, and its base identification is the composite of the two specified
identifications. Cartesian universality is obtained by factoring first through `V` and
then through `U` (FOUNDATIONS Definition 31.1). -/
def comp {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    {E : Type u₃} [Category.{v₃} E] {U : C ⥤ D} {V : D ⥤ E}
    (L : MonoLift U) (M : MonoLift V) : MonoLift (U ⋙ V) where
  obj X _ i _ := L.obj X (M.hom (U.obj X) i)
  hom X _ i _ := L.hom X (M.hom (U.obj X) i)
  iso X _ i _ := V.mapIso (L.iso X (M.hom (U.obj X) i)) ≪≫ M.iso (U.obj X) i
  fac X _ i _ := by
    dsimp
    rw [L.fac, V.map_comp, M.fac, Category.assoc]
  universal X K i hi Y g f hf := by
    obtain ⟨d, hd, _⟩ := M.universal (U.obj X) i g (U.map f) hf
    obtain ⟨h, hh, _⟩ := L.universal X (M.hom (U.obj X) i) d f hd.2.symm
    refine ⟨h, ⟨?_, hh.2⟩, ?_⟩
    · dsimp
      rw [← Category.assoc, ← V.map_comp, hh.1, hd.1]
    · intro k hk
      exact (cancel_mono (L.hom X (M.hom (U.obj X) i))).mp (hk.2.trans hh.2.symm)

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {E : Type u₃} [Category.{v₃} E] {U : C ⥤ D} {V : D ⥤ E}
  (L : MonoLift U) (M : MonoLift V) (X : C) {K : E} (i : K ⟶ V.obj (U.obj X)) [Mono i]

/-- Public object-action equation for composed callable lift signatures. -/
theorem computation_comp_obj :
    (L.comp M).computation.obj X i =
      L.computation.obj X (M.computation.hom (U.obj X) i) := rfl

/-- Public defining-map equation for composed callable lift signatures. -/
theorem computation_comp_hom :
    (L.comp M).computation.hom X i =
      L.computation.hom X (M.computation.hom (U.obj X) i) := rfl

/-- Forward comparison is ordinary functorial map action followed by composition. -/
theorem computation_comp_forward :
    (L.comp M).computation.forward X i =
      V.map (L.computation.forward X (M.computation.hom (U.obj X) i)) ≫
        M.computation.forward (U.obj X) i := rfl

/-- Backward comparison retains the reverse composition order. -/
theorem computation_comp_backward :
    (L.comp M).computation.backward X i =
      M.computation.backward (U.obj X) i ≫
        V.map (L.computation.backward X (M.computation.hom (U.obj X) i)) := rfl

end MonoLift

end CasCatalogue
