/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Lie.Extension

/-!
# Equivalence classes of Lie-algebra extensions with fixed action

Weibel, *An Introduction to Homological Algebra*, Construction 7.6.2, pp. 234--237
(FC05-C07-U044).

Mathlib already owns the short exact Lie-algebra extension and its induced action on an abelian
kernel.  Here we impose that this induced action is a fixed `L`-module action, define equivalence
by an isomorphism of middle Lie algebras that is the identity on both endpoints, and form the set
of equivalence classes denoted `Ext(L,M)` by Weibel.
-/

@[expose] public section

namespace LieAlgebra

universe u

variable (R M L : Type u) [CommRing R]
  [LieRing L] [LieAlgebra R L]
  [LieRing M] [LieAlgebra R M] [IsLieAbelian M]
  [LieRingModule L M] [LieModule R L M]

/-- An extension of `L` by the abelian Lie algebra `M` whose canonical action on the kernel is the
fixed `L`-module action on `M`.

Source: Weibel, Construction 7.6.2, pp. 234--237 (FC05-C07-U044). -/
structure ModuleExtension where
  /-- The underlying short exact Lie-algebra extension. -/
  toExtension : Extension.{u, u, u, u} R M L
  /-- The action induced by the extension agrees with the fixed action on `M`. -/
  inducesAction : ∀ x : L, ∀ m : M,
    @Bracket.bracket L M toExtension.ringModuleOf.toBracket x m = ⁅x, m⁆

namespace ModuleExtension

variable {R M L}

/-- An equivalence of extensions: an isomorphism of the middle Lie algebras which fixes the kernel
`M` and quotient `L`.

Source: Weibel, Construction 7.6.2, pp. 234--237 (FC05-C07-U044). -/
structure Equiv (E F : ModuleExtension R M L) where
  /-- Isomorphism of the middle Lie algebras. -/
  middle : E.toExtension.L ≃ₗ⁅R⁆ F.toExtension.L
  /-- The isomorphism is the identity on the kernel endpoint. -/
  incl_comm : ∀ m : M, middle (E.toExtension.incl m) = F.toExtension.incl m
  /-- The isomorphism is the identity on the quotient endpoint. -/
  proj_comm : ∀ e : E.toExtension.L,
    F.toExtension.proj (middle e) = E.toExtension.proj e

namespace Equiv

/-- Identity equivalence of extensions. -/
def refl (E : ModuleExtension R M L) : Equiv E E where
  middle := LieEquiv.refl
  incl_comm _ := rfl
  proj_comm _ := rfl

/-- Reverse an equivalence of extensions. -/
def symm {E F : ModuleExtension R M L} (e : Equiv E F) : Equiv F E where
  middle := e.middle.symm
  incl_comm m := by
    apply e.middle.injective
    simp [e.incl_comm]
  proj_comm x := by
    obtain ⟨y, rfl⟩ := e.middle.surjective x
    simp [e.proj_comm]

/-- Compose equivalences of extensions. -/
def trans {E F H : ModuleExtension R M L} (e : Equiv E F) (f : Equiv F H) : Equiv E H where
  middle := e.middle.trans f.middle
  incl_comm m := by simp [e.incl_comm, f.incl_comm]
  proj_comm x := by simp [e.proj_comm, f.proj_comm]

end Equiv

/-- Weibel's equivalence relation on extensions inducing the fixed action. -/
def Equivalent (E F : ModuleExtension R M L) : Prop := Nonempty (Equiv E F)

instance : Setoid (ModuleExtension R M L) where
  r := Equivalent
  iseqv :=
    ⟨fun E => ⟨Equiv.refl E⟩,
      fun ⟨e⟩ => ⟨e.symm⟩,
      fun ⟨e⟩ ⟨f⟩ => ⟨e.trans f⟩⟩

/-- The set `Ext(L,M)` of equivalence classes of extensions inducing the fixed action.

This is only the source's extension-class construction.  Its later identification with
`H²(L,M)` is theorem-level material.

Source: Weibel, Construction 7.6.2, pp. 234--237 (FC05-C07-U044). -/
abbrev Classes := Quotient (inferInstance : Setoid (ModuleExtension R M L))

end ModuleExtension

end LieAlgebra
