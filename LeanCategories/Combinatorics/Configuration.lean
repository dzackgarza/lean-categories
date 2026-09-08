/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Combinatorics.Configuration

/-!
# Incidence automorphisms of configurations

The source notion is Dummit--Foote FC01-C06-U026: an automorphism of a
point-line incidence structure is a permutation of its points together with a
permutation of its lines preserving incidence.
-/

@[expose] public section

namespace Configuration

universe u v

variable {P : Type u} {L : Type v} [Membership P L]

/-- An automorphism of a point-line incidence structure: simultaneous
permutations of points and lines preserving and reflecting incidence. -/
structure Automorphism where
  pointEquiv : P ≃ P
  lineEquiv : L ≃ L
  mem_iff : ∀ p l, pointEquiv p ∈ lineEquiv l ↔ p ∈ l

namespace Automorphism

/-- The identity automorphism of an incidence structure. -/
def refl : Automorphism (P := P) (L := L) where
  pointEquiv := Equiv.refl P
  lineEquiv := Equiv.refl L
  mem_iff := fun _ _ => Iff.rfl

/-- Composition of incidence automorphisms. -/
def trans (f g : Automorphism (P := P) (L := L)) : Automorphism (P := P) (L := L) where
  pointEquiv := f.pointEquiv.trans g.pointEquiv
  lineEquiv := f.lineEquiv.trans g.lineEquiv
  mem_iff := by
    intro p l
    rw [Equiv.trans_apply, Equiv.trans_apply, g.mem_iff, f.mem_iff]

/-- Inverse incidence automorphism. -/
def symm (f : Automorphism (P := P) (L := L)) : Automorphism (P := P) (L := L) where
  pointEquiv := f.pointEquiv.symm
  lineEquiv := f.lineEquiv.symm
  mem_iff := by
    intro p l
    rw [← f.mem_iff (f.pointEquiv.symm p) (f.lineEquiv.symm l)]
    simp

end Automorphism

end Configuration
