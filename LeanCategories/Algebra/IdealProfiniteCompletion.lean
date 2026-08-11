/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RingTheory.DedekindDomain.Factorization
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Completion over all nonzero ideals

This file gives the explicit inverse limit of the quotient rings `R / I`, indexed by the nonzero
ideals of a domain.
-/

@[expose] public section

noncomputable section

namespace LeanCategories

universe u

variable (R : Type u) [CommRing R]

/-- A nonzero ideal. -/
abbrev NonzeroIdeal := {I : Ideal R // I ≠ ⊥}

namespace IdealProfiniteCompletion

/-- The quotient transition map associated to an inclusion of nonzero ideals. -/
def transition {I J : NonzeroIdeal R} (h : (I : Ideal R) ≤ J) :
    R ⧸ (I : Ideal R) →+* R ⧸ (J : Ideal R) :=
  Ideal.Quotient.factor h

@[simp]
theorem transition_mk {I J : NonzeroIdeal R} (h : (I : Ideal R) ≤ J) (r : R) :
    transition R h (Ideal.Quotient.mk (I : Ideal R) r) =
      Ideal.Quotient.mk (J : Ideal R) r :=
  rfl

/-- Compatible residue families form an `R`-subalgebra of the product of all quotient rings. -/
def subalgebra : Subalgebra R ((I : NonzeroIdeal R) → R ⧸ (I : Ideal R)) where
  carrier := {x | ∀ (I J : NonzeroIdeal R) (h : (I : Ideal R) ≤ J),
    transition R h (x I) = x J}
  zero_mem' := by intro I J h; simp [transition]
  one_mem' := by intro I J h; simp [transition]
  add_mem' := by
    intro x y hx hy I J h
    change transition R h (x I + y I) = x J + y J
    rw [map_add, hx I J h, hy I J h]
  mul_mem' := by
    intro x y hx hy I J h
    change transition R h (x I * y I) = x J * y J
    rw [map_mul, hx I J h, hy I J h]
  algebraMap_mem' := by
    intro r I J h
    exact transition_mk R h r

/-- The inverse limit of `R / I` over all nonzero ideals `I`. -/
abbrev Completion := subalgebra R

/-- Evaluation at one nonzero ideal. -/
def eval (I : NonzeroIdeal R) : Completion R →ₐ[R] R ⧸ (I : Ideal R) :=
  { toFun := fun x ↦ x.1 I
    map_one' := rfl
    map_mul' _ _ := rfl
    map_zero' := rfl
    map_add' _ _ := rfl
    commutes' _ := rfl }

@[simp]
theorem eval_apply (I : NonzeroIdeal R) (x : Completion R) :
    eval R I x = x.1 I :=
  rfl

/-- The diagonal map into the inverse limit. -/
def diagonal : R →ₐ[R] Completion R :=
  Algebra.ofId R (Completion R)

@[simp]
theorem eval_diagonal (I : NonzeroIdeal R) (r : R) :
    ((diagonal R r : Completion R) :
      (I : NonzeroIdeal R) → R ⧸ (I : Ideal R)) I =
        Ideal.Quotient.mk (I : Ideal R) r :=
  rfl

/-- A compatible family of algebra maps into the quotients induces a map into the inverse limit. -/
def lift {S : Type u} [CommRing S] [Algebra R S]
    (f : (I : NonzeroIdeal R) → S →ₐ[R] R ⧸ (I : Ideal R))
    (hf : ∀ (I J : NonzeroIdeal R) (h : (I : Ideal R) ≤ J),
      (Ideal.Quotient.factorₐ R h).comp (f I) = f J) :
    S →ₐ[R] Completion R where
  toFun s := ⟨fun I ↦ f I s, fun I J h ↦ AlgHom.congr_fun (hf I J h) s⟩
  map_one' := by apply Subtype.ext; funext I; exact map_one (f I)
  map_mul' x y := by apply Subtype.ext; funext I; exact map_mul (f I) x y
  map_zero' := by apply Subtype.ext; funext I; exact map_zero (f I)
  map_add' x y := by apply Subtype.ext; funext I; exact map_add (f I) x y
  commutes' r := by apply Subtype.ext; funext I; exact (f I).commutes r

@[simp]
theorem eval_lift {S : Type u} [CommRing S] [Algebra R S]
    (f : (I : NonzeroIdeal R) → S →ₐ[R] R ⧸ (I : Ideal R))
    (hf : ∀ (I J : NonzeroIdeal R) (h : (I : Ideal R) ≤ J),
      (Ideal.Quotient.factorₐ R h).comp (f I) = f J)
    (I : NonzeroIdeal R) (s : S) :
    ((lift R f hf s : Completion R) :
      (I : NonzeroIdeal R) → R ⧸ (I : Ideal R)) I = f I s :=
  rfl

/-- Maps into the inverse limit are determined by all quotient projections. -/
theorem hom_ext {S : Type u} [CommRing S] [Algebra R S]
    {f g : S →ₐ[R] Completion R}
    (h : ∀ I, (eval R I).comp f = (eval R I).comp g) : f = g := by
  ext s I
  exact AlgHom.congr_fun (h I) s

end IdealProfiniteCompletion

end LeanCategories
