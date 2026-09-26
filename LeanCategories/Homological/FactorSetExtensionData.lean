/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.GroupTheory.GroupExtension.Basic
public import Mathlib.GroupTheory.GroupAction.Basic
public import Mathlib.Tactic

/-!
# Raw factor-set extension data

Dummit--Foote, *Abstract Algebra*, Section 17.4 (FC01-C17-U070).

For a coefficient group written additively and a group `G`, the source
constructs the extension carrier `A × G` and gives its twisted multiplication
from a normalized factor set. Sweep III records only that carrier and formula.
Normalization, the cocycle identity, associativity, identity/inverse laws, and
the resulting group-extension structure are result-layer statements.
-/

@[expose] public section

namespace GroupExtension

universe uA uG

/-- A normalized additive factor set for a group action, including exactly
the cocycle law needed for the twisted product to be a group. -/
structure AddFactorSet (A : Type uA) (G : Type uG)
    [AddCommGroup A] [Group G] [DistribMulAction G A] where
  toFun : G × G → A
  cocycle : ∀ g h j,
    toFun (g, h) + toFun (g * h, j) =
      g • toFun (h, j) + toFun (g, h * j)
  map_one_one : toFun (1, 1) = 0

namespace AddFactorSet

variable {A : Type uA} {G : Type uG}
  [AddCommGroup A] [Group G] [DistribMulAction G A]

instance : FunLike (AddFactorSet A G) (G × G) A where
  coe := AddFactorSet.toFun
  coe_injective := by
    rintro ⟨f, hf, h1⟩ ⟨g, hg, h2⟩ h
    cases h
    rfl

@[simp] theorem map_one_left (f : AddFactorSet A G) (g : G) : f (1, g) = 0 := by
  change f.toFun (1, g) = 0
  have h := f.cocycle 1 1 g
  simpa [f.map_one_one] using h

@[simp] theorem map_one_right (f : AddFactorSet A G) (g : G) : f (g, 1) = 0 := by
  change f.toFun (g, 1) = 0
  have h := f.cocycle g 1 1
  simpa [f.map_one_one] using h

/-- The twisted-product extension carrier attached to a normalized factor
set. -/
@[ext] structure Extension (f : AddFactorSet A G) where
  left : A
  right : G

namespace Extension

variable {f : AddFactorSet A G}

instance : Mul f.Extension where
  mul x y := ⟨x.left + x.right • y.left + f (x.right, y.right), x.right * y.right⟩

@[simp] theorem mul_left (x y : f.Extension) :
    (x * y).left = x.left + x.right • y.left + f (x.right, y.right) := rfl

@[simp] theorem mul_right (x y : f.Extension) :
    (x * y).right = x.right * y.right := rfl

instance : One f.Extension where
  one := ⟨0, 1⟩

@[simp] theorem one_left : (1 : f.Extension).left = 0 := rfl
@[simp] theorem one_right : (1 : f.Extension).right = 1 := rfl

instance : Inv f.Extension where
  inv x :=
    ⟨x.right⁻¹ • (-(x.left + f (x.right, x.right⁻¹))), x.right⁻¹⟩

@[simp] theorem inv_left (x : f.Extension) :
    x⁻¹.left = x.right⁻¹ • (-(x.left + f (x.right, x.right⁻¹))) := rfl

@[simp] theorem inv_right (x : f.Extension) : x⁻¹.right = x.right⁻¹ := rfl

private theorem cocycle_inv (f : AddFactorSet A G) (g : G) :
    g⁻¹ • f (g, g⁻¹) = f (g⁻¹, g) := by
  change g⁻¹ • f.toFun (g, g⁻¹) = f.toFun (g⁻¹, g)
  have h := f.cocycle g⁻¹ g g⁻¹
  have h₁ : f.toFun (g⁻¹, 1) = 0 := by
    change f (g⁻¹, 1) = 0
    exact map_one_right f g⁻¹
  have h₂ : f.toFun (1, g⁻¹) = 0 := by
    change f (1, g⁻¹) = 0
    exact map_one_left f g⁻¹
  simpa [h₁, h₂] using h.symm

instance : Group f.Extension where
  mul_assoc x y z := by
    ext
    · simp only [mul_left, mul_right]
      rw [smul_add, smul_add, mul_smul]
      have hc :
          f (x.right, y.right) + f (x.right * y.right, z.right) =
            x.right • f (y.right, z.right) + f (x.right, y.right * z.right) := by
        change
          f.toFun (x.right, y.right) + f.toFun (x.right * y.right, z.right) =
            x.right • f.toFun (y.right, z.right) +
              f.toFun (x.right, y.right * z.right)
        exact f.cocycle _ _ _
      calc
        x.left + x.right • y.left + f (x.right, y.right) +
              x.right • y.right • z.left + f (x.right * y.right, z.right) =
            x.left + x.right • y.left + x.right • y.right • z.left +
              (f (x.right, y.right) + f (x.right * y.right, z.right)) := by abel
        _ = x.left + x.right • y.left + x.right • y.right • z.left +
              (x.right • f (y.right, z.right) +
                f (x.right, y.right * z.right)) := by rw [hc]
        _ = x.left +
              (x.right • y.left + x.right • y.right • z.left +
                x.right • f (y.right, z.right)) +
              f (x.right, y.right * z.right) := by abel
    · simp [mul_right, mul_assoc]
  one_mul x := by
    ext <;> simp [mul_left, mul_right]
  mul_one x := by
    ext <;> simp [mul_left, mul_right]
  inv_mul_cancel x := by
    ext
    · simp only [mul_left, inv_left, inv_right]
      change
        x.right⁻¹ • (-(x.left + f (x.right, x.right⁻¹))) +
            x.right⁻¹ • x.left + f (x.right⁻¹, x.right) = 0
      rw [smul_neg, smul_add, cocycle_inv]
      abel
    · simp [mul_right]

end Extension

/-- Inclusion of the coefficient group in the twisted product. -/
def inl (f : AddFactorSet A G) : Multiplicative A →* f.Extension where
  toFun a := ⟨a.toAdd, 1⟩
  map_one' := by ext <;> simp [Extension.one_left, Extension.one_right]
  map_mul' a b := by ext <;> simp [Extension.mul_left, Extension.mul_right]

/-- Projection of the twisted product to the quotient group. -/
def rightHom (f : AddFactorSet A G) : f.Extension →* G where
  toFun x := x.right
  map_one' := Extension.one_right
  map_mul' := Extension.mul_right

theorem inl_injective (f : AddFactorSet A G) : Function.Injective f.inl := by
  intro a b h
  exact congrArg Multiplicative.ofAdd (congrArg Extension.left h)

theorem range_inl_eq_ker_rightHom (f : AddFactorSet A G) :
    f.inl.range = f.rightHom.ker := by
  ext x
  constructor
  · rintro ⟨a, rfl⟩
    simp [MonoidHom.mem_ker, inl, rightHom]
  · intro hx
    have hx' : x.right = 1 := by simpa [MonoidHom.mem_ker, rightHom] using hx
    refine ⟨Multiplicative.ofAdd x.left, ?_⟩
    ext
    · rfl
    · exact hx'.symm

theorem rightHom_surjective (f : AddFactorSet A G) :
    Function.Surjective f.rightHom :=
  fun g => ⟨⟨0, g⟩, rfl⟩

/-- The actual group extension constructed from a normalized additive factor
set (Dummit--Foote FC01-C17-U070). -/
def groupExtension (f : AddFactorSet A G) :
    GroupExtension (Multiplicative A) f.Extension G where
  inl := f.inl
  rightHom := f.rightHom
  inl_injective := f.inl_injective
  range_inl_eq_ker_rightHom := f.range_inl_eq_ker_rightHom
  rightHom_surjective := f.rightHom_surjective

end AddFactorSet

/-- The carrier `A × G` of the extension attached to factor-set data. -/
abbrev FactorSetExtensionCarrier (A : Type uA) (G : Type uG) := A × G

/-- The distinguished identity data `(0,1)` on the factor-set extension
carrier. No identity law is asserted here. -/
def factorSetExtensionIdentity (A : Type uA) (G : Type uG)
    [Zero A] [One G] : FactorSetExtensionCarrier A G :=
  (0, 1)

/-- Dummit--Foote's displayed twisted multiplication
`(a,g) * (b,h) = (a + g • b + f(g,h), gh)` (FC01-C17-U070).

The intended `f` is a normalized two-cocycle, but those conditions and all
laws they imply are deliberately not bundled into this data constructor. -/
def factorSetExtensionMul (A : Type uA) (G : Type uG)
    [Add A] [SMul G A] [Mul G] (f : G → G → A)
    (x y : FactorSetExtensionCarrier A G) : FactorSetExtensionCarrier A G :=
  (x.1 + x.2 • y.1 + f x.2 y.2, x.2 * y.2)

end GroupExtension
