/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.EuclideanDomain.Basic
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Basic.Complex.Basic
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.Logic.Equiv.Basic

@[expose] public section

/-!
# Direct products of groups: the general statements of the Chapter 8 cards

Cards `P-CH8-1`, `P-CH8-3`, `P-CH8-4`, `P-CH8-7`, `P-CH8-15` and `P-CH8-40` of the
qualifying-exam corpus.  Source: Gallian, *Contemporary Abstract Algebra*, 7th edition,
chapter 8, printed pages 167–170.  Certificate: new-qual-site `proofs/cards/CH8DirectProduct.lean`
at commit `16c09abaa4`.

The finite computations of the same collection are checked in new-qual-site
`proofs/cards/CH8DirectProduct.g`; the two files are complementary: this one states the uniform
statements, the GAP file checks the particular groups.  Each declaration names the card whose
solution it certifies, and each proof names the Mathlib declaration that carries it.

## The Mathlib hits

LC-09 search record (formalization corpus and local Mathlib, several formulations).  Nine of the
certificate's seventeen declarations state exactly what a Mathlib declaration already states, and
their proofs are those declarations; they are written here so that the card has a name to link,
which is the one purpose a restatement is allowed:

| declaration | Mathlib statement it restates |
| --- | --- |
| `product_mul_apply` | `Pi.mul_apply` |
| `product_one_apply` | `Pi.one_apply` |
| `prod_bot_eq_ker_snd` | `MonoidHom.ker_snd` (`(MonoidHom.snd G H).ker = ⊤.prod ⊥`) |
| `prod_bot_normal` | `Subgroup.prod_normal ⊤ ⊥` |
| `bot_prod_normal` | `Subgroup.prod_normal ⊥ ⊤` |
| `prodBotMulEquiv` | `MulEquiv.prodUnique`, whose hypothesis is `Unique H` |
| `botProdMulEquiv` | `MulEquiv.uniqueProd`, same |
| `prodCommMulEquiv` | `MulEquiv.prodComm` |
| `complexAddEquivRealProd` | `Complex.equivRealProdAddHom` |

The group structure on the external direct product of `P-CH8-1` is Mathlib's instance on the pi
type, and its operations are the pointwise ones the card writes.  Queries run:
`content:MulEquiv.prodComm`, `content:Subgroup.prod normal quotient group factor`,
`prod_bot_eq_ker_snd fst snd kernel quotient isomorphic`, `content:Prod.orderOf`,
`orderOf tuple direct product infinite iff some coordinate`,
`content:Complex.equivRealProdAddHom`, `content:Pi.mul_apply`, `content:MonoidHom.ker_snd`,
`content:MulEquiv.prodUnique`, `quotient group product normal subgroup second projection
isomorphic`.

What is *not* in Mathlib at this head, and is written here: the two quotient isomorphisms of
`P-CH8-3`, the abelian-iff-both criterion of `P-CH8-4`, the permuted-index isomorphism of
`P-CH8-7` (there is no `MulEquiv.piCongrLeft`), and the two infinite-order criteria of
`P-CH8-40`.  The last two are glue over Mathlib's `Prod.orderOf` and `Pi.orderOf`, which already
state the order of a tuple as an `lcm`; that replaces the certificate's own coordinate analysis
(`pi_pow_eq_one_of_coord`, `coord_pow_eq_one`), which is therefore not ported.

Provenance: ported from new-qual-site at commit `16c09abaa4`, `proofs/cards/CH8DirectProduct.lean`.
Repaired in the port: the definitions are renamed to `lowerCamelCase`
(`quotientProdBotMulEquiv`, `quotientBotProdMulEquiv`, `prodBotMulEquiv`, `botProdMulEquiv`,
`prodCommMulEquiv`, `piPermMulEquiv`, `complexAddEquivRealProd`), which the repository's
`defsWithUnderscore` lint requires of definitions; theorem names keep the certificate's spelling,
as `LeanCategories/Homological/DeltaSimplexChains.lean` does after the same finding.  The
certificate's `[Fintype ι]` in `pi_orderOf_eq_zero_iff` is the card's "finite index set" and is
written `[Finite ι]`, the form the repository's `unusedFintypeInType` finding asks for.
-/

open scoped BigOperators

namespace LeanCategories.Algebra.CH8DirectProduct

/-! ## `P-CH8-1`: the external direct product of finitely many groups is a group -/

/-- Multiplication in the external direct product is componentwise: Mathlib's `Pi.mul_apply`. -/
theorem product_mul_apply (n : ℕ) (G : Fin n → Type*) [∀ i, Group (G i)]
    (x y : ∀ i, G i) (i : Fin n) : (x * y) i = x i * y i :=
  Pi.mul_apply x y i

/-- The identity of the external direct product is the tuple of identities, and inverses are
componentwise: Mathlib's `Pi.one_apply`. -/
theorem product_one_apply (n : ℕ) (G : Fin n → Type*) [∀ i, Group (G i)] (i : Fin n) :
    (1 : ∀ i, G i) i = 1 :=
  Pi.one_apply (M := G) i

/-! ## `P-CH8-3`: `G ⊕ {e}` and `{e} ⊕ H` are normal, with the stated quotients -/

section prodbot

variable (G H : Type*) [Group G] [Group H]

/-- `G × {e}` is the kernel of the second projection: Mathlib's `MonoidHom.ker_snd`, in the
orientation the card writes. -/
theorem prod_bot_eq_ker_snd :
    ((⊤ : Subgroup G).prod (⊥ : Subgroup H)) = (MonoidHom.snd G H).ker :=
  (MonoidHom.ker_snd (G := G) (G' := H)).symm

/-- `G × {e}` is a normal subgroup of `G × H`: Mathlib's `Subgroup.prod_normal`. -/
theorem prod_bot_normal : Subgroup.Normal ((⊤ : Subgroup G).prod (⊥ : Subgroup H)) :=
  Subgroup.prod_normal ⊤ ⊥

/-- `{e} × H` is the kernel of the first projection, hence normal: Mathlib's
`Subgroup.prod_normal`. -/
theorem bot_prod_normal : Subgroup.Normal ((⊥ : Subgroup G).prod (⊤ : Subgroup H)) :=
  Subgroup.prod_normal ⊥ ⊤

/-- `(G × H) / (G × {e}) ≅ H`: the second projection kills exactly the first factor.  The
identification of `G × {e}` with the kernel of that projection is Mathlib's
`MonoidHom.ker_snd`, so the quotient is Mathlib's `quotientKerEquivOfSurjective` of the
projection. -/
noncomputable def quotientProdBotMulEquiv :
    ((G × H) ⧸ ((⊤ : Subgroup G).prod (⊥ : Subgroup H))) ≃* H :=
  (QuotientGroup.quotientMulEquivOfEq (MonoidHom.ker_snd (G := G) (G' := H)).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (MonoidHom.snd G H) Prod.snd_surjective)

/-- `(G × H) / ({e} × H) ≅ G`: the first projection kills exactly the second factor, dually. -/
noncomputable def quotientBotProdMulEquiv :
    ((G × H) ⧸ ((⊥ : Subgroup G).prod (⊤ : Subgroup H))) ≃* G :=
  (QuotientGroup.quotientMulEquivOfEq (MonoidHom.ker_fst (G := G) (G' := H)).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (MonoidHom.fst G H) Prod.fst_surjective)

end prodbot

section proddone

variable (G : Type*) [Group G] (H : Type*) [Group H]

/-- `G × {e} ≅ G`: the first half of `P-CH8-3`, with the trivial group written as a
one-point type.  Mathlib's `MulEquiv.prodUnique` states it for `[Unique H]`; the card's
`[Subsingleton H]` supplies that. -/
noncomputable def prodBotMulEquiv [Subsingleton H] : G × H ≃* G := by
  haveI : Inhabited H := ⟨1⟩
  haveI : Unique H := Unique.mk' H
  exact MulEquiv.prodUnique

/-- `{e} × H ≅ H`: the second half of `P-CH8-3`.  Mathlib's `MulEquiv.uniqueProd`. -/
noncomputable def botProdMulEquiv [Subsingleton H] : H × G ≃* G := by
  haveI : Inhabited H := ⟨1⟩
  haveI : Unique H := Unique.mk' H
  exact MulEquiv.uniqueProd

end proddone

/-! ## `P-CH8-4`: `G ⊕ H` is abelian if and only if `G` and `H` are -/

section prodcomm

variable (G H : Type*) [Group G] [Group H]

/-- The external direct product is abelian exactly when both factors are: a commutator of the
product is a pair of commutators, and each factor embeds in the product. -/
theorem prod_comm_iff :
    (∀ x y : G × H, x * y = y * x) ↔
      (∀ x y : G, x * y = y * x) ∧ (∀ x y : H, x * y = y * x) := by
  constructor
  · intro h
    exact ⟨fun x y => congrArg Prod.fst (h (x, 1) (y, 1)),
           fun x y => congrArg Prod.snd (h (1, x) (1, y))⟩
  · rintro ⟨hG, hH⟩ ⟨a, b⟩ ⟨c, d⟩
    ext <;> simp [hG, hH]

end prodcomm

/-! ## `P-CH8-7`: `G₁ ⊕ G₂ ≅ G₂ ⊕ G₁`, and the general case -/

/-- The two-factor case of `P-CH8-7`: Mathlib's `MulEquiv.prodComm`. -/
noncomputable def prodCommMulEquiv (G H : Type*) [Group G] [Group H] : G × H ≃* H × G :=
  MulEquiv.prodComm

/-- **The general case of `P-CH8-7`**: permuting the index set of a direct product gives an
isomorphic group.  Mathlib owns the underlying equivalence `Equiv.piCongrLeft` and the
multiplicative structure of the pi type; there is no `MulEquiv.piCongrLeft` at this head, so the
`MulEquiv` is assembled here. -/
noncomputable def piPermMulEquiv {ι κ : Type*} (e : ι ≃ κ) (G : κ → Type*)
    [∀ k, Group (G k)] : (∀ k, G k) ≃* (∀ i, G (e i)) :=
  { (Equiv.piCongrLeft G e).symm with
    map_mul' := fun _ _ => rfl }

/-! ## `P-CH8-15`: the additive group of `ℂ` is `ℝ ⊕ ℝ` -/

/-- The group of complex numbers under addition is the direct product of two copies of `ℝ`, as
the card asserts: Mathlib's `Complex.equivRealProdAddHom`. -/
noncomputable def complexAddEquivRealProd : ℂ ≃+ ℝ × ℝ :=
  Complex.equivRealProdAddHom

/-! ## `P-CH8-40`: a tuple has infinite order exactly when a coordinate does -/

/-- In a direct product of two groups the order of a tuple is the `lcm` of the orders of its
coordinates (Mathlib's `Prod.orderOf`), so the tuple has infinite order exactly when some
coordinate does. -/
theorem prod_orderOf_eq_zero_iff {G H : Type*} [Group G] [Group H] (x : G × H) :
    orderOf x = 0 ↔ orderOf x.1 = 0 ∨ orderOf x.2 = 0 := by
  rw [Prod.orderOf, Nat.lcm_eq_zero_iff]

/-- The same for a finite family: the order of a tuple is the `lcm` of the coordinate orders
(Mathlib's `Pi.orderOf`), so it is infinite exactly when some coordinate has infinite order.
The finiteness is used by that `lcm`; over an infinite index set the statement fails, since a
tuple all of whose coordinates have finite order can still have infinite order. -/
theorem pi_orderOf_eq_zero_iff {ι : Type*} [Finite ι] {G : ι → Type*} [∀ i, Group (G i)]
    (x : ∀ i, G i) : orderOf x = 0 ↔ ∃ i, orderOf (x i) = 0 := by
  classical
  let := Fintype.ofFinite ι
  rw [Pi.orderOf, Finset.lcm_eq_zero_iff]
  simp

end LeanCategories.Algebra.CH8DirectProduct
