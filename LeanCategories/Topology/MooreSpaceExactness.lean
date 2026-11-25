module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Data.Nat.Cast.Basic

@[expose] public section

/-!
# The torsion and mod-torsion functors fail exactness on the Moore pair

Card `E-HAT-2.3-1` of the qualifying-exam corpus.  Source: Hatcher, *Algebraic
Topology*, Section 2.3, exercise 1 — the torsion subgroup and mod-torsion
functor do not define homology theories — as checked on the card (new-qual-site
`corpus/collections/SRC-TEXT-HAT02/2-3/E-HAT-2.3-1.md`).  Certificate:
new-qual-site `proofs/cards/MooreSpaceExactness.lean` at main `16c09abaa4`.

LC-09 search record (queries run against the formalization corpus and local
Mathlib): `torsion_not_exact` (corpus: 0 hits), "Moore space exactness reduced
homology" (corpus: 2 files, generic Mathlib root match).  Route: written — the
group-data exactness failures are the card's settled proof.

# `E-HAT-2.3-1`: the torsion and mod-torsion functors fail exactness on the Moore pair

For the Moore pair `(X, A)` with `A = S^1` and `X = S^1 ∪_m e^2` (`m ≥ 2`), Hatcher's
cellular computation gives the integral sequence

`0 = H_2(X) → H_2(X,A) ≅ ℤ --m--> ℤ ≅ H_1(A) → H_1(X) ≅ ℤ/m → H_1(X,A) = 0`.

The rewritten proof of the card uses three algebraic facts about these groups, each
certified here:

* `nontrivial_zmod`: `ℤ/m` is nontrivial for `m ≥ 2`, so `T_1(X) = ℤ/m` is not the
  trivial group, while `T_1(A)` and `T_1(X,A)` vanish because `ℤ`-groups are
  torsion-free. `nsmul_eq_zero_zmod` records that `ℤ/m` is torsion.
* `subsingleton_of_kernel_eq_range`: if `P` and `Q` are trivial, then a sequence
  `P → B → Q` exact at `B` forces `B` to be trivial. `torsion_not_exact` applies this
  with `B = ℤ/m`: the torsion functor's sequence at `T_1(X)` cannot be exact.
* `mul_eq_zero_int` and `not_surjective_mul`: multiplication by `m ≥ 2` on `ℤ` is
  injective but not surjective, so the mod-torsion sequence `ℤ --m--> ℤ → 0` is not
  exact at the second `ℤ` (`mod_torsion_not_exact`).

The identification of these groups with the homology of the Moore pair is Hatcher's
cellular computation, not formalized here; the file certifies the group-theoretic data
that the exactness failures turn on.
-/

namespace LeanCategories.Topology.MooreSpaceExactness

/-- The exactness-failure shape: `P → B → Q` exact at `B`, with `P` and `Q` trivial,
forces `B` to be trivial. -/
theorem subsingleton_of_kernel_eq_range {P B Q : Type*} [AddCommGroup P] [AddCommGroup B]
    [AddCommGroup Q] [Subsingleton P] [Subsingleton Q] (f : P →+ B) (g : B →+ Q)
    (h : ∀ b, g b = 0 ↔ ∃ p, f p = b) : Subsingleton B := by
  have h₀ : ∀ b : B, b = 0 := by
    intro b
    obtain ⟨p, hp⟩ := (h b).1 (Subsingleton.elim (g b) 0)
    rw [← hp, Subsingleton.elim p 0, map_zero]
  exact ⟨fun b₁ b₂ => by rw [h₀ b₁, h₀ b₂]⟩

/-- `ℤ/m` is nontrivial for `m ≥ 2`. -/
theorem nontrivial_zmod (m : ℕ) (hm : 2 ≤ m) : Nontrivial (ZMod m) :=
  @ZMod.nontrivial m ⟨by omega⟩

/-- Every element of `ℤ/m` is killed by `m`. -/
theorem nsmul_eq_zero_zmod (m : ℕ) (x : ZMod m) : m • x = 0 := by
  rw [nsmul_eq_mul, ZMod.natCast_self, zero_mul]

/-- Multiplication by `m ≥ 1` on `ℤ` is injective: the connecting map
`H_2(X,A) = ℤ → H_1(A) = ℤ` has trivial kernel, as `H_2(X) = 0` requires. -/
theorem mul_eq_zero_int (m : ℕ) (hm : 1 ≤ m) {z : ℤ} (h : (m : ℤ) * z = 0) : z = 0 := by
  rcases mul_eq_zero.mp h with h1 | h2
  · exact absurd h1 (by exact_mod_cast (by omega : m ≠ 0))
  · exact h2

/-- Multiplication by `m ≥ 2` on `ℤ` is not surjective. -/
theorem not_surjective_mul (m : ℕ) (hm : 2 ≤ m) :
    ¬ Function.Surjective fun z : ℤ => (m : ℤ) * z := by
  intro hs
  obtain ⟨z, hz⟩ := hs 1
  have hdvd : (m : ℤ) ∣ 1 := ⟨z, hz.symm⟩
  have hle : (m : ℤ) ≤ 1 := Int.le_of_dvd one_pos hdvd
  have hge : (2 : ℤ) ≤ (m : ℤ) := by exact_mod_cast hm
  omega

/-- The torsion functor's sequence at `T_1(X) = ℤ/m`: with trivial groups on both sides
it cannot be exact for `m ≥ 2`, whichever maps the functor induces. -/
theorem torsion_not_exact (m : ℕ) (hm : 2 ≤ m) (f : ZMod 1 →+ ZMod m)
    (g : ZMod m →+ ZMod 1) : ¬ ∀ b, g b = 0 ↔ ∃ p, f p = b := by
  intro h
  have hsub : Subsingleton (ZMod m) := subsingleton_of_kernel_eq_range f g h
  obtain ⟨a, b, hab⟩ := @exists_pair_ne (ZMod m) (nontrivial_zmod m hm)
  exact hab (hsub.elim a b)

/-- The mod-torsion sequence `ℤ --m--> ℤ → 0` is not exact at the second `ℤ` for
`m ≥ 2`: the image of multiplication by `m` is a proper subgroup. -/
theorem mod_torsion_not_exact (m : ℕ) (hm : 2 ≤ m) :
    ¬ ∀ y : ℤ, ∃ x : ℤ, (m : ℤ) * x = y := not_surjective_mul m hm

end LeanCategories.Topology.MooreSpaceExactness
