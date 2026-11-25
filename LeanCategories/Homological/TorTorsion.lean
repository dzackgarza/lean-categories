module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Data.Nat.Cast.Basic

@[expose] public section

/-!
# The coordinate step in the converse for `Tor`

Card `E-HAT-3.A-6` of the qualifying-exam corpus.  Source: Hatcher, *Algebraic
Topology*, Section 3.A, exercise 6 — "`Tor(A, B)` contains an element of order
`n` if and only if both `A` and `B` do".  Certificate: new-qual-site
`proofs/cards/TorTorsion.lean` at commit `16c09abaa4`.

LC-09 search record (queries run against the formalization corpus and local
Mathlib): `ratchet_le` (0 hits); `exact_order_smul` (0 hits).  Route: written —
the coordinate step is the card's settled proof.

# `E-HAT-3.A-6`: the coordinate step in the converse for `Tor`

Hatcher, *Algebraic Topology*, §3.A exercise 6: `Tor(A, B)` contains an element of
order `n` if and only if both `A` and `B` do.

The converse reduces to groups: for an abelian group `B` and a finite family of
subgroups `B[p^(k j)]`, a class of order exactly `p^m` in their product has a
coordinate of order exactly `p^m`, and that coordinate lies in `B` itself. Writing
"order exactly `p^m`" as "killed by `p^m` but not by `p^(m-1)`", this file certifies:

* `ratchet_le`: an element of exact order `p^m` that is also killed by `p^k` forces
  `m ≤ k`. So a coordinate in `B[p^k]` of order `p^m` gives `k ≥ m` and nothing more;
  in particular no element of order `p^k` in `B`.
* `exact_order_smul`: from an element of exact order `p^k` one gets one of exact order
  `p^m` for every `m ≤ k`, by multiplying.
* `exists_coord`: a family of coordinates each killed by `p^(k j)`, one of which is not
  killed by `p^(m-1)`, has a coordinate of exact order `p^m`, and `m ≤ k j` there.
* `zmod_two_no_exact_order_eight`: with `A = Z/8`, `B = Z/2` and `n = 2`, the group
  `B = Z/2` has `8`-torsion — every element is killed by `8` — but no element of exact
  order `8`. This is the inference the earlier version of the card made and that is
  false as stated.
* `zmod_eight_order_four`: on the `A` side, `2` is an element of `Z/8` of exact order
  `4`, the `m = 2`, `k = 3` instance of `exact_order_smul`.

The Tor-theoretic reductions that put the coordinate step in play are not formalized
here; the card cites them by name: `Tor(A,B) ≅ Tor(T(A),B)` because `A/T(A)` is
torsion-free hence flat, `Tor` commutes with direct sums, `Tor(A_p,B) ≅ Tor(A_p,B_p)`
because `B/B_p` has no `p`-torsion, `Tor(Z/p^k,B) ≅ B[p^k]`, and `Tor` commutes with
direct limits.
-/

namespace LeanCategories.Homological.TorTorsion

variable {B : Type*} [AddCommGroup B]

/-- `p^(j+k) • x = p^j • (p^k • x)` in any additive commutative group. -/
theorem smul_pow_mul (p j k : ℕ) (x : B) : p ^ (j + k) • x = p ^ j • (p ^ k • x) := by
  rw [pow_add]
  exact mul_nsmul' x (p ^ j) (p ^ k)

/-- `p^(j+k) • x = p^k • (p^j • x)`, the same identity read the other way round. -/
theorem smul_pow_mul' (p j k : ℕ) (x : B) : p ^ (j + k) • x = p ^ k • (p ^ j • x) := by
  rw [Nat.add_comm, smul_pow_mul]

/-- An element killed by `p^m` but not by `p^(m-1)` — of exact order `p^m` — that is
also killed by `p^k` forces `m ≤ k`. -/
theorem ratchet_le (p m k : ℕ) (x : B)
    (hm1 : p ^ (m - 1) • x ≠ 0) (hk : p ^ k • x = 0) : m ≤ k := by
  rcases lt_or_ge k m with hlt | hge
  · exfalso
    have h1 : m - 1 = k + (m - 1 - k) := by omega
    rw [h1, smul_pow_mul', hk, nsmul_zero] at hm1
    exact hm1 rfl
  · exact hge

/-- An element of exact order `p^k` yields one of exact order `p^m` for every `m ≤ k`. -/
theorem exact_order_smul (p m k : ℕ) (hm : 0 < m) (hmk : m ≤ k) (a : B)
    (hk0 : p ^ k • a = 0) (hk1 : p ^ (k - 1) • a ≠ 0) :
    p ^ m • (p ^ (k - m) • a) = 0 ∧ p ^ (m - 1) • (p ^ (k - m) • a) ≠ 0 := by
  constructor
  · rw [← smul_pow_mul, Nat.add_sub_cancel' hmk, hk0]
  · intro h
    apply hk1
    rw [← smul_pow_mul, show m - 1 + (k - m) = k - 1 by omega] at h
    exact h

/-- The coordinate step: a family of elements each killed by `p^(k j)`, some member of
which is not killed by `p^(m-1)`, has a coordinate of exact order `p^m`, and at that
coordinate `m ≤ k j`. -/
theorem exists_coord (p m : ℕ) {J : Type*} (k : J → ℕ) (x : J → B)
    (hx : ∀ j, p ^ (k j) • x j = 0)
    (hm0 : ∀ j, p ^ m • x j = 0)
    (hm1 : ∃ j, p ^ (m - 1) • x j ≠ 0) :
    ∃ j, m ≤ k j ∧ p ^ m • x j = 0 ∧ p ^ (m - 1) • x j ≠ 0 := by
  obtain ⟨j, hj⟩ := hm1
  exact ⟨j, ratchet_le p m (k j) (x j) hj (hx j), hm0 j, hj⟩

/-- `B = Z/2` has `8`-torsion but no element of exact order `8`: the rejected
inference, with `p = 2`, `k = 3`, `m = 2`, `A = Z/8`, `B = Z/2`. -/
theorem zmod_two_no_exact_order_eight :
    ¬ ∃ x : ZMod 2, (2 ^ 3 : ℕ) • x = 0 ∧ (2 ^ 2 : ℕ) • x ≠ 0 := by
  rintro ⟨x, -, h2⟩
  apply h2
  have h4 : ((2 ^ 2 : ℕ) : ZMod 2) = 0 := by decide
  rw [nsmul_eq_mul, h4, zero_mul]

/-- Every element of `Z/2` is killed by `8`, so `B[8] = B` and `8`-torsion certainly
exists there. -/
theorem zmod_two_is_eight_torsion (x : ZMod 2) : (2 ^ 3 : ℕ) • x = 0 := by
  have h8 : ((2 ^ 3 : ℕ) : ZMod 2) = 0 := by decide
  rw [nsmul_eq_mul, h8, zero_mul]

/-- The `A` side: `2` is an element of `Z/8` of exact order `4`, obtained from the
element `1` of exact order `8` by multiplying by `2^(3-2)`. -/
theorem zmod_eight_order_four :
    (2 ^ 2 : ℕ) • ((2 ^ (3 - 2) : ℕ) • (1 : ZMod 8)) = 0 ∧
      (2 ^ (2 - 1) : ℕ) • ((2 ^ (3 - 2) : ℕ) • (1 : ZMod 8)) ≠ 0 := by
  refine exact_order_smul 2 2 3 (by omega) (by omega) 1 ?_ ?_
  · decide
  · decide

end LeanCategories.Homological.TorTorsion
