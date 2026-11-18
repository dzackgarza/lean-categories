# Issue 89 — the normal-form unit: what is left, and what it must prove

**One item of #89 is open**, and it is the only one: the completeness of the presentation
`⟨S, T | S⁴, (TS)³ = S²⟩` of `SL(2, ℤ)`, i.e.

```lean
ModularGroup.Sl2zPresentationComplete : Prop := Function.Injective sl2zToGroup
```

at `LeanCategories/ForMathlib/ModularGroupPresentation.lean:201`. Everything else in that file is
proved: the relators evaluated (`S_pow_four`, `T_mul_S_pow_three_eq_S_sq`), the presentation and its
map (`sl2zRelators`, `sl2zToGroup`), surjectivity (`sl2zToGroup_surjective`), the amalgam change of
generators as a `MulEquiv` (`sl2zAmalgamEquiv`), the factor orders in both `SL(2, ℤ)` and the
presentation (`S_sq_ne_one` … `of_one_mul_of_zero_pow_six`), and for item 2 the whole semidirect
product (`gl2z_isComplement`) and the restriction of the adjoined presentation (`sl2zInGl`).

## It is not a lookup

Probe (`.scratch/wt89-probes/closeattempt.lean`, not shipped): `exact?` and `aesop` cannot close
`Function.Injective sl2zToGroup`, and `exact?` cannot close the reduced-word datum it reduces to. No
Mathlib lemma states it: there is no pushout instance for `SL(2, ℤ)` (`PushoutI` gives normal forms
only for a pushout one maps *into*), no Farey graph and no Bass–Serre theory.

## The two components, with their Lean shape

1. **Euclid descent on the first column.** With `colHeight A := max |A 0 0| |A 1 0|` (ℤ-valued), prove
   for `2 ≤ colHeight A` that there are `ε : Fin 2`, `q : ℤ`, `A'` with
   `A = S ^ (ε : ℕ) * T ^ q * A'` and `colHeight A' < colHeight A`. Inputs: `ModularGroup.coe_T_zpow`
   for the first column of `T ^ q * A`, `Matrix.mul_fin_two` for the entries, `Int.emod_lt_abs` and
   `Int.emod_add_ediv` for `|a % c| < |c|`, and — for the two degenerate cases `c = 0` and
   `|a| = |c|` — `det = 1 ⟹ gcd a c = 1`, which is Bezout from `det_fin_two_of`.
2. **The cusp stratum.** `colHeight A = 1`, i.e. the image fixes the cusp `∞` up to sign: a word there
   must be relation-equivalent to `T ^ b`. This is the vertex-stabilizer statement of the tree action
   and is what the elementary route cannot supply; it is where a formalized amalgam normal form (or
   unique reduced words for `ℤ/4 *_{ℤ/2} ℤ/6`) enters.

The consumer named in the issue — Todd–Coxeter enumeration of cosets of finite-index subgroups of
`GL(2, ℤ)` — needs (1) and (2): with only the relations already verified, an enumeration returns a
quotient of `SL(2, ℤ)`, not `SL(2, ℤ)`.
