# #23 — state of `VinbergE10Chamber.lean` (branch `wip/e10-vinberg-chamber`)

Toolchain environment at hand-off (2026-11 image):
* worktree `.scratch/wt23b` on local branch `wip/e10-vinberg-chamber`, based on main `9867918e`.
* Packages materialized at **main's manifest pin** `6526be5` (Mathlib master has since moved to
  `bbff2954`); `scripts/cache-get.sh` linked the certified build-store trees. 52 G free.
* `lake build LeanCategories.All` → 12132 jobs, exit 0. (Note: `lake build` alone builds only
  8340 jobs — the root module `LeanCategories.lean` does not import `LeanCategories.All`.)
* Typecheck a single module with: `lake env lean LeanCategories/Lattices/Valued/VinbergE10Chamber.lean`

## Verified (compiles): `.wip/e10-arith-core.lean`
`e10Edge`, `e10Adjacency`, `e10Cartan`, `e10Cartan_eq` (= 2·1 − adjacency, by `ext;fin_cases;decide`),
`e10CartanInverse` with `e10Cartan_mul_inverse` and `e10Cartan_inverse_mul` (2×100 `decide`,
~30 s), `e10Cartan_isSymm`, `quadC`, `dotProduct_adjacency`, `quadC_energy`, `quadC_even`.
Run it with `lake env lean .wip/e10-arith-core.lean` (~5 min, mostly `decide`).

## Remaining errors in `VinbergE10Chamber.lean` (12, all plumbing)
line 177 `toRealForm_sum`: `TensorProduct.tmul_smul`/`Int.cast_smul_eq_zsmul` do not close it.
line 199 `e10BlockGram_isSymm`: `simpa`/`decide +revert` does not reduce the block cases —
  use `Matrix.fromBlocks_apply_inl_inl` etc. explicitly, or `ext i j; rcases …; simp; omega`.
line 238 `e10BlockGram_det`: `Matrix.det_smul` does not match after `det_fromBlocks_zero₁₂`;
  the `Matrix.det_smul` statement is `(a • M).det = a ^ card * M.det`, so rewrite it as
  `Matrix.det_smul _ _` with the exponent `Fintype.card (Fin 2)` / `(Fin 8)` made explicit.
line 250 `e10BlockGram_signature` `hmap`: the `e8GramMatrix_eq` literal is a *vector of rows*
  (`![![…], …]`), not a `Matrix.of` literal; the `simp only` list must use
  `Matrix.cons_val`/`Matrix.cons_val'` at the right arity, or state `hmap` with `funext`-free
  `Matrix.fromBlocks_map`.
line 266 `e10Lattice_integralSignature`: `gramMatrix e10FiniteLattice.obj` vs `e10Lattice` —
  `e10FiniteLattice.obj` is defeq to `e10Lattice`; insert `show` or state the sign. theorem
  for `e10FiniteLattice`.
line 312 `e10Root`: `Sum.elim (fun c => if c = 0 then … else …)` needs `Fin 2` decidable
  equality made explicit — write `fun c => if (c : ℕ) = 0 then … else …` and `decide`-free
  `if_neg`/`if_pos`.
line 332 `e10Root_pairing`: `rw [e10Lattice_pairing]` misses because `e10Lattice_pairing` is
  stated for `e10Lattice.obj.carrier` while the goal has the `ModuleCat`-coerced carrier;
  insert `change` or restate as `Matrix.toBilin'_apply`.
lines 348/376/385/387: same two causes (carrier coercion, `Sum` index literals).

## Not done at all
* `e10_signs` : `quadC b = 2 → (∀ i, 0 ≤ b i) ∨ (∀ i, b i ≤ 0)`.
  Needs: (1) PD on `E₁₀∖{i}` for `i ≠ 9` (nine cases; reduce to E₈ — `e8Lattice_matrixSignature`
  — plus the star forms T(1,1,6) and T(1,2,3) and paths, by the branch Cauchy–Schwarz bound
  `Σ 1/(βⱼ+1) > 1`), (2) PSD on `E₁₀∖{9}` (affine E₉, `Σ 1/(βⱼ+1) = 1`, null vector δ),
  (3) the mixed-sign bound (quadC even + disjoint supports ⟹ ≥ 4).
* `e10_reflective_norm` : reflective ∧ negative square ⟹ `quadC b = 2`, via `S ∣ 2(Cb)ᵢ`,
  `e10CartanInverse` integral, and `b = k·c ⟹ k·S(c) = 2`.
* Registration in `LeanCategories/All.lean` (in the same commit), `just test`, push to `main`.
