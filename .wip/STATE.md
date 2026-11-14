# #23 — state of the Vinberg chamber of E₁₀(2) (branch `wip/e10-vinberg-chamber`)

Worktree `.scratch/wt23b`, branch `wip/e10-vinberg-chamber`, based on main `9867918e`.
Packages at main's manifest pin `6526be5`. Commands:
* typecheck one module: `lake env lean LeanCategories/Lattices/Valued/<File>.lean`
* acceptance: `just test` (build + lean-no-sorry + vacuity + mathlib-lint + unused-variables +
  axiom-audit).

## DONE and compiling: `LeanCategories/Lattices/Valued/VinbergE10Roots.lean` (1332 lines, in `All.lean`)

The whole arithmetic layer of the obligation, and the **sign lemma** (step 1 + step 3 of the route):

* `e10Edge`, `e10Adjacency`, `e10Cartan`, `e10Cartan_eq` (2·1 − A), `e10CartanInverse` with
  `e10Cartan_mul_inverse` and `e10Cartan_inverse_mul` (so `C` is unimodular, `det C = -1`),
  `e10Cartan_isSymm`.
* `quadC b = b ⬝ᵥ (C b)`; `quadC_explicit` (the Cartesian expansion), `quadC_even` (2 ∣ quadC b),
  `e10NullVector` = δ of the affine subdiagram `E₉`, `quadC_e10NullVector` (`decide`),
  `quadC_smul`, `quadC_nullVector`, `quadC_sub` (the expansion of `quadC (u - v)` along the edges).
* **Ten sum-of-squares certificates** `e10CertZero … e10CertNine`: for `u i = 0`,
  `N · quadC u` is a sum of squares with positive integral coefficients. They come from the `LDLᵀ`
  elimination of the principal submatrix `C[univ ∖ {i}]` with the tree rooted at the trivalent node
  `4` (children peeled from the leaves inward). Pivots (node : pivot):
  * `i = 9` (the affine `E₉`): `4 : 0`, `1,2 : 2`, `3,8 : 3/2`, `7 : 4/3`, `6 : 5/4`, `5 : 6/5`,
    `0 : 2` — the single **zero** pivot is the affine degeneracy, and the resolution of the
    triangular system reproduces `δ = (1,2,3,4,6,5,4,3,2)` at nodes `0…8`.
  * every other `i` gives all pivots **strictly positive** (e.g. `i = 0`: root `4 : 1/30`;
    `i = 8`: `4 : 1/12`), so the principal submatrix is positive definite.
* `quadC_nonneg_of_zero` (nonnegativity away from any coordinate hyperplane) and
  `quadC_eq_zero_of_zero` (kernel = ℤ·δ) follow by `fin_cases` on the node.
* **`quadC_eq_two_signs`**: `quadC b = 2 → (∀ i, 0 ≤ b i) ∨ (∀ i, b i ≤ 0)`. Proof: split
  `b = u - v` into positive and negative parts (`hu`, `hv`, disjoint support), so
  `2 = quadC u + quadC v + 2 Σ_{edges}(u a·v b + v a·u b)` with all terms ≥ 0 and the first two
  even; every part is `0` (a multiple of δ) or ≥ 2, and if a part is `k·δ` the other is supported at
  node `9` alone so the edge `(0,9)` contributes ≥ 2 more. Either way `quadC b ≥ 4`, contradiction.
  **Integrality is essential**: over ℚ the statement is false (`quadC` is indefinite).

## REMAINING for #23's acceptance (not in this commit)

1. `LeanCategories/Lattices/Valued/VinbergE10Chamber.lean` (the lattice-level file, 429+ lines,
   *not* in `All.lean`) still does not elaborate; `lake env lean` on it reports these errors:
   * `quadC_energy` (l.181): after the rewrites the goal is an equality of `Finset.sum`s
     (`∑ x, b x * (b x + b x) - ∑ i, 2 * (…) = 2 * (…)`); `Finset.sum_mul` no longer matches.
     **Fix**: drop `quadC_energy`/`dotProduct_adjacency` from the module and take `quadC_even` from
     `quadC_explicit` (`omega`), as `VinbergE10Roots.lean` does.
   * `e10BlockGram_isSymm` (l.203): `simp [e10BlockGram]` leaves `Matrix.of ((… ⊕ᵥ …))`; prove
     `(2 • hyperbolicPlaneGramMatrix).IsSymm` and `(2 • e8GramMatrix).IsSymm` separately
     (`funext`-free, `fin_cases`/`IsSymm.apply`) and feed them into the four `Sum` cases with
     `simpa`.
   * `e10BlockGram_det` (l.248): `Matrix.det_smul` does not unify with `(2 • e8GramMatrix).det`
     (the `SMul` instance path); use `(Matrix.det_smul e8GramMatrix 2)` applied explicitly, plus
     `e8GramMatrix_det` (`Standard.lean:1007`), and `Matrix.det_fin_two` for the plane (that part
     works).
   * `e10BlockGram_signature` (l.268): the `Sum.inr/Sum.inr` case of `hmap`; the block entry is
     `Matrix.of ((… ⊕ᵥ …))` and needs `Int.cast_mul` + `push_cast; ring` after reducing `⊕ᵥ`
     (`Matrix.fromBlocks_apply_inl_inl`-style lemmas; `e8GramMatrix_eq` must **not** be unfolded
     into the literal, which is a *vector of rows*).
   * `e10Lattice_integralSignature` (l.341): the `Pi.basisFun` must be given the lattice's carrier
     by name: `let b : Module.Basis (Fin 2 ⊕ Fin 8) ℤ e10FiniteLattice.obj.obj.carrier :=
     Pi.basisFun ℤ (Fin 2 ⊕ Fin 8)` (the idiom of `cobleFiniteLattice_integralSignature`,
     `CobleQuotientSignature.lean:136`). With that the proof goes through as written.
   * `e10RootMatrixInverse` (l.329): the column index is `Fin 2 ⊕ Fin 8`, the literal is 10×10;
     index it through `finSumFinEquiv`.
   * `e10Root_pairing` (l.350) and the later `pairing` statements: `e10Root i` has type
     `Fin 2 ⊕ Fin 8 → ℤ` but `L.obj.obj.pairing` wants `↑L.obj.carrier` (the carrier is
     `L.carrierObj`, a `def`, so the elaborator does not coerce). Write the goal with
     `show Matrix.toBilin' e10BlockGram (e10Root i) (e10Root j) = …` instead of the `L.pairing`
     form, and prove the `L.pairing` form from `e10Lattice_pairing` (`rfl`) only where the
     `WeylChambers` API forces the carrier type.
   * `toRealForm_sum` (l.368): `TensorProduct.tmul_eq_smul_one_tmul` leaves the `AddCommMonoid`
     metavariable unsolved. Route: prove `toRealForm_add` (`TensorProduct.tmul_add`) and
     `toRealForm_zsmul` (`TensorProduct.tmul_smul`) first, then `Finset.cons_induction`, or bundle
     `toRealForm L` as an `AddMonoidHom` and use `map_sum`.
   * `pairing_ne_zero_of_signs` (l.376, 385, 387): `rw [map_sum] at hzero` fails (use
     `simp only [map_sum, map_smul, smul_eq_mul] at hzero`), and `lt_of_le_of_ne (h i₀) (Ne.symm hi₀)`
     must be `lt_of_le_of_ne (h i₀) hi₀`.
   * `isChamberWithWalls_of_signs` (l.413): `absurd hs.2 (lt_irrefl 0)` — `s = 0` makes the goal
     `¬ (pairing 0 0 < 0)`; use `simpa using hs.2` after `rw [h0] at hs`.
2. **Step 2, `e10_reflective_norm`** — not yet written. The proof route (checked on paper, uses only
   facts now in the tree): let `v = Σ bᵢ αᵢ` be a reflective root with `(v,v) < 0` and
   `n = quadC b` (so `(v,v) = -2n`, `n > 0`, `n` even). `IsReflectiveRoot` is
   `LinearMap.IsReflective`, i.e. `(v,v) ∣ 2(v,y)` for every `y ∈ L`. Take `y = y_j`, the lattice
   vector with `(α_k, y_j) = 2 δ_jk`: in the α-basis its coordinates are `-C⁻¹ e_j`, integral by
   `e10Cartan_inverse_mul`. Then `2(v, y_j) = 4 b_j`, so `n ∣ 2 b_j` for every `j`. Define
   `b' := 2 b / n` (integral by that divisibility). Then
   `quadC b' = (4/n²) · quadC b = 4/n`, and `quadC b'` is an even integer (`quadC_even`), so
   `n ∣ 4` and `4/n` is even, so `n ∣ 2`; with `n` even and `n > 0` this gives `n = 2`.
   **No Bézout, no primitivity, no gcd argument is needed** — do not re-derive one.
3. The `IsChamberWithWalls` assembly, which needs the real-form layer: `e10Root_isReflectiveRoot`
   (the lattice is even — `e10BlockGram_even` — so `(r,r) = -4 ∣ 2(r,y)`), the interior point
   `z = (31, 30, -46, -68, -91, -135, -110, -84, -57, -29)` in the block basis, verified numerically
   to pair `2` with each of the ten roots and to have square `2480`, and the criterion
   `isChamberWithWalls_of_signs` fed by `quadC_eq_two_signs` via `e10_reflective_norm`.
4. `coxeterDiagramOfRoots` for the ten roots: `(αᵢ, αⱼ) = -2 C_ij` gives edge weights
   `(2/2)² = 1` on the nine edges and `0` elsewhere, so the diagram is the `E₁₀` diagram.

## LC-09 record (this session)

Corpus queries: `content:PosSemidef submatrix`, `content:Matrix.PosDef.submatrix`,
`content:CartanMatrix E8`, `content:positive semidefinite principal submatrix`,
`content:Vinberg chamber Lorentzian root system`, `content:IsFiniteCartan`; local greps over the
pinned Mathlib for `IsReflective`, `PosSemidef`, `CartanMatrix`, `matrixSignature`, `finSumFinEquiv`.
Hits: Mathlib's `CartanMatrix.E n` (`Mathlib/LinearAlgebra/Matrix/Cartan/Basic.lean`, so
`CartanMatrix.E 10` *is* `e10Cartan` up to the node order, with `E_det`, `E_off_diag_nonpos`,
`isSimplyLaced_E`) and `Matrix.IsFiniteCartan` (`exists_posDef`, `det_pos`, `transpose`); TauCeti's
`Matrix.IsFiniteCartan.toSymmetrizableDatum` and `posDef_symmetrizedMatrix_toSymmetrizableDatum`;
Atlas's `Matrix.PosDef.submatrix_of_injective`. Nothing supplies positive **semi**definiteness for a
diagram of affine or indefinite type, and nothing supplies a null-vector statement, so the
certificates are proved directly by `ring`. Nothing is ported.
