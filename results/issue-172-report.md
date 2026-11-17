# #172 — transfer of an ambient orbit count to a fibre's traces

Everything below is in `LeanCategories/Lattices/Valued/AmbientTraceTransfer.lean`, imported from
`LeanCategories/All.lean`. No hypothesis of #167's code was touched.

## 1. The proposition, with every hypothesis named

Declaration: `LeanCategories.Lattices.Valued.ambientWallTrace_mem_orbitFamily`.

```lean
theorem ambientWallTrace_mem_orbitFamily
    (hBQ : ∀ u w : V, (associated Q) (rationalPoint u) (rationalPoint w) = (BQ u w : ℝ))
    (hBsym : BQ.IsSymm) (F : ConicalLine BQ Q)
    (Γ : Set (V ≃ₗ[ℚ] V)) (ΓI : Set (↥F.space ≃ₗ[ℚ] ↥F.space))
    (hΓiso : ∀ g ∈ Γ, ∀ x y : V, BQ (g x) (g y) = BQ x y)
    (hΓIiso : ∀ e ∈ ΓI, ∀ x y : ↥F.space,
      restrictBilinForm BQ F.space (e x) (e y) = restrictBilinForm BQ F.space x y)
    {v₀ : V} (hwall₀ : BQ v₀ F.gen = 0) (_hπ₀ : fibreCarrierProj hBsym F v₀ ≠ 0)
    (hTrans : ∀ h : ↥F.space, h ≠ 0 →
      fibreForm Q F.space (rationalPoint h) =
        fibreForm Q F.space (rationalPoint (fibreCarrierProj hBsym F v₀)) →
      ∃ e ∈ ΓI, ∃ c : ℚ, c ≠ 0 ∧ h = c • e (fibreCarrierProj hBsym F v₀))
    {g : V ≃ₗ[ℚ] V} (hg : g ∈ Γ) (hwall : BQ (g v₀) F.gen = 0)
    (hπg : fibreCarrierProj hBsym F (g v₀) ≠ 0) :
    LinearMap.ker (restrictBilinForm BQ F.space (fibreCarrierProj hBsym F (g v₀))) ∈
      orbitFamily ({LinearMap.ker (restrictBilinForm BQ F.space
        (fibreCarrierProj hBsym F v₀))} : Finset (Submodule ℚ ↥F.space)) ΓI
```

The hypotheses, in words:

| name | content |
| --- | --- |
| `hBQ`, `hBsym` | the ambient quadratic form `Q` polarises to `BQ`, and `BQ` is symmetric |
| `F` | the `ℚ`-isotropic line `I = ℚ F.gen`, its hyperbolic partner, its sheet; the fibre `I^⊥/I` is the carrier `F.space = planeComplement BQ F.gen F.partner`, and `π := fibreCarrierProj hBsym F` is `I^⊥ → I^⊥/I` in that model |
| `Γ`, `hΓiso` | a set of **isometries** of `V` — the ambient group whose orbits the arrangement hypothesis of the source is stated on |
| `ΓI`, `hΓIiso` | a set of **isometries of the fibre**; in the intended reading the image `Γ̄_I` of `Stab_Γ(I)` (`fibreInducedEquiv`) |
| `v₀`, `hwall₀` | the wall `H₀ = ker (BQ v₀)` passes through `I` (`v₀ ∈ I^⊥`) |
| `_hπ₀` | `H₀ ≠ I^⊥`, i.e. its trace is a genuine hyperplane of the fibre (this makes `hTrans` satisfiable; it is not used in the proof) |
| `hTrans` | **the fibre-transitivity hypothesis**: every nonzero fibre vector whose fibre value equals that of `π v₀` is a nonzero multiple of a `Γ_I`-image of `π v₀` |
| `hg`, `hwall`, `hπg` | `g ∈ Γ`; the wall `gH₀` passes through `I`; `gH₀ ≠ I^⊥` |

The conclusion: the trace of `gH₀` at `I` — `fibreTrace_eq_ker_restrictBilinForm_proj` already in
`FibreArithmetic.lean` — lies in the `Γ_I`-orbit family of the **single** fibre hyperplane
`ker (restrictBilinForm BQ F.space (π v₀))`. The `Finset` has one element: no count on the ambient
index set appears, and the statement is about traces of walls through `I` only.

### What makes it work

Two lemmas plus two kernel computations:

* `fibreForm_fibreCarrierProj_of_gen_perp`: for a wall normal `v ∈ I^⊥`,
  `q_F(π v) = q(v)` (ambient value). Hence for `g` an isometry and `gH₀` a wall through `I`,
  `q_F(π (g v₀)) = q(g v₀) = q(v₀) = q_F(π v₀)`: **every wall of the orbit has a trace normal of
  the same fibre value.** No statement about `Γ_I`'s action on the ambient walls is used.
* `ker_restrictBilinForm_smul`, `ker_restrictBilinForm_map`: rescaling a normal does not move its
  zero set, and an isometry of the fibre carries the zero set of `w` to that of `e w`.
* `hTrans` finishes.

**The candidate hypothesis is not what makes the proof work.** Transitivity of `Γ_I` on the walls
through `I` inside one `Γ`-orbit is neither used nor needed. The hypothesis that does the work is
fibre-internal: transitivity of the *isometries of the fibre* on the norm level set of `π v₀`. The
`x² − 2y² = 1` phenomenon is real — an orbit of walls can meet one fibre infinitely often — but it
only repeats traces, and the count of #167 is duplicate-insensitive.

## 2. Verdict on `U ⊕ U`: TRUE, one orbit

`twoHyperbolicPlanes_hTrans` and `twoHyperbolicPlanes_ambientWallTrace_mem_orbitFamily`, with
`V = Fin 4 → ℚ`, `uuForm x y = x₀y₁ + x₁y₀ + x₂y₃ + x₃y₂` (the rational form of the repository's
`twoHyperbolicPlanes`, `CuspWorkedInstance.lean:633`), `I = ℚ e₀`, partner `e₁`, fibre
`⟨e₂, e₃⟩ ≅ ℚ²` (`uuFibreEquiv`), and `Γ` **any** set of isometries.

For **every** wall normal `v₀` through `I` with `π v₀ ≠ 0`, `hTrans` holds with `ΓI` the set of all
isometries of the restricted form. So the traces of the walls of any `Γ`-orbit through `I` are a
**single** `Γ_I`-orbit of fibre hyperplanes.

The one mathematical ingredient beyond the general theorem is `hp_exists_isometry`: two nonzero
vectors of a hyperbolic plane with equal value are related by an isometry and a nonzero scalar —
explicitly `diag(u₀/u₀')` when both coordinates are nonzero, the swap when one is, and the identity
`/` swap when `u₀` is isotropic. Consequently the trace set of the orbit is exactly

* the two isotropic lines `⟨e₂⟩`, `⟨f₂⟩` when the wall normal is isotropic (`q_F(π v₀) = 0`), or
* the whole class `{⟨h⟩ : q_F(h) = q_F(π v₀)}` (a hyperbola of lines) otherwise,

and in both cases one orbit.

No `exists_isometry_apply_eq` and no arithmeticity was used. This is *not* a use of the point
transitivity of `O(L)` on primitive isotropic vectors: the ambient orbit enters only through "`g`
is an isometry", which is what fixes the norm.

## 3. Does the argument use anything special to `U ⊕ U`?

Yes: **the rank** — the fibre is a plane. Then the trace is a *line* of `I^⊥/I`, and a line of a
hyperbolic plane is determined up to isometry by its value alone, so the level set is one orbit and,
with an integral structure, finitely many lattice lines.

In the source's rank the trace `L = (H ∩ I^⊥)/I` is a hyperplane of dimension `≥ 2` of `I^⊥/I`, and
the same determinant computation gives only one invariant:

> if `H ⊂ V` is a hyperplane containing the isotropic line `I` and `L = (H ∩ I^⊥)/I`, then
> `det(q|_H) ≡ ± disc(L)` modulo squares

(with `dim L = 1`, `disc(L)` *is* the value, which is why the plane case closes). For `dim L ≥ 2` the
discriminant is one invariant among several, so the traces are **not** one `O(I^⊥/I)`-orbit, and the
transitivity statement needed is not the fibre's; it becomes the arithmetic statement that a lattice
has finitely many orbits on the level set of a fixed norm, i.e. finiteness of the double cosets
`Γ_I \ O(I^⊥/I) / Stab(L₀)` — Borel–Harish-Chandra / class-number finiteness. That is not in the
tree.

(Over the full rational orthogonal group the transitivity itself survives in every rank — Witt's
extension theorem on 1-dimensional subspaces — but the consumer's `Γ_I` is arithmetic, and it is
exactly the passage from `O` to `Γ_I` that the rank decides.)

## 4. Consequence for #167

* **On `U ⊕ U` the hypothesis `hsub` is derived.** Not only is the trace set one orbit: for the
  integral lattice the trace normal `π (g v₀)` is a *lattice* vector of `Λ_red = (Λ ∩ I^⊥)/(Λ ∩ I)`
  of the fixed norm `q(v₀)` (`π v = v − ⟨partner, v⟩ gen` and all pairings are integral), so the
  trace set of the whole orbit is **finite** — `ab = q(v₀)/2` has finitely many integer solutions,
  and the isotropic case gives the two lines `⟨e₂⟩, ⟨f₂⟩`. `hsub` therefore holds with the trace set
  itself as the finite `H₀`. *(This last paragraph is a hand computation; what is formalized is the
  one-orbit statement with `ΓI` the fibre's isometry group.)*
* **For `I_{2,9}` the hypothesis is not derived, and `I_{2,9}` is not a second instance of this
  proof.** The argument transfers verbatim up to "all traces have the same discriminant" and then
  stops; the remaining finiteness is the genus statement above, which the tree does not contain.
  `hsub` is therefore a hypothesis the source's configuration does not supply *in this repository* —
  not refuted, undischarged. What would be needed to discharge it: finiteness of `Γ_I`-orbits on the
  norm level set of the reduced lattice at the fibre of `I` (equivalently, of the double cosets), of
  which the plane case is the degenerate instance that the determinant identity settles.

## Searches recorded (LC-09)

Corpus (`scripts/formalization_corpus.py search`), and Mathlib source on disk at
`/opt/mathlib/Mathlib`:

* `Witt's theorem extension isometry subspace` — corpus hit `facebookresearch__atlas-lean`
  (`WittTheorem`, `WittExtensionProof`, `IsometryExtensionLemma`); the extension theorem exists in
  the corpus, **not** in this tree, and the transfer as formalized does not need it (traces are
  compared inside the fibre, not by extending an ambient isometry to the hyperplanes through `I`).
* `orbit of hyperplanes stabilizer transitivity`, `trace of a hyperplane at an isotropic fibre` — no
  relevant hit.
* Mathlib: `Submodule.map_equiv_eq_comap_symm` (used only to see the shape; the kernel lemma is
  proved directly), `LinearMap.BilinMap.toQuadraticMap`, `LinearMap.mk₂` (form of the worked
  instance), `LinearEquiv.trans_apply`, `Matrix.cons_val_*` (`![…]` coordinates).

## Verification

* `lake build LeanCategories.Lattices.Valued.AmbientTraceTransfer` — builds, no warnings from this
  file (also under `-DrelaxedAutoImplicit=false -Dweak.linter.mathlibStandardSet=true`).
* `#print axioms` on `fibreForm_fibreCarrierProj_of_gen_perp`, `ambientWallTrace_mem_orbitFamily`,
  `hp_exists_isometry`, `twoHyperbolicPlanes_hTrans`,
  `twoHyperbolicPlanes_ambientWallTrace_mem_orbitFamily`: each is exactly
  `[propext, Classical.choice, Quot.sound]`.
* No `sorry`, no `native_decide`, no new axiom in the file.
* **Not run:** `just test` (the full gate builds the whole library; the tree's oleans for
  `Semifan`, `SemifanArrangement`, `ConicalLocus` and `ConicalMember` were absent at the start of
  this turn and the full closure was not rebuilt). The whole-library steps
  (`_lean-vacuity-audit`, `_lean-mathlib-lint-audit`, `_lean-axiom-audit`) are therefore still owed
  on this change.
