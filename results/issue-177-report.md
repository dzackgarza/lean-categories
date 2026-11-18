# Issue #177 — `E-HAT-3.A-6` at a finitely generated stage

Certificates added in `LeanCategories/Homological/TorFiniteStage.lean` (new module, imported from
`LeanCategories/All.lean`).  Build: `lake build LeanCategories.Homological.TorFiniteStage` —
`Build completed successfully (5151 jobs)`.

## Acceptance, item by item

### 1. The statement proved for a finitely generated stage, no `sorryAx`

Landed, three layers:

* `LeanCategories/Homological/TorFiniteStage.lean:71` — `exists_fin_free_presentation`:
  a finitely generated `ℤ`-module is a quotient of `ℤ ^ n`.
  **Statement.** `[AddCommGroup A] [Module ℤ A] [Module.Finite ℤ A] → ∃ (n : ℕ) (f : (Fin n → ℤ) →ₗ[ℤ] A), Function.Surjective f`
* `LeanCategories/Homological/TorFiniteStage.lean:84` — `exists_fin_free_presentation_fg`:
  the same presentation with a finitely generated syzygy (`TorFreeResolution.syzygy_finite`), i.e. the
  two-term resolution `0 → ker f → ℤ ^ n → A → 0` inside finitely generated modules.
* `LeanCategories/Homological/TorFiniteStage.lean:102` — `isAddTorsion_ker_stage`,
  **the torsion statement at a finitely generated stage**: for `F` free with basis `b`, `F' ≤ F`
  finitely generated and any relation submodule `R`,
  `IsAddTorsion ↥(LinearMap.ker (((R ⊓ F').subtype).rTensor B))`.  The killing integer is the
  Smith-normal-form product of `TorExercise3A6.exists_nsmul_eq_zero_of_stage`; `:113`
  (`exists_nsmul_eq_zero_ker_stage`) is the same content in existential form.
* `LeanCategories/Homological/TorFiniteStage.lean:130` — `isAddTorsion_torOne_of_finiteStage`,
  the card's statement at a finitely generated stage:
  `[AddCommGroup A] [AddCommGroup B] [Module.Finite ℤ A] → IsAddTorsion ↥(TorBridge.torOne (ModuleCat.of ℤ A) (ModuleCat.of ℤ B))`.
  `:136` is the both-variables-finitely-generated form, `:143` the elementwise order form.

No `sorry`, `admit` or `native_decide` occurs in the module.

**How the reduction is licensed.**  new-qual-site#111 records Hatcher §3.A exercise 4 (Tor commuting
with filtered colimits) as absent at the pin, so the card's "directed union of finitely generated
subgroups" step has no colimit comparison behind it.  The resolution alternative the issue accepts is
what is certified: `TorExercise3A6.isAddTorsion_torOne` reduces an element of `Tor₁(A, B)` to a
finitely generated stage by `TorStages.exists_stage_of_free` and kills it there by the Smith normal
form of `exists_nsmul_eq_zero_of_stage` — the same computation `isAddTorsion_ker_stage` states at the
stage.  The card-level statements are that proof restricted to finitely generated `A`; no colimit
comparison and no `CategoryTheory.Tor` comparison API are used.

**Probed and failed (exact failure).** A direct transport of the tensor kernel at a finite free
presentation, so that the card-level statement could be proved without passing through
`isAddTorsion_torOne`, fails on the instance diamond of the subtype carriers:
`.scratch/probe177/Stage.lean:32` — `rw [← LinearMap.rTensor_comp, hcomp]` reports
`Application type mismatch: the argument LinearMap.rTensor B ↑e has type … TensorProduct.instModule …
but is expected to have type` (the `LinearEquiv.ofEq` subtype carries `Submodule.instModule` while the
tensored kernel carries `TensorProduct.instModule` on the `AddCommGroup`-synthesized structure).
That is the `toIntModule`-versus-`instModule` family already logged for `TorBridge.lean:343` and
`TorExercise3A6.kerOf`; the committed proof avoids it by building the stage element with
`LinearMap.codRestrict` (`TorStages.exists_stage_of_free`) instead of an `ofEq` transport.

### 2. `#print axioms` exactly `[propext, Classical.choice, Quot.sound]`

Verified through `lake env lean` on a probe importing the module; all seven declarations print
exactly:

```
'LeanCategories.Homological.TorFiniteStage.exists_fin_free_presentation' depends on axioms: [propext, Classical.choice, Quot.sound]
'LeanCategories.Homological.TorFiniteStage.exists_fin_free_presentation_fg' depends on axioms: [propext, Classical.choice, Quot.sound]
'LeanCategories.Homological.TorFiniteStage.isAddTorsion_ker_stage' depends on axioms: [propext, Classical.choice, Quot.sound]
'LeanCategories.Homological.TorFiniteStage.exists_nsmul_eq_zero_ker_stage' depends on axioms: [propext, Classical.choice, Quot.sound]
'LeanCategories.Homological.TorFiniteStage.isAddTorsion_torOne_of_finiteStage' depends on axioms: [propext, Classical.choice, Quot.sound]
'LeanCategories.Homological.TorFiniteStage.isAddTorsion_torOne_of_finiteStage_fg' depends on axioms: [propext, Classical.choice, Quot.sound]
'LeanCategories.Homological.TorFiniteStage.exists_addOrderOf_pos_torOne_of_finiteStage' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The pre-existing `E-HAT-3.A-6` declarations on `main` were checked in the same session and carry the
same three axioms: `TorExercise3A6.isAddTorsion_torOne`, `torOne_prime_pow_iff`,
`torOne_exists_addOrderOf_iff`, `exists_fg_stage`, `exists_nsmul_eq_zero_of_stage`, and
`TorFreeResolution.isZero_torOne_of_finite_torsionFree`.

### 3. The card linking the declaration by name

**Not done in this session.**  The GitHub connector available here is scoped to
`dzackgarza/lean-categories` (one connected repository), so `new-qual-site` card
`E-HAT-3.A-6` could not be edited.  The link the card needs, by declaration name:

```
Tor₁(A,B) is a torsion group for finitely generated A:
lean-categories `LeanCategories/Homological/TorFiniteStage.lean:130`
`LeanCategories.Homological.TorFiniteStage.isAddTorsion_torOne_of_finiteStage`
(TorExercise3A6.isAddTorsion_torOne restricted to `Module.Finite ℤ A`; axioms
[propext, Classical.choice, Quot.sound], no sorryAx)

the stage computation it rests on:
`LeanCategories.Homological.TorFiniteStage.isAddTorsion_ker_stage` (`:102`)
`LeanCategories.Homological.TorExercise3A6.exists_nsmul_eq_zero_of_stage`
```

## Notes on the checkout

`LeanCategories/All.lean` already carried the import line
`public import LeanCategories.Homological.TorFiniteStage` when this module was committed: the shared
checkout's other session swept the in-flight line into `67a530c1` and pushed it, so `main` imported a
module that did not yet exist until this push landed the file.  Nothing else of that session's work is
included in this commit.
