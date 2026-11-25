# Quickstart: validate the arithmetic lattice feature

Run from the repository root on the research image. Before any Lean process,
`pgrep -a -x 'lean|lake'` prints nothing (constitution E10).

## 1. An owner row is closed (US1–US4)

Take a row of [data-model.md](data-model.md). Open its owner module and the comparison theorems that
the closing task names in its commit. Elaborate the owner and its test module:

```bash
flock .tmp/lean.lock lake env lean LeanCategories/Lattices/Valued/IdealDual.lean
```

Expected: exit 0; each specialization of the row is identified with the owner by a named theorem;
`#print axioms` on each theorem lists only `propext`, `Classical.choice` and `Quot.sound`.

## 2. The genus is ring-adelic (US2)

After T023, the integer genus statement is the theorem `sameGenus_iff_sameAdeleGenus` about the
ring-adelic owner of `Lattices/Valued/Adele.lean`, and no definition `SameGenus` remains.

## 3. The named lattices follow the sign convention (US4)

After T034, `Λ_K3` is built as `U^{⊥3} ⊥ E8^{⊥2}` from the generic operations, and its signature
`(3, 19)` and evenness follow from generic theorems.

## 4. The phase gate

```bash
just test
```

Expected: build, `lean-no-sorry`, vacuity audit, Mathlib lint audit, unused-variable check and axiom
audit pass.
