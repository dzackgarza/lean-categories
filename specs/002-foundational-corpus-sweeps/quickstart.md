# Quickstart: validate the corpus programme

Run from the repository root on the research image. Before any Lean process,
`pgrep -a -x 'lean|lake'` prints nothing (constitution E10).

## 1. The record regenerates (US2)

```bash
just foundational-frontier
python3 scripts/foundational_definition_index.py
```

Expected: both exit 0. At `fc549baa` the first fails on the three rows of
[units.md](units.md#scheduler-defects); task T001 repairs them.

## 2. A unit resolves to its declaration (US1)

```bash
grep -P '^FC06-C02-U231\t' FOUNDATIONAL_DEFINITIONS.tsv | cut -f1,7,8,11
grep -h '^| `FC06-C02-U231`' corpus/chapter-2-schemes-fc06.md
```

Expected after T031: the row carries `[realized]` and names the constructing declaration in
`LeanCategories/Schemes/RelativeProjData.lean`; the index gives route `unmatched` and action
`reuse`.

## 3. No stub remains (US1)

```bash
python3 scripts/stub_population.py
```

Expected after Phase 3: no output on standard output and `0 open` on standard error.

## 4. A definition agrees with its source (US3)

Open the source clause through the library item key of the manifest (T002), the mapping row and
the declaration. Apply plan.md Contract R. Expected: the recorded comparison agrees with the
reviewer's comparison.

## 5. The full gate (milestones)

```bash
just test
```

Expected: build, `lean-no-sorry`, vacuity audit, Mathlib lint audit, unused-variable check and
axiom audit pass. The axiom audit admits only `propext`, `Classical.choice` and `Quot.sound`.
