# Quickstart: validate reflection, fan and toric geometry

Run from the repository root on the research image; `pgrep -a -x 'lean|lake'` prints nothing first.

## 1. The folding theorem (US1)

After T003, elaborate `LeanCategories/Lattices/Valued/FoldingAEGSExample.lean` with
`flock .tmp/lean.lock lake env lean <module>`. Expected: exit 0; the folded roots and diagram are
those of the source; `#print axioms` lists only `propext`, `Classical.choice` and `Quot.sound`.

## 2. Vinberg's algorithm (US2)

After T004, `Lattices/Valued/VinbergAlgorithmTests.lean` returns the $E_{10}$ chamber with its
proof and `none` at a bound that is too small.

## 3. The toric functor (US4)

After T010, the fan of $\mathbb P^2$ gives $\mathbb P^2_k$, and a fan morphism gives a toric
morphism with the identity and composition laws.

## 4. The milestone gate

`just test` passes on the milestone revision.
