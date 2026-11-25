# Quickstart: validate scheme and stack geometry

Run from the repository root on the research image; `pgrep -a -x 'lean|lake'` prints nothing first.

## 1. Universal properties (US1)

After T006 and T007, elaborate `LeanCategories/AlgebraicGeometry/Blowup.lean` and
`Covers.lean` with `flock .tmp/lean.lock lake env lean <module>`. Expected: exit 0; the universal
property of the blowup of $\mathbb A^2_k$ at the origin is a theorem.

## 2. Stack conditions (US2, US3, US4)

After T010, T015 and T018, the stack conditions of $BG$, $[X/G]$, the KSBA fibred category and
$\overline{\mathcal M}_{g,n}$ are theorems; `#print axioms` lists only `propext`,
`Classical.choice` and `Quot.sound`.

## 3. Invalid placements

A coarse moduli space is not a variety by construction; a stack is not Deligne–Mumford by
construction; a pair that is not slc is not stable. Each is a test of the module that owns it.

## 4. The milestone gate

`just test` passes on the milestone revision.
