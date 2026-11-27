# Quickstart: validate manifolds, Hodge theory and period constructions

Run from the repository root on the research image; `pgrep -a -x 'lean|lake'` prints nothing first.

## 1. The period domain and its quotient (US1)

After T003, elaborate `LeanCategories/Analytic/ArithmeticQuotient.lean` with
`just loop <module>` (feature 001 T001). Expected: exit 0; for $T = U \perp U$ a component of
$\Omega_T$ is biholomorphic to $\mathbb H \times \mathbb H$; a stabilizer survives in the stack.

## 2. The period map (US2)

After T007, the period map of a pulled-back family equals the composite with the base map;
`#print axioms` lists only `propext`, `Classical.choice` and `Quot.sound`.

## 3. Lattices of a surface (US5)

After T014 and T015, $\mathbb P^1 \times \mathbb P^1$ gives $U$, $\operatorname{Bl}_k \mathbb P^2$
gives $I_{1,k}$, and the rational elliptic surface gives the Mordell–Weil lattice $E_8(-1)$.

## 4. The milestone gate

`just test` passes on the milestone revision.
