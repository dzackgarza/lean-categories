# Quickstart: validate the abelian projectivity feature

Run from the repository root on the research image; `pgrep -a -x 'lean|lake'` prints nothing first.

## 1. The final theorem

After T009, elaborate the module of the final theorem with `just loop <module>` (feature 001
T001). Expected: exit 0; `#print axioms` of the final theorem lists only `propext`,
`Classical.choice` and `Quot.sound`; its hypotheses are a `ComplexTorus` with `IsAbelianVariety`.

## 2. A principal polarization

For an elliptic curve $\mathbb C/(\mathbb Z + \tau\mathbb Z)$ with its principal polarization, the
theorems of T006 and T007 give $h^0(L) = 1$ and an embedding into $\mathbb P^2$ by $L^{\otimes 3}$.

## 3. The milestone gate

`just test` passes on the milestone revision.
