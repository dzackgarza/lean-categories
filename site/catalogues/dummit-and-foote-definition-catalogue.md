---
title: "Dummit and Foote definition catalogue"
---

Title: *Abstract Algebra*, third edition

Authors: David S. Dummit and Richard M. Foote

Zotero key: `A4FFDNKB`

Citekey: `DF04`

Source attachment: ``local-write-api-1783380265761-A4FFDNKB_extracted.md``

## Preliminary chapter

- [x] Set — §0.1, Basics, p. 1
  - Mathlib: `Set` — [`Mathlib/Data/Set/Defs.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Set/Defs.html)
- [x] Function — §0.1, Basics, p. 1
  - Mathlib: `Function` — [`Mathlib/Logic/Function/Basic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Logic/Function/Basic.html)
- [x] Equivalence relation — §0.1, Basics, p. 1
  - Mathlib: `Equivalence` — [`Mathlib/Logic/Relation.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Logic/Relation.html)
- [x] Partition — §0.1, Basics, p. 1
  - Mathlib: [`Setoid.IsPartition`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Setoid.IsPartition#doc) — [`Mathlib/Data/Setoid/Partition.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Setoid/Partition.html)
- [x] Divisibility — §0.2, Properties of the Integers, p. 4
  - Mathlib: [`Dvd.dvd`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Dvd.dvd#doc) — `Init/Prelude.lean:1560` (Lean core, not Mathlib)
- [x] Greatest common divisor — §0.2, Properties of the Integers, p. 4
  - Mathlib: `gcd` — [`Mathlib/Data/Nat/GCD/Basic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Nat/GCD/Basic.html)
- [x] Congruence modulo n — §0.3, Z/nZ: The Integers Modulo n, p. 8
  - Mathlib: [`Nat.ModEq`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Nat.ModEq#doc) — [`Mathlib/Data/Nat/ModEq.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Nat/ModEq.html)
- [x] Residue class — §0.3, Z/nZ: The Integers Modulo n, p. 8
  - Mathlib: `ZMod` — [`Mathlib/Data/ZMod/Basic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/ZMod/Basic.html)

## Chapter 1: Introduction to Groups

- [x] Binary operation — §1.1, Basic Axioms and Examples, p. 16
  - Mathlib: `Mul` — [`Mathlib/Algebra/Group/Defs.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Group/Defs.html)
- [x] Group — §1.1, Basic Axioms and Examples, p. 16
  - Mathlib: `Group` — [`Mathlib/Algebra/Group/Defs.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Group/Defs.html)
- [x] Abelian group — §1.1, Basic Axioms and Examples, p. 16
  - Mathlib: `CommGroup` — [`Mathlib/Algebra/Group/Defs.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Group/Defs.html)
- [x] Order of a group — §1.1, Basic Axioms and Examples, p. 16
  - Mathlib: [`Nat.card`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Nat.card#doc) — [`Mathlib/SetTheory/Cardinal/Finite.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/SetTheory/Cardinal/Finite.html)
- [x] Order of an element — §1.1, Basic Axioms and Examples, p. 16
  - Mathlib: `orderOf` — [`Mathlib/GroupTheory/OrderOfElement.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/GroupTheory/OrderOfElement.html)
- [x] Dihedral group — §1.2, Dihedral Groups, p. 23
  - Mathlib: `DihedralGroup` — [`Mathlib/GroupTheory/SpecificGroups/Dihedral.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/GroupTheory/SpecificGroups/Dihedral.html)
- [x] Symmetric group — §1.3, Symmetric Groups, p. 29
  - Mathlib: [`Equiv.Perm`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Equiv.Perm#doc) — [`Mathlib/GroupTheory/Perm/Basic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/GroupTheory/Perm/Basic.html)
- [x] Permutation — §1.3, Symmetric Groups, p. 29
  - Mathlib: [`Equiv.Perm`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Equiv.Perm#doc) — [`Mathlib/GroupTheory/Perm/Basic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/GroupTheory/Perm/Basic.html)
- [x] General linear group — §1.4, Matrix Groups, p. 34
  - Mathlib: `GL` — `Mathlib/LinearAlgebra/Matrix/GeneralLinearGroup/Defs.lean:47`
- [x] Quaternion group — §1.5, The Quaternion Group, p. 36
  - Mathlib: `QuaternionGroup` — [`Mathlib/GroupTheory/SpecificGroups/Quaternion.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/GroupTheory/SpecificGroups/Quaternion.html)
- [x] Group homomorphism — §1.6, Homomorphisms and Isomorphisms, p. 36
  - Mathlib: `MonoidHom` — [`Mathlib/Algebra/Group/Hom/Defs.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Group/Hom/Defs.html)
- [x] Group isomorphism — §1.6, Homomorphisms and Isomorphisms, p. 36
  - Mathlib: `MulEquiv` — [`Mathlib/Algebra/Group/Equiv/Defs.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Group/Equiv/Defs.html)
- [x] Group action — §1.7, Group Actions, p. 41
  - Mathlib: `MulAction` — [`Mathlib/GroupTheory/GroupAction/Defs.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/GroupTheory/GroupAction/Defs.html)
- [x] Permutation representation — §1.7, Group Actions, p. 41
  - Mathlib: [`MulAction.toPerm`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=MulAction.toPerm#doc) — [`Mathlib/GroupTheory/GroupAction/Basic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/GroupTheory/GroupAction/Basic.html)

## Chapter 2: Subgroups

- [x] Subgroup — §2.1, Definition and Examples, p. 46
  - Mathlib: `Subgroup` — [`Mathlib/Algebra/Group/Subgroup/Defs.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Group/Subgroup/Defs.html)
- [x] Centralizer — §2.2, Centralizers and Normalizers, Stabilizers and Kernels, p. 49
  - Mathlib: [`Subgroup.centralizer`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Subgroup.centralizer#doc) — [`Mathlib/GroupTheory/Subgroup/Centralizer.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/GroupTheory/Subgroup/Centralizer.html)
- [x] Normalizer — §2.2, Centralizers and Normalizers, Stabilizers and Kernels, p. 49
  - Mathlib: [`Subgroup.normalizer`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Subgroup.normalizer#doc) — [`Mathlib/Algebra/Group/Subgroup/Defs.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Group/Subgroup/Defs.html)
- [x] Stabilizer — §2.2, Centralizers and Normalizers, Stabilizers and Kernels, p. 49
  - Mathlib: [`MulAction.stabilizer`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=MulAction.stabilizer#doc) — [`Mathlib/GroupTheory/GroupAction/Defs.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/GroupTheory/GroupAction/Defs.html)
- [x] Kernel of an action — §2.2, Centralizers and Normalizers, Stabilizers and Kernels, p. 49
  - Mathlib: [`MulAction.ker`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=MulAction.ker#doc) — [`Mathlib/GroupTheory/GroupAction/Defs.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/GroupTheory/GroupAction/Defs.html)
- [x] Cyclic group — §2.3, Cyclic Groups and Cyclic Subgroups, p. 54
  - Mathlib: [`Subgroup.zpowers`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Subgroup.zpowers#doc) — `Mathlib/Algebra/Group/Subgroup/ZPowers/Basic.lean:30`
- [x] Generated subgroup — §2.4, Subgroups Generated by Subsets of a Group, p. 61
  - Mathlib: [`Subgroup.closure`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Subgroup.closure#doc) — `Mathlib/Algebra/Group/Subgroup/Lattice.lean:329`
- [x] Subgroup lattice — §2.5, The Lattice of Subgroups of a Group, p. 66
  - Mathlib: `Subgroup` — [`Mathlib/Algebra/Group/Subgroup/Lattice.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Group/Subgroup/Lattice.html)

## Chapter 3: Quotient Groups and Homomorphisms

- [x] Left coset — §3.1, Definitions and Examples, p. 73
  - Mathlib: `LeftCosetEquivalence` — [`Mathlib/GroupTheory/Coset/Basic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/GroupTheory/Coset/Basic.html)
- [x] Right coset — §3.1, Definitions and Examples, p. 73
  - Mathlib: `RightCosetEquivalence` — [`Mathlib/GroupTheory/Coset/Basic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/GroupTheory/Coset/Basic.html)
- [x] Normal subgroup — §3.1, Definitions and Examples, p. 73
  - Mathlib: [`Subgroup.Normal`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Subgroup.Normal#doc) — `Mathlib/Algebra/Group/Subgroup/Defs.lean:605`
- [x] Quotient group — §3.1, Definitions and Examples, p. 73
  - Mathlib: `QuotientGroup` — [`Mathlib/GroupTheory/QuotientGroup/Defs.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/GroupTheory/QuotientGroup/Defs.html)
- [x] Index of a subgroup — §3.2, More on Cosets and Lagrange's Theorem, p. 89
  - Mathlib: [`Subgroup.index`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Subgroup.index#doc) — [`Mathlib/GroupTheory/Index.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/GroupTheory/Index.html)
- [x] Composition series — §3.4, Composition Series and the Holder Program, p. 101
  - Mathlib: `CompositionSeries` — `Mathlib/Order/JordanHolder.lean:137`
- [x] Simple group — §3.4, Composition Series and the Holder Program, p. 101
  - Mathlib: `IsSimpleGroup` — `Mathlib/GroupTheory/Subgroup/Simple.lean:38`
- [x] Refinement of a composition series — §3.4, Composition Series and the Holder Program, p. 101
  - Mathlib: [`LTSeries.exists_relSeries_covBy`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=LTSeries.exists_relSeries_covBy#doc) — [`Mathlib/Order/RelSeries.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Order/RelSeries.html)
- [x] Transposition — §3.5, Transpositions and the Alternating Group, p. 106
  - Mathlib: [`Equiv.swap`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Equiv.swap#doc) — [`Mathlib/Logic/Equiv/Basic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Logic/Equiv/Basic.html)
- [x] Alternating group — §3.5, Transpositions and the Alternating Group, p. 106
  - Mathlib: `alternatingGroup` — [`Mathlib/GroupTheory/SpecificGroups/Alternating.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/GroupTheory/SpecificGroups/Alternating.html)

## Chapter 4: Group Actions

- [x] Orbit — §4.1, Group Actions and Permutation Representations, p. 112
  - Mathlib: [`MulAction.orbit`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=MulAction.orbit#doc) — [`Mathlib/GroupTheory/GroupAction/Defs.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/GroupTheory/GroupAction/Defs.html)
- [x] Faithful action — §4.1, Group Actions and Permutation Representations, p. 112
  - Mathlib: `FaithfulSMul` — [`Mathlib/GroupTheory/GroupAction/Defs.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/GroupTheory/GroupAction/Defs.html)
- [x] Regular action — §4.2, Groups Acting on Themselves by Left Multiplication, p. 118
  - Mathlib: [`Monoid.toMulAction`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Monoid.toMulAction#doc) — [`Mathlib/Algebra/Group/Action/Defs.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Group/Action/Defs.html)
- [x] Conjugation action — §4.3, Groups Acting on Themselves by Conjugation, p. 122
  - Mathlib: [`MulAction.conj`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=MulAction.conj#doc) — [`Mathlib/GroupTheory/GroupAction/ConjAct.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/GroupTheory/GroupAction/ConjAct.html)
- [x] Conjugacy class — §4.3, Groups Acting on Themselves by Conjugation, p. 122
  - Mathlib: `conjugacyClass` — (no Mathlib declaration; closest: `IsConj` — `Mathlib/Algebra/Group/Conj.lean:32`)
- [x] Automorphism — §4.4, Automorphisms, p. 133
  - Mathlib: `MulAut` — `Mathlib/Algebra/Group/End.lean:631`
- [x] Inner automorphism — §4.4, Automorphisms, p. 133
  - Mathlib: [`MulAut.inner`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=MulAut.inner#doc) — [`Mathlib/GroupTheory/GroupAction/ConjAct.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/GroupTheory/GroupAction/ConjAct.html)
- [x] Outer automorphism group — §4.4, Automorphisms, p. 133
  - LeanCategories: [`LeanCategories.Algebra.outerAutomorphismGroup`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=LeanCategories.Algebra.outerAutomorphismGroup#doc) — [`LeanCategories/Algebra/GroupTheory.lean`](https://github.com/dzackgarza/lean-categories/blob/main/LeanCategories/Algebra/GroupTheory.lean)
- [x] p-subgroup — §4.5, The Sylow Theorems, p. 139
  - Mathlib: `Sylow` — [`Mathlib/GroupTheory/Sylow.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/GroupTheory/Sylow.html)
- [x] Sylow p-subgroup — §4.5, The Sylow Theorems, p. 139
  - Mathlib: `Sylow` — [`Mathlib/GroupTheory/Sylow.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/GroupTheory/Sylow.html)

## Chapter 5: Direct and Semidirect Products and Abelian Groups

- [x] Direct product of groups — §5.1, Direct Products, p. 152
  - Mathlib: `DirectProduct` — (no Mathlib declaration; the product group is `G × H` with [`Prod.instGroup`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Prod.instGroup#doc) — `Mathlib/Algebra/Group/Prod.lean:123`)
- [x] Finitely generated group — §5.2, The Fundamental Theorem of Finitely Generated Abelian Groups, p. 158
  - Mathlib: [`Monoid.FG`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Monoid.FG#doc) — `Mathlib/GroupTheory/Finiteness.lean:160`
- [x] Torsion subgroup — §5.2, The Fundamental Theorem of Finitely Generated Abelian Groups, p. 158
  - Mathlib: `torsion` — [`Mathlib/GroupTheory/Torsion.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/GroupTheory/Torsion.html)
- [x] Invariant factors — §5.2, The Fundamental Theorem of Finitely Generated Abelian Groups, p. 158
  - LeanCategories: [`LeanCategories.Algebra.InvariantFactorData`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=LeanCategories.Algebra.InvariantFactorData#doc) — [`LeanCategories/Algebra/CanonicalForms.lean`](https://github.com/dzackgarza/lean-categories/blob/main/LeanCategories/Algebra/CanonicalForms.lean)
- [x] Elementary divisors — §5.2, The Fundamental Theorem of Finitely Generated Abelian Groups, p. 158
  - Mathlib: [`Module.equiv_directSum_of_isTorsion`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Module.equiv_directSum_of_isTorsion#doc) — [`Mathlib/Algebra/Module/PID.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Module/PID.html)
- [x] Internal direct product — §5.4, Recognizing Direct Products, p. 169
  - Mathlib: [`Subgroup.internalDirectProduct`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Subgroup.internalDirectProduct#doc) — (no Mathlib declaration; closest: [`Subgroup.prod`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Subgroup.prod#doc) — `Mathlib/Algebra/Group/Subgroup/Basic.lean:91`)
- [x] Semidirect product — §5.5, Semidirect Products, p. 175
  - Mathlib: `SemidirectProduct` — [`Mathlib/GroupTheory/SemidirectProduct.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/GroupTheory/SemidirectProduct.html)

## Chapter 6: Further Topics in Group Theory

- [x] p-group — §6.1, p-groups, Nilpotent Groups, and Solvable Groups, p. 188
  - Mathlib: `IsPGroup` — [`Mathlib/GroupTheory/Sylow.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/GroupTheory/Sylow.html)
- [x] Upper central series — §6.1, p-groups, Nilpotent Groups, and Solvable Groups, p. 188
  - Mathlib: `upperCentralSeries` — `Mathlib/GroupTheory/Nilpotent.lean:182`
- [x] Nilpotent group — §6.1, p-groups, Nilpotent Groups, and Solvable Groups, p. 188
  - Mathlib: `IsNilpotent` — [`Mathlib/GroupTheory/Nilpotent.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/GroupTheory/Nilpotent.html)
- [x] Derived series — §6.1, p-groups, Nilpotent Groups, and Solvable Groups, p. 188
  - Mathlib: `derivedSeries` — `Mathlib/GroupTheory/Solvable.lean:43`
- [x] Solvable group — §6.1, p-groups, Nilpotent Groups, and Solvable Groups, p. 188
  - Mathlib: `IsSolvable` — [`Mathlib/GroupTheory/Solvable.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/GroupTheory/Solvable.html)
- [x] Free group — §6.3, A Word on Free Groups, p. 215
  - Mathlib: `FreeGroup` — `Mathlib/GroupTheory/FreeGroup/Basic.lean:471`
- [x] Group presentation — §6.3, A Word on Free Groups, p. 215
  - Mathlib: `PresentedGroup` — [`Mathlib/GroupTheory/PresentedGroup.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/GroupTheory/PresentedGroup.html)

## Chapter 7: Introduction to Rings

- [x] Ring — §7.1, Basic Definitions and Examples, p. 223
  - Mathlib: `Ring` — [`Mathlib/Algebra/Ring/Defs.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Ring/Defs.html)
- [x] Commutative ring — §7.1, Basic Definitions and Examples, p. 223
  - Mathlib: `CommRing` — [`Mathlib/Algebra/Ring/Defs.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Ring/Defs.html)
- [x] Ring with identity — §7.1, Basic Definitions and Examples, p. 223
  - Mathlib: `Ring` — [`Mathlib/Algebra/Ring/Defs.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Ring/Defs.html)
- [x] Unit — §7.1, Basic Definitions and Examples, p. 223
  - Mathlib: `IsUnit` — `Mathlib/Algebra/Group/Units/Defs.lean:364`
- [x] Zero divisor — §7.1, Basic Definitions and Examples, p. 223
  - Mathlib: `notMem_nonZeroDivisors_iff` — [`Mathlib/Algebra/GroupWithZero/NonZeroDivisors.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/GroupWithZero/NonZeroDivisors.html)
- [x] Integral domain — §7.1, Basic Definitions and Examples, p. 223
  - Mathlib: `IsDomain` — `Mathlib/Algebra/Ring/Defs.lean:439`
- [x] Division ring — §7.1, Basic Definitions and Examples, p. 223
  - Mathlib: `DivisionRing` — [`Mathlib/Algebra/Field/Defs.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Field/Defs.html)
- [x] Field — §7.1, Basic Definitions and Examples, p. 223
  - Mathlib: `Field` — [`Mathlib/Algebra/Field/Defs.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Field/Defs.html)
- [x] Subring — §7.1, Basic Definitions and Examples, p. 223
  - Mathlib: `Subring` — [`Mathlib/Algebra/Ring/Subring/Defs.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Ring/Subring/Defs.html)
- [x] Polynomial ring — §7.2, Polynomial Rings, Matrix Rings, and Group Rings, p. 233
  - Mathlib: `Polynomial` — [`Mathlib/Algebra/Polynomial/Basic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Polynomial/Basic.html)
- [x] Matrix ring — §7.2, Polynomial Rings, Matrix Rings, and Group Rings, p. 233
  - Mathlib: `Matrix` — `Mathlib/LinearAlgebra/Matrix/Defs.lean:55`
- [x] Group ring — §7.2, Polynomial Rings, Matrix Rings, and Group Rings, p. 233
  - Mathlib: `MonoidAlgebra` — [`Mathlib/Algebra/MonoidAlgebra/Defs.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/MonoidAlgebra/Defs.html)
- [x] Ring homomorphism — §7.3, Ring Homomorphisms and Quotient Rings, p. 239
  - Mathlib: `RingHom` — [`Mathlib/Algebra/Ring/Hom/Defs.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Ring/Hom/Defs.html)
- [x] Ideal — §7.3, Ring Homomorphisms and Quotient Rings, p. 239
  - Mathlib: `Ideal` — [`Mathlib/RingTheory/Ideal/Defs.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/Ideal/Defs.html)
- [x] Quotient ring — §7.3, Ring Homomorphisms and Quotient Rings, p. 239
  - Mathlib: [`Ideal.Quotient`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Ideal.Quotient#doc) — `Mathlib/RingTheory/Ideal/Quotient/Defs.lean:43`
- [x] Prime ideal — §7.4, Properties of Ideals, p. 251
  - Mathlib: [`Ideal.IsPrime`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Ideal.IsPrime#doc) — [`Mathlib/RingTheory/Ideal/Prime.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/Ideal/Prime.html)
- [x] Maximal ideal — §7.4, Properties of Ideals, p. 251
  - Mathlib: [`Ideal.IsMaximal`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Ideal.IsMaximal#doc) — [`Mathlib/RingTheory/Ideal/Operations.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/Ideal/Operations.html)
- [x] Ring of fractions — §7.5, Rings of Fractions, p. 260
  - Mathlib: `Localization` — [`Mathlib/RingTheory/Localization/Basic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/Localization/Basic.html)

## Chapter 8: Euclidean Domains, Principal Ideal Domains and Unique Factorization Domains

- [x] Norm on an integral domain — §8.1, Euclidean Domains, p. 270
  - Mathlib: [`EuclideanDomain.norm`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=EuclideanDomain.norm#doc) — [`Mathlib/RingTheory/EuclideanDomain.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/EuclideanDomain.html)
- [x] Euclidean domain — §8.1, Euclidean Domains, p. 270
  - Mathlib: `EuclideanDomain` — [`Mathlib/RingTheory/EuclideanDomain.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/EuclideanDomain.html)
- [x] Principal ideal domain — §8.2, Principal Ideal Domains, p. 279
  - Mathlib: `IsPrincipalIdealRing` — [`Mathlib/RingTheory/PrincipalIdealDomain.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/PrincipalIdealDomain.html)
- [x] Irreducible element — §8.3, Unique Factorization Domains, p. 283
  - Mathlib: `Irreducible` — [`Mathlib/RingTheory/UniqueFactorizationDomain/Basic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/UniqueFactorizationDomain/Basic.html)
- [x] Prime element — §8.3, Unique Factorization Domains, p. 283
  - Mathlib: `Prime` — [`Mathlib/RingTheory/UniqueFactorizationDomain/Basic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/UniqueFactorizationDomain/Basic.html)
- [x] Unique factorization domain — §8.3, Unique Factorization Domains, p. 283
  - Mathlib: `UniqueFactorizationMonoid` — [`Mathlib/RingTheory/UniqueFactorizationDomain/Basic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/UniqueFactorizationDomain/Basic.html)

## Chapter 9: Polynomial Rings

- [x] Polynomial — §9.1, Definitions and Basic Properties, p. 295
  - Mathlib: `Polynomial` — [`Mathlib/Algebra/Polynomial/Basic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Polynomial/Basic.html)
- [x] Degree of a polynomial — §9.1, Definitions and Basic Properties, p. 295
  - Mathlib: [`Polynomial.degree`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Polynomial.degree#doc) — [`Mathlib/Algebra/Polynomial/Degree/Definitions.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Polynomial/Degree/Definitions.html)
- [x] Polynomial evaluation homomorphism — §9.1, Definitions and Basic Properties, p. 295
  - Mathlib: `Polynomial.eval₂RingHom` — [`Mathlib/Algebra/Polynomial/Eval/Defs.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Polynomial/Eval/Defs.html)
- [x] Content of a polynomial — §9.3, Polynomial Rings that are Unique Factorization Domains, p. 303
  - Mathlib: [`Polynomial.content`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Polynomial.content#doc) — `Mathlib/RingTheory/Polynomial/Content.lean:90`
- [x] Primitive polynomial — §9.3, Polynomial Rings that are Unique Factorization Domains, p. 303
  - Mathlib: [`Polynomial.IsPrimitive`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Polynomial.IsPrimitive#doc) — `Mathlib/RingTheory/Polynomial/Content.lean:45`
- [x] Eisenstein polynomial — §9.4, Irreducibility Criteria, p. 307
  - Mathlib: [`Polynomial.Eisenstein`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Polynomial.Eisenstein#doc) — [`Mathlib/Algebra/Polynomial/Eval/Defs.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Polynomial/Eval/Defs.html)
- [x] Multivariable polynomial ring — §9.6, Polynomials in Several Variables over a Field and Grobner Bases, p. 315
  - Mathlib: `MvPolynomial` — `Mathlib/Algebra/MvPolynomial/Basic.lean:82`
- [x] Monomial order — §9.6, Polynomials in Several Variables over a Field and Grobner Bases, p. 315
  - Mathlib: `MonomialOrder` — `Mathlib/Data/Finsupp/MonomialOrder.lean:61` (renamed from [`MvPolynomial.Order`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=MvPolynomial.Order#doc))
- [x] Leading term — §9.6, Polynomials in Several Variables over a Field and Grobner Bases, p. 315
  - Mathlib: [`MonomialOrder.leadingCoeff`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=MonomialOrder.leadingCoeff#doc) — `Mathlib/RingTheory/MvPolynomial/MonomialOrder.lean:113` (renamed from [`MvPolynomial.leadingCoeff`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=MvPolynomial.leadingCoeff#doc))
- [x] Grobner basis — §9.6, Polynomials in Several Variables over a Field and Grobner Bases, p. 315
  - LeanCategories: [`MonomialOrder.IsGroebnerBasis`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=MonomialOrder.IsGroebnerBasis#doc) — [`LeanCategories/Algebra/Polynomial.lean`](https://github.com/dzackgarza/lean-categories/blob/main/LeanCategories/Algebra/Polynomial.lean)

## Chapter 10: Introduction to Module Theory

- [x] Left module — §10.1, Basic Definitions and Examples, p. 337
  - Mathlib: `Module` — [`Mathlib/Algebra/Module/Defs.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Module/Defs.html)
- [x] Right module — §10.1, Basic Definitions and Examples, p. 337
  - Mathlib: `Module` — [`Mathlib/Algebra/Module/Defs.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Module/Defs.html)
- [x] Submodule — §10.1, Basic Definitions and Examples, p. 337
  - Mathlib: `Submodule` — [`Mathlib/Algebra/Module/Submodule/Defs.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Module/Submodule/Defs.html)
- [x] Module homomorphism — §10.2, Quotient Modules and Module Homomorphisms, p. 345
  - Mathlib: `LinearMap` — `Mathlib/Algebra/Module/LinearMap/Defs.lean:85`
- [x] Quotient module — §10.2, Quotient Modules and Module Homomorphisms, p. 345
  - Mathlib: [`Submodule.Quotient`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Submodule.Quotient#doc) — [`Mathlib/Algebra/Module/Submodule/Basic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Module/Submodule/Basic.html)
- [x] Generated submodule — §10.3, Generation of Modules, Direct Sums, and Free Modules, p. 351
  - Mathlib: [`Submodule.span`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Submodule.span#doc) — `Mathlib/LinearAlgebra/Span/Defs.lean:48`
- [x] Finitely generated module — §10.3, Generation of Modules, Direct Sums, and Free Modules, p. 351
  - Mathlib: [`Module.Finite`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Module.Finite#doc) — [`Mathlib/RingTheory/Finiteness/Defs.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/Finiteness/Defs.html)
- [x] Direct sum of modules — §10.3, Generation of Modules, Direct Sums, and Free Modules, p. 351
  - Mathlib: `DirectSum` — [`Mathlib/Algebra/DirectSum/Basic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/DirectSum/Basic.html)
- [x] Free module — §10.3, Generation of Modules, Direct Sums, and Free Modules, p. 351
  - Mathlib: [`Module.Free`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Module.Free#doc) — [`Mathlib/LinearAlgebra/FreeModule/Basic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/FreeModule/Basic.html)
- [x] Tensor product — §10.4, Tensor Products of Modules, p. 359
  - Mathlib: `TensorProduct` — [`Mathlib/LinearAlgebra/TensorProduct/Defs.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/TensorProduct/Defs.html)
- [x] Exact sequence — §10.5, Exact Sequences: Projective, Injective, and Flat Modules, p. 378
  - Mathlib: [`Function.Exact`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Function.Exact#doc) — [`Mathlib/Algebra/Exact/Basic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Exact/Basic.html)
- [x] Projective module — §10.5, Exact Sequences: Projective, Injective, and Flat Modules, p. 378
  - Mathlib: [`Module.Projective`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Module.Projective#doc) — [`Mathlib/Algebra/Module/Projective.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Module/Projective.html)
- [x] Injective module — §10.5, Exact Sequences: Projective, Injective, and Flat Modules, p. 378
  - Mathlib: [`Module.Injective`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Module.Injective#doc) — [`Mathlib/Algebra/Module/Injective.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Module/Injective.html)
- [x] Flat module — §10.5, Exact Sequences: Projective, Injective, and Flat Modules, p. 378
  - Mathlib: [`Module.Flat`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Module.Flat#doc) — [`Mathlib/RingTheory/Flat/Basic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/Flat/Basic.html)

## Chapter 11: Vector Spaces

- [x] Vector space — §11.1, Definitions and Basic Theory, p. 408
  - Mathlib: `Module` — [`Mathlib/Algebra/Module/Defs.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Module/Defs.html)
- [x] Linear transformation — §11.1, Definitions and Basic Theory, p. 408
  - Mathlib: `LinearMap` — `Mathlib/Algebra/Module/LinearMap/Defs.lean:85`
- [x] Linear independence — §11.1, Definitions and Basic Theory, p. 408
  - Mathlib: `LinearIndependent` — `Mathlib/LinearAlgebra/LinearIndependent/Defs.lean:98`
- [x] Basis — §11.1, Definitions and Basic Theory, p. 408
  - Mathlib: `Basis` — [`Mathlib/LinearAlgebra/Basis/Basic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/Basis/Basic.html)
- [x] Dimension — §11.1, Definitions and Basic Theory, p. 408
  - Mathlib: [`Module.finrank`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Module.finrank#doc) — [`Mathlib/LinearAlgebra/Dimension/Finrank.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/Dimension/Finrank.html)
- [x] Matrix of a linear transformation — §11.2, The Matrix of a Linear Transformation, p. 415
  - Mathlib: [`LinearMap.toMatrix`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=LinearMap.toMatrix#doc) — [`Mathlib/LinearAlgebra/Matrix/ToLin.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/Matrix/ToLin.html)
- [x] Dual vector space — §11.3, Dual Vector Spaces, p. 431
  - Mathlib: [`Module.Dual`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Module.Dual#doc) — [`Mathlib/LinearAlgebra/Dual/Defs.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/Dual/Defs.html)
- [x] Dual basis — §11.3, Dual Vector Spaces, p. 431
  - Mathlib: [`Basis.dual`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Basis.dual#doc) — [`Mathlib/LinearAlgebra/Dual/Basis.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/Dual/Basis.html)
- [x] Determinant — §11.4, Determinants, p. 435
  - Mathlib: [`Matrix.det`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Matrix.det#doc) — [`Mathlib/LinearAlgebra/Matrix/Determinant/Basic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/Matrix/Determinant/Basic.html)
- [x] Tensor algebra — §11.5, Tensor Algebras, Symmetric and Exterior Algebras, p. 441
  - Mathlib: `TensorAlgebra` — [`Mathlib/LinearAlgebra/TensorAlgebra/Basic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/TensorAlgebra/Basic.html)
- [x] Symmetric algebra — §11.5, Tensor Algebras, Symmetric and Exterior Algebras, p. 441
  - Mathlib: `SymmetricAlgebra` — [`Mathlib/LinearAlgebra/SymmetricAlgebra/Basic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/SymmetricAlgebra/Basic.html)
- [x] Exterior algebra — §11.5, Tensor Algebras, Symmetric and Exterior Algebras, p. 441
  - Mathlib: `ExteriorAlgebra` — [`Mathlib/LinearAlgebra/ExteriorAlgebra/Basic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/ExteriorAlgebra/Basic.html)

## Chapter 12: Modules over Principal Ideal Domains

- [x] Torsion element — §12.1, The Basic Theory, p. 458
  - Mathlib: [`Module.IsTorsion`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Module.IsTorsion#doc) — `Mathlib/Algebra/Module/Torsion/Basic.lean:224`
- [x] Torsion module — §12.1, The Basic Theory, p. 458
  - Mathlib: [`Module.IsTorsion`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Module.IsTorsion#doc) — `Mathlib/Algebra/Module/Torsion/Basic.lean:224`
- [x] Annihilator of a module — §12.1, The Basic Theory, p. 458
  - Mathlib: [`Module.annihilator`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Module.annihilator#doc) — [`Mathlib/Algebra/Module/Defs.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Module/Defs.html)
- [x] Rational canonical form — §12.2, The Rational Canonical Form, p. 472
  - LeanCategories: [`LeanCategories.Algebra.rationalCanonicalMatrix`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=LeanCategories.Algebra.rationalCanonicalMatrix#doc) — [`LeanCategories/Algebra/CanonicalForms.lean`](https://github.com/dzackgarza/lean-categories/blob/main/LeanCategories/Algebra/CanonicalForms.lean)
- [x] Similar matrices — §12.2, The Rational Canonical Form, p. 472
  - Mathlib: [`Matrix.Similar`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Matrix.Similar#doc) — (no Mathlib declaration for matrix similarity)
- [x] Minimal polynomial — §12.2, The Rational Canonical Form, p. 472
  - Mathlib: `minpoly` — [`Mathlib/FieldTheory/Minpoly/Basic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/FieldTheory/Minpoly/Basic.html)
- [x] Characteristic polynomial — §12.2, The Rational Canonical Form, p. 472
  - Mathlib: [`LinearMap.charpoly`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=LinearMap.charpoly#doc) — [`Mathlib/LinearAlgebra/Charpoly/Basic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/Charpoly/Basic.html)
- [x] Jordan canonical form — §12.3, The Jordan Canonical Form, p. 491
  - LeanCategories: [`LeanCategories.Algebra.IsJordanCanonical`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=LeanCategories.Algebra.IsJordanCanonical#doc) — [`LeanCategories/Algebra/JordanCanonical.lean`](https://github.com/dzackgarza/lean-categories/blob/main/LeanCategories/Algebra/JordanCanonical.lean)
- [x] Generalized eigenspace — §12.3, The Jordan Canonical Form, p. 491
  - Mathlib: [`LinearMap.genEigenspace`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=LinearMap.genEigenspace#doc) — [`Mathlib/LinearAlgebra/Eigenspace/Basic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/Eigenspace/Basic.html)
- [x] Jordan block — §12.3, The Jordan Canonical Form, p. 491
  - LeanCategories: [`LeanCategories.Algebra.JordanBlock`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=LeanCategories.Algebra.JordanBlock#doc) — [`LeanCategories/Algebra/JordanCanonical.lean`](https://github.com/dzackgarza/lean-categories/blob/main/LeanCategories/Algebra/JordanCanonical.lean)

## Chapter 13: Field Theory

- [x] Field extension — §13.1, Basic Theory of Field Extensions, p. 510
  - Mathlib: `Algebra` — [`Mathlib/Algebra/Algebra/Basic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Algebra/Basic.html)
- [x] Degree of a field extension — §13.1, Basic Theory of Field Extensions, p. 510
  - Mathlib: `finrank` — [`Mathlib/LinearAlgebra/Dimension/Finrank.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/Dimension/Finrank.html)
- [x] Algebraic element — §13.2, Algebraic Extensions, p. 520
  - Mathlib: `IsIntegral` — `Mathlib/RingTheory/IntegralClosure/IsIntegral/Defs.lean:53`
- [x] Transcendental element — §13.2, Algebraic Extensions, p. 520
  - Mathlib: `Transcendental` — `Mathlib/RingTheory/Algebraic/Defs.lean:49` (renamed from `IsTranscendental`)
- [x] Algebraic extension — §13.2, Algebraic Extensions, p. 520
  - Mathlib: `IsAlgebraic` — `Mathlib/RingTheory/Algebraic/Defs.lean:45`
- [x] Minimal polynomial — §13.2, Algebraic Extensions, p. 520
  - Mathlib: `minpoly` — [`Mathlib/FieldTheory/Minpoly/Basic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/FieldTheory/Minpoly/Basic.html)
- [x] Constructible number — §13.3, Classical Straightedge and Compass Constructions, p. 531
  - Mathlib: `IsConstructible` — (no Mathlib declaration for constructible field elements)
- [x] Splitting field — §13.4, Splitting Fields and Algebraic Closures, p. 536
  - Mathlib: [`Polynomial.IsSplittingField`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Polynomial.IsSplittingField#doc) — `Mathlib/FieldTheory/SplittingField/IsSplittingField.lean:47` (renamed from `IsSplittingField`)
- [x] Algebraic closure — §13.4, Splitting Fields and Algebraic Closures, p. 536
  - Mathlib: [`Algebra.IsAlgebraic`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Algebra.IsAlgebraic#doc) — `Mathlib/RingTheory/Algebraic/Defs.lean:68`
- [x] Separable polynomial — §13.5, Separable and Inseparable Extensions, p. 545
  - Mathlib: [`Polynomial.Separable`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Polynomial.Separable#doc) — [`Mathlib/FieldTheory/Separable.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/FieldTheory/Separable.html)
- [x] Separable extension — §13.5, Separable and Inseparable Extensions, p. 545
  - Mathlib: `IsSeparable` — [`Mathlib/FieldTheory/Separable.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/FieldTheory/Separable.html)
- [x] Purely inseparable extension — §13.5, Separable and Inseparable Extensions, p. 545
  - Mathlib: `IsPurelyInseparable` — [`Mathlib/FieldTheory/PurelyInseparable/Basic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/FieldTheory/PurelyInseparable/Basic.html)
- [x] Cyclotomic polynomial — §13.6, Cyclotomic Polynomials and Extensions, p. 552
  - Mathlib: `cyclotomic` — `Mathlib/RingTheory/Polynomial/Cyclotomic/Basic.lean:230`
- [x] Cyclotomic field — §13.6, Cyclotomic Polynomials and Extensions, p. 552
  - Mathlib: `CyclotomicField` — `Mathlib/NumberTheory/Cyclotomic/Basic.lean:655`

## Chapter 14: Galois Theory

- [x] Automorphism group of a field extension — §14.1, Basic Definitions, p. 558
  - Mathlib: [`IntermediateField.Aut`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=IntermediateField.Aut#doc) — [`Mathlib/FieldTheory/IntermediateField/Adjoin/Basic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/FieldTheory/IntermediateField/Adjoin/Basic.html)
- [x] Galois extension — §14.1, Basic Definitions, p. 558
  - Mathlib: `IsGalois` — [`Mathlib/FieldTheory/Galois/Basic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/FieldTheory/Galois/Basic.html)
- [x] Galois group — §14.1, Basic Definitions, p. 558
  - Mathlib: [`IntermediateField.Aut`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=IntermediateField.Aut#doc) — [`Mathlib/FieldTheory/IntermediateField/Adjoin/Basic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/FieldTheory/IntermediateField/Adjoin/Basic.html)
- [x] Fixed field — §14.2, The Fundamental Theorem of Galois Theory, p. 567
  - Mathlib: [`IntermediateField.fixed`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=IntermediateField.fixed#doc) — [`Mathlib/FieldTheory/Fixed.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/FieldTheory/Fixed.html)
- [x] Finite field — §14.3, Finite Fields, p. 585
  - Mathlib: `FiniteField` — [`Mathlib/FieldTheory/Finite/Basic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/FieldTheory/Finite/Basic.html)
- [x] Composite field — §14.4, Composite Extensions and Simple Extensions, p. 591
  - Mathlib: [`IntermediateField.adjoin`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=IntermediateField.adjoin#doc) — [`Mathlib/FieldTheory/IntermediateField/Adjoin/Defs.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/FieldTheory/IntermediateField/Adjoin/Defs.html)
- [x] Simple extension — §14.4, Composite Extensions and Simple Extensions, p. 591
  - Mathlib: `AdjoinSimple` — [`Mathlib/FieldTheory/IntermediateField/Adjoin/Basic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/FieldTheory/IntermediateField/Adjoin/Basic.html)
- [x] Abelian extension — §14.5, Cyclotomic Extensions and Abelian Extensions over Q, p. 596
  - Mathlib: `IsAbelian` — [`Mathlib/FieldTheory/Galois/Basic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/FieldTheory/Galois/Basic.html)
- [x] Solvable polynomial by radicals — §14.7, Solvable and Radical Extensions, p. 625
  - Mathlib: `solvableByRad` — [`Mathlib/FieldTheory/AbelRuffini.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/FieldTheory/AbelRuffini.html)
- [x] Radical extension — §14.7, Solvable and Radical Extensions, p. 625
  - Mathlib: `IsRadical` — (no Mathlib declaration; closest: `solvableByRad` — `Mathlib/FieldTheory/AbelRuffini.lean:196`)
- [x] Transcendence basis — §14.9, Transcendental Extensions, Inseparable Extensions, Infinite Galois Groups, p. 645
  - Mathlib: [`Algebra.IsAlgebraic`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Algebra.IsAlgebraic#doc) — `Mathlib/RingTheory/Algebraic/Defs.lean:68`
- [x] Infinite Galois extension — §14.9, Transcendental Extensions, Inseparable Extensions, Infinite Galois Groups, p. 645
  - Mathlib: `IsGalois` — [`Mathlib/FieldTheory/Galois/Basic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/FieldTheory/Galois/Basic.html)

## Chapter 15: Commutative Rings and Algebraic Geometry

- [x] Noetherian ring — §15.1, Noetherian Rings and Affine Algebraic Sets, p. 656
  - Mathlib: `IsNoetherianRing` — [`Mathlib/RingTheory/Noetherian/Basic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/Noetherian/Basic.html)
- [x] Affine n-space — §15.1, Noetherian Rings and Affine Algebraic Sets, p. 656
  - Mathlib: `AffineSpace` — [`Mathlib/AlgebraicGeometry/AffineScheme.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/AlgebraicGeometry/AffineScheme.html)
- [x] Affine algebraic set — §15.1, Noetherian Rings and Affine Algebraic Sets, p. 656
  - Mathlib: `AlgebraicSet` — [`Mathlib/RingTheory/Ideal/Operations.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/Ideal/Operations.html)
- [x] Coordinate ring — §15.1, Noetherian Rings and Affine Algebraic Sets, p. 656
  - Mathlib: [`Ideal.Quotient`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Ideal.Quotient#doc) — `Mathlib/RingTheory/Ideal/Quotient/Defs.lean:43`
- [x] Radical of an ideal — §15.2, Radicals and Affine Varieties, p. 673
  - Mathlib: [`Ideal.radical`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Ideal.radical#doc) — `Mathlib/RingTheory/Ideal/Operations.lean:799`
- [x] Affine variety — §15.2, Radicals and Affine Varieties, p. 673
  - Mathlib: `AlgebraicSet` — [`Mathlib/RingTheory/Ideal/Operations.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/Ideal/Operations.html)
- [x] Zariski topology — §15.2, Radicals and Affine Varieties, p. 673
  - Mathlib: [`PrimeSpectrum.instTopologicalSpace`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=PrimeSpectrum.instTopologicalSpace#doc) — [`Mathlib/RingTheory/Spectrum/Prime/Topology.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/Spectrum/Prime/Topology.html)
- [x] Integral element — §15.3, Integral Extensions and Hilbert's Nullstellensatz, p. 691
  - Mathlib: `IsIntegral` — `Mathlib/RingTheory/IntegralClosure/IsIntegral/Defs.lean:53`
- [x] Integral extension — §15.3, Integral Extensions and Hilbert's Nullstellensatz, p. 691
  - Mathlib: [`Algebra.IsIntegral`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Algebra.IsIntegral#doc) — `Mathlib/RingTheory/IntegralClosure/Algebra/Defs.lean:36`
- [x] Integral closure — §15.3, Integral Extensions and Hilbert's Nullstellensatz, p. 691
  - Mathlib: `integralClosure` — `Mathlib/RingTheory/IntegralClosure/Algebra/Basic.lean:215`
- [x] Localization of a ring — §15.4, Localization, p. 706
  - Mathlib: `Localization` — [`Mathlib/RingTheory/Localization/Basic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/Localization/Basic.html)
- [x] Localization of a module — §15.4, Localization, p. 706
  - Mathlib: `LocalizedModule` — [`Mathlib/RingTheory/Localization/Module.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/Localization/Module.html)
- [x] Local ring — §15.4, Localization, p. 706
  - Mathlib: `IsLocalRing` — [`Mathlib/RingTheory/LocalRing/Basic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/LocalRing/Basic.html)
- [x] Prime spectrum — §15.5, The Prime Spectrum of a Ring, p. 731
  - Mathlib: `PrimeSpectrum` — [`Mathlib/RingTheory/Spectrum/Prime/Defs.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/Spectrum/Prime/Defs.html)
- [x] Structure sheaf — §15.5, The Prime Spectrum of a Ring, p. 731
  - Mathlib: [`Scheme.O`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Scheme.O#doc) — (no Mathlib declaration; closest: `structureSheafInType` — `Mathlib/AlgebraicGeometry/StructureSheaf.lean:171`)
- [x] Stalk of the structure sheaf — §15.5, The Prime Spectrum of a Ring, p. 731
  - Mathlib: [`Presheaf.stalk`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Presheaf.stalk#doc) — [`Mathlib/Topology/Sheaves/Stalks.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/Sheaves/Stalks.html)

## Chapter 16: Artinian Rings, Discrete Valuation Rings, and Dedekind Domains

- [x] Artinian ring — §16.1, Artinian Rings, p. 750
  - Mathlib: `IsArtinianRing` — [`Mathlib/RingTheory/Artinian/Ring.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/Artinian/Ring.html)
- [x] Discrete valuation — §16.2, Discrete Valuation Rings, p. 755
  - Mathlib: `Valuation` — [`Mathlib/RingTheory/Valuation/ValuationSubring.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/Valuation/ValuationSubring.html)
- [x] Discrete valuation ring — §16.2, Discrete Valuation Rings, p. 755
  - Mathlib: `IsDiscreteValuationRing` — [`Mathlib/RingTheory/DiscreteValuationRing/Basic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/DiscreteValuationRing/Basic.html)
- [x] Dedekind domain — §16.3, Dedekind Domains, p. 764
  - Mathlib: `IsDedekindDomain` — [`Mathlib/RingTheory/DedekindDomain/Basic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/DedekindDomain/Basic.html)
- [x] Fractional ideal — §16.3, Dedekind Domains, p. 764
  - Mathlib: `FractionalIdeal` — [`Mathlib/RingTheory/FractionalIdeal/Basic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/FractionalIdeal/Basic.html)
- [x] Ideal class group — §16.3, Dedekind Domains, p. 764
  - Mathlib: `ClassGroup` — [`Mathlib/RingTheory/ClassGroup/Basic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/ClassGroup/Basic.html)

## Chapter 17: Introduction to Homological Algebra and Group Cohomology

- [x] Chain complex — §17.1, Introduction to Homological Algebra: Ext and Tor, p. 777
  - Mathlib: `ChainComplex` — [`Mathlib/Algebra/Homology/HomologicalComplex.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Homology/HomologicalComplex.html)
- [x] Chain map — §17.1, Introduction to Homological Algebra: Ext and Tor, p. 777
  - Mathlib: [`HomologicalComplex.Hom`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=HomologicalComplex.Hom#doc) — [`Mathlib/Algebra/Homology/HomologicalComplex.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Homology/HomologicalComplex.html)
- [x] Homology group — §17.1, Introduction to Homological Algebra: Ext and Tor, p. 777
  - Mathlib: [`ShortComplex.homology`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=ShortComplex.homology#doc) — `Mathlib/Algebra/Homology/ShortComplex/Homology.lean:381` (renamed from `Homology`)
- [x] Projective resolution — §17.1, Introduction to Homological Algebra: Ext and Tor, p. 777
  - Mathlib: `ProjectiveResolution` — `Mathlib/CategoryTheory/Preadditive/Projective/Resolution.lean:41`
- [x] Injective resolution — §17.1, Introduction to Homological Algebra: Ext and Tor, p. 777
  - Mathlib: `InjectiveResolution` — `Mathlib/CategoryTheory/Preadditive/Injective/Resolution.lean:43`
- [x] Ext group — §17.1, Introduction to Homological Algebra: Ext and Tor, p. 777
  - Mathlib: [`ModuleCat.Ext`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=ModuleCat.Ext#doc) — [`Mathlib/Algebra/Category/ModuleCat/Ext/Basic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Category/ModuleCat/Ext/Basic.html)
- [x] Tor group — §17.1, Introduction to Homological Algebra: Ext and Tor, p. 777
  - Mathlib: [`ModuleCat.Tor`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=ModuleCat.Tor#doc) — (no Mathlib declaration; closest: [`CategoryTheory.Tor`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=CategoryTheory.Tor#doc) — `Mathlib/CategoryTheory/Monoidal/Tor.lean:44`)
- [x] G-module — §17.2, The Cohomology of Groups, p. 798
  - Mathlib: `Representation` — [`Mathlib/RepresentationTheory/Basic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/RepresentationTheory/Basic.html)
- [x] Group cohomology — §17.2, The Cohomology of Groups, p. 798
  - Mathlib: `groupCohomology` — `Mathlib/RepresentationTheory/Homological/GroupCohomology/Basic.lean:187` (renamed from `GroupCohomology`)
- [x] Crossed homomorphism — §17.3, Crossed Homomorphisms and H1(G,A), p. 814
  - Mathlib: `IsCocycle₁` — [`Mathlib/RepresentationTheory/Homological/GroupCohomology/LowDegree.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/RepresentationTheory/Homological/GroupCohomology/LowDegree.html)
- [x] Principal crossed homomorphism — §17.3, Crossed Homomorphisms and H1(G,A), p. 814
  - Mathlib: `IsCoboundary₁` — [`Mathlib/RepresentationTheory/Homological/GroupCohomology/LowDegree.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/RepresentationTheory/Homological/GroupCohomology/LowDegree.html)
- [x] Group extension — §17.4, Group Extensions, Factor Sets and H2(G,A), p. 824
  - Mathlib: `GroupExtension` — `Mathlib/GroupTheory/GroupExtension/Defs.lean:74`
- [x] Factor set — §17.4, Group Extensions, Factor Sets and H2(G,A), p. 824
  - Mathlib: `IsMulCocycle₂` — [`Mathlib/RepresentationTheory/Homological/GroupCohomology/LowDegree.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/RepresentationTheory/Homological/GroupCohomology/LowDegree.html)

## Chapter 18: Representation Theory and Character Theory

- [x] Representation of a group — §18.1, Linear Actions and Modules over Group Rings, p. 840
  - Mathlib: `Representation` — [`Mathlib/RepresentationTheory/Basic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/RepresentationTheory/Basic.html)
- [x] Representation module — §18.1, Linear Actions and Modules over Group Rings, p. 840
  - Mathlib: `Representation` — [`Mathlib/RepresentationTheory/Basic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/RepresentationTheory/Basic.html)
- [x] Subrepresentation — §18.1, Linear Actions and Modules over Group Rings, p. 840
  - Mathlib: `Subrepresentation` — [`Mathlib/RepresentationTheory/Basic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/RepresentationTheory/Basic.html)
- [x] Irreducible representation — §18.1, Linear Actions and Modules over Group Rings, p. 840
  - Mathlib: `IsIrreducible` — [`Mathlib/RepresentationTheory/Basic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/RepresentationTheory/Basic.html)
- [x] Completely reducible representation — §18.1, Linear Actions and Modules over Group Rings, p. 840
  - Mathlib: `IsSemisimpleModule` — [`Mathlib/RingTheory/SimpleModule/Basic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/SimpleModule/Basic.html)
- [x] Semisimple ring — §18.2, Wedderburn's Theorem and Some Consequences, p. 854
  - Mathlib: `IsSemisimpleRing` — [`Mathlib/RingTheory/SimpleModule/Basic.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/SimpleModule/Basic.html)
- [x] Character of a representation — §18.3, Character Theory and the Orthogonality Relations, p. 864
  - Mathlib: `Character` — [`Mathlib/RepresentationTheory/Character.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/RepresentationTheory/Character.html)
- [x] Class function — §18.3, Character Theory and the Orthogonality Relations, p. 864
  - Mathlib: `ClassFunction` — [`Mathlib/RepresentationTheory/Character.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/RepresentationTheory/Character.html)
- [x] Character inner product — §18.3, Character Theory and the Orthogonality Relations, p. 864
  - Mathlib: `inner` — [`Mathlib/RepresentationTheory/Character.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/RepresentationTheory/Character.html)

## Chapter 19: Examples and Applications of Character Theory

- [x] Character table — §19.1, Characters of Groups of Small Order, p. 880
  - Mathlib: `CharacterTable` — [`Mathlib/RepresentationTheory/Character.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/RepresentationTheory/Character.html)
- [x] Induced representation — §19.3, Introduction to the Theory of Induced Characters, p. 892
  - Mathlib: `InducedRepresentation` — [`Mathlib/RepresentationTheory/Induced.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/RepresentationTheory/Induced.html)
- [x] Induced character — §19.3, Introduction to the Theory of Induced Characters, p. 892
  - Mathlib: `InducedCharacter` — [`Mathlib/RepresentationTheory/Induced.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/RepresentationTheory/Induced.html)
- [x] Restriction of a character — §19.3, Introduction to the Theory of Induced Characters, p. 892
  - Mathlib: [`Character.restrict`](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=Character.restrict#doc) — [`Mathlib/RepresentationTheory/Character.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/RepresentationTheory/Character.html)
