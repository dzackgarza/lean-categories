from __future__ import annotations

import json
from pathlib import Path

d = {}

def add(n, route, refs, comparison, family):
    d[str(n)] = dict(route=route, refs=refs, comparison=comparison, search_family=family)

def a(n, refs, comparison, family='quadratic'):
    add(n, 'project-existing', refs, comparison, family)

def m(n, refs, comparison, family='quadratic'):
    add(n, 'mathlib', refs, comparison, family)

def r(n, refs, comparison, family='quadratic'):
    add(n, 'reference-port', refs, comparison, family)

def u(n, refs, comparison, family='quadratic'):
    add(n, 'unmatched', refs, comparison, family)

a(1, 'A/Lattices/Valued/Hasse.lean :: hasseMinkowskiInvariantOfDiagonal, hasseMinkowskiInvariantOfDiagonal_eq_prod_Iio',
  'For a diagonal tuple of nonzero coefficients this is exactly the product over i<j of the Hilbert symbols, matching the source Hasse invariant definition.', 'hasse')
m(2, 'P/LinearAlgebra/QuadraticForm/Basic.lean :: QuadraticMap.associatedHom, QuadraticMap.associated_apply, QuadraticMap.associated_eq_self_apply',
  'When 2 is invertible, associatedHom is one half of the polar form q(x+y)-q(x)-q(y), and associated_eq_self_apply gives b(x,x)=q(x), exactly the source convention.', 'quadratic')
r(3, 'R/QuadraticForm/Basic.lean :: QuadraticMap.XY, QuadraticMap.IsHyperbolic, QuadraticMap.XY_isHyperbolic',
  'The reference source defines the binary split form XY and calls a quadratic form hyperbolic exactly when it is equivalent to that two-dimensional model. The declarations are complete, but the source targets Lean 4.34.0-rc2 and therefore require a port.', 'hyperbolic')
u(4, 'R/QuadraticForm/Chain.lean :: Module.Basis.IsContiguous, Module.Basis.Chain',
  'The reference source has the intended vocabulary, but its Chain structure currently states contiguity of a basis with itself rather than consecutive bases, so it is not interface-equivalent to the source definition.', 'chain')
u(5, 'R/QuadraticForm/Chain.lean',
  'No exact formalization of the displayed Euclidean rotation example was identified; the reference chain file contains only the general setup.', 'chain')
u(6, 'R/QuadraticForm/Chain.lean :: Module.Basis.chainOfNondegenerate',
  'The exact reference theorem exists only with a `sorry` proof in current upstream, so it is not accepted as a completed owner.', 'chain')
a(7, 'A/Lattices/Valued/HasseInvariance.lean :: hasseMinkowskiInvariantOfDiagonal_eq_of_equivalent, DiagonalPresentation.hasseMinkowskiValue_eq, hasseMinkowskiInvariant',
  'The project proves directly that the diagonal Hasse value is invariant under quadratic equivalence and that any two diagonal presentations compute the same canonical value. This supplies the source well-definedness result without the incomplete chain proof.', 'hasse')
r(8, 'R/QuadraticForm/Basic.lean :: QuadraticMap.Isotropic, QuadraticMap.represents, QuadraticMap.represents_zero_iff_isotropic',
  'The reference source defines representation by a nonzero vector and proves representation of zero equivalent to isotropy exactly as in the source. These declarations are complete but require a toolchain port.', 'representation')
u(9, 'R/QuadraticForm/Basic.lean :: QuadraticMap.represents_of_isotropic_of_nondegenerate',
  'The reference source has the exact theorem under nondegeneracy, but its current proof is `sorry`; no independent completed owner was found.', 'representation')
u(10, 'R/QuadraticForm/Basic.lean',
  'This is a cross-reference to a later general lemma; no independent completed declaration matching the remark was found.', 'representation')
u(11, 'R/QuadraticForm/Basic.lean :: QuadraticMap.represents_iff_sub_isotropic',
  'The reference source contains the crucial representation-versus-isotropy criterion, but it is still `sorry` in current upstream; the full three-way equivalence therefore has no completed owner.', 'representation')
u(12, 'R/QuadraticForm/HighRank.lean',
  'The searched reference project proves only the rational Hasse-Minkowski high-rank step, and its key high-rank isotropy theorem remains `sorry`; no completed theorem that every rank-at-least-five form over Q_p is isotropic was found.', 'padic')
u(13, 'R/QuadraticForm/HasseMinkowskiInvariant.lean; A/Lattices/Valued/Hasse.lean; A/Lattices/Valued/PadicHilbert.lean',
  'Rank-two/three Hilbert-symbol ingredients and p-adic symbol formulae exist, but the source row is the complete rank-by-rank Q_p representability classification. No single completed owner supplies all four cases.', 'padic')
u(14, 'A/Lattices/Valued/PadicHilbert.lean; R/HilbertSymbol/Basic.lean',
  'The local Hilbert-symbol computations do not provide the finite-exceptional-prime theorem for a localized rational ternary form as an existing declaration.', 'padic')
u(15, 'A/Lattices/Valued/HasseInvariance.lean; A/Lattices/Valued/PadicHilbert.lean; R/QuadraticForm/HasseMinkowskiInvariant.lean',
  'Rank, discriminant and Hasse invariants are represented, but no completed theorem classifies all nondegenerate Q_p quadratic forms up to isometry by those invariants.', 'padic-classification')
u(16, 'R/QuadraticForm/HasseMinkowski.lean :: QuadraticMap.HasseMinkowski',
  'The reference source has the exact Hasse-Minkowski statement, but every rank branch of the current proof is `sorry`; it is therefore not accepted as a completed reference port.', 'local-global')
u(17, 'R/QuadraticForm/HasseMinkowski.lean; R/QuadraticForm/Basic.lean',
  'The representability corollary would require the incomplete Hasse-Minkowski theorem together with the incomplete representation/isotropy criterion; no independent completed theorem was found.', 'local-global')
u(18, 'R/QuadraticForm/HasseMinkowski.lean; A/Lattices/Valued/Signature.lean',
  'Meyer’s theorem is not present as a completed declaration; deriving it would require the incomplete global theorem plus local high-rank isotropy.', 'local-global')
u(19, 'R/QuadraticForm/HasseMinkowski.lean; A/Lattices/Valued/HasseInvariance.lean',
  'The searched sources formalize isotropy local-global infrastructure, not the source isometry Hasse principle for two rational quadratic spaces. No completed exact owner was found.', 'local-global')
u(20, 'A/Lattices/Valued/Hasse.lean; A/Lattices/Valued/HasseInvariance.lean; R/HilbertSymbol/Basic.lean',
  'Parts of the bundled remark are formalized (real Hasse invariant/signature behavior and Hilbert-product infrastructure), but the row also asserts the behavior of prescribed local isometries and the full global product statement. Strict whole-row semantics therefore leave it unmatched.', 'local-global')

assert len(d) == 20
Path('/tmp/fc11-continuation/c03-decisions.json').write_text(json.dumps(d, indent=2, ensure_ascii=False))
print('recorded', len(d), 'C03 decisions')
