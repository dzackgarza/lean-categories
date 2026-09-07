from __future__ import annotations

import json
from pathlib import Path

out = {}

def add(n, route, refs, comparison, family):
    out[str(n)] = {
        'route': route, 'refs': refs,
        'comparison': comparison, 'search_family': family,
    }

def u(n, refs, comparison, family):
    add(n, 'unmatched', refs, comparison, family)

def a(n, refs, comparison, family):
    add(n, 'project-existing', refs, comparison, family)

u(1, 'A/Lattices/Valued/Standard.lean; A/Lattices/Valued/Signature.lean; A/Lattices/Valued/MetricDual.lean',
  'The project defines parity, signature and unimodularity and supplies standard models, but no theorem classifies every indefinite unimodular integral lattice by parity, rank and index.', 'classification')
a(2, 'A/Lattices/Valued/Residue.lean :: reduceIntegralToResidueField, reduceIntegralToResidueField_pairing_tmul',
  'For R=Z and the prime ideal (p), the residue-field base change is the canonical reduction of the lattice modulo p and its pairing is the reduction of the integral pairing.', 'residue')
u(3, 'A/Lattices/Valued/Residue.lean; P/LinearAlgebra/BilinearForm/Properties.lean',
  'The reduction functor and the generic criterion that a finite bilinear form is nondegenerate iff its determinant is nonzero are available, but no existing declaration connects primality of the integral discriminant to nondegeneracy of this lattice reduction as one theorem.', 'residue')
u(4, 'A/Lattices/Valued/Residue.lean; A/Lattices/Valued/ScaleAndEvenness.lean; P/LinearAlgebra/BilinearForm/Properties.lean',
  'The ingredients for an alternating reduction in characteristic two are present, but the claimed even-dimensionality/rank theorem for an even odd-discriminant lattice is not an existing declaration.', 'residue')
u(5, 'P/LinearAlgebra/BilinearForm/Properties.lean; P/LinearAlgebra/SymplecticGroup.lean',
  'Mathlib has alternating bilinear forms and symplectic matrices, but no bundled general symplectic-space owner matching the source remark was identified.', 'symplectic')
u(6, 'T/LowDimTopology/Plumbing/Characteristic.lean',
  'TauCeti defines characteristic covectors only for plumbing lattices. The source definition quantifies characteristic elements of an arbitrary odd-discriminant integral lattice.', 'characteristic')
u(7, 'A/Lattices/Valued/ScaleAndEvenness.lean; T/LowDimTopology/Plumbing/Characteristic.lean',
  'Evenness is implemented and TauCeti has plumbing characteristic covectors, but no arbitrary-lattice theorem states that zero is characteristic under the source hypotheses.', 'characteristic')
u(8, 'T/LowDimTopology/Plumbing/Characteristic.lean; T/LowDimTopology/Plumbing/Weight/Basic.lean',
  'No searched source provides existence of characteristic elements for all odd-discriminant lattices together with well-definedness and orthogonal additivity of the square modulo eight.', 'characteristic')
u(9, '', 'This is a scope remark about the preceding sigma-invariant construction; because that construction is unmatched, there is no independent Lean owner for the remark.', 'characteristic')
u(10, 'A/Lattices/Valued/Standard.lean; A/Lattices/Valued/ScaleAndEvenness.lean',
  'Standard rank-one lattices and evenness exist, but the sigma-invariant calculations modulo eight are not formalized.', 'characteristic')
u(11, 'A/Lattices/Valued/Standard.lean; A/Lattices/Valued/MetricDual.lean; A/Lattices/Valued/Signature.lean',
  'The standard hyperbolic lattice and unimodularity/signature predicates exist; the complete rank-at-most-four classification of all unimodular lattices does not.', 'classification')
u(12, 'P/LinearAlgebra/QuadraticForm/Isometry.lean; A/Lattices/Valued/OrthogonalSummand.lean; A/Lattices/Valued/Standard.lean',
  'Generic isotropic-vector and orthogonal-complement tools do not prove that every indefinite unimodular integral lattice contains an integral isotropic vector and splits off U or the odd plane W.', 'classification')
u(13, 'P/LinearAlgebra/BilinearForm/Basic.lean; A/Lattices/Valued/Signature.lean',
  'Diagonalization of symmetric forms over fields does not imply integral diagonalization of every odd indefinite unimodular Z-lattice. No integral classification theorem was identified.', 'classification')
u(14, 'A/Lattices/Valued/Signature.lean; A/Lattices/Valued/MetricDual.lean',
  'No theorem identifies arbitrary even indefinite unimodular lattices having the same rank and index.', 'classification')
u(15, 'A/Lattices/Valued/Signature.lean; A/Lattices/Valued/ScaleAndEvenness.lean',
  'Signature/index and evenness are represented, but the van der Blij congruence sigma(L)=tau(L) mod 8 and its divisibility consequence are not formalized.', 'characteristic')
u(16, 'A/Lattices/Valued/Standard.lean; A/Lattices/Valued/Constructions.lean',
  'E8, the hyperbolic plane and orthogonal-sum constructions exist, but the source row is an existence-and-uniqueness classification for all even indefinite unimodular lattices, which those constructors do not establish.', 'classification')
u(17, 'A/Lattices/Valued/Standard.lean',
  'The E8 and U models are implemented, but no isometry E8 plus its opposite to eight hyperbolic planes was identified.', 'classification')
u(18, 'P/Geometry/Manifold/Bordism.lean; T/LowDimTopology/Plumbing/IntersectionForm.lean',
  'Mathlib mentions intersection forms only as motivation in manifold bordism, while TauCeti constructs the form of a plumbing graph. Neither constructs the unimodular cup/intersection form on H^2 of an arbitrary oriented compact four-manifold or the realizability notions.', 'four-manifold')
u(19, 'T/LowDimTopology/Plumbing/BlowUp.lean; T/LowDimTopology/Plumbing/EdgeBlowUp.lean',
  'TauCeti proves orthogonal splitting for plumbing blow-ups, not the connected-sum formula for arbitrary four-manifolds.', 'four-manifold')
u(20, 'P/Topology/Homotopy/SimplyConnected.lean; A/Lattices/Valued/MetricDual.lean',
  'Simply-connected-space and unimodular-lattice APIs do not establish torsion-freeness of H^2 or the indefinite intersection-form classification for four-manifolds.', 'four-manifold')
u(21, 'P/Topology/Homotopy/SimplyConnected.lean',
  'No formalization of Freedman classification/existence for simply connected topological four-manifolds was found in project, Mathlib, package, GitHub, or reference searches.', 'four-manifold')
u(22, 'P/LinearAlgebra/BilinearForm/Basic.lean',
  'Algebraic diagonalization over fields is not Donaldson diagonalization over Z. No compatible formalization of Donaldson theorem was found.', 'four-manifold')
u(23, 'A/Lattices/Valued/Standard.lean',
  'The standard U and E8 lattices exist, but the asserted restriction on smooth simply connected four-manifold intersection forms depends on Donaldson and the global integral classification, both unmatched.', 'four-manifold')
u(24, 'P/Geometry/Manifold; A/Lattices/Valued/ScaleAndEvenness.lean',
  'No second Stiefel-Whitney class API and no theorem equating its vanishing with parity of the integral intersection form under the no-2-torsion hypothesis was identified.', 'four-manifold')
u(25, 'P/Topology/Homotopy/SimplyConnected.lean; P/AlgebraicTopology',
  'The searched topology APIs do not supply this universal-coefficient/Poincare-duality torsion calculation for closed simply connected four-manifolds.', 'four-manifold')
u(26, '', 'No compatible formalization of the Rokhlin/Rohlin signature divisibility theorem was found. A broad GitHub hit merely records it as an external missing hypothesis, not a proof.', 'four-manifold')
u(27, '', 'This corollary depends on the unmatched parity criterion and Rokhlin theorem; no independent exact owner was found.', 'four-manifold')
u(28, 'P/Geometry/Manifold/Complex; P/Geometry/Manifold',
  'No formalization connects divisibility of c1 for simply connected complex surfaces to parity of the integral intersection form, and the K3/hypersurface examples are likewise absent.', 'complex-surface')
u(29, 'P/Geometry/Manifold/Complex; P/Geometry/Manifold/VectorBundle',
  'Complex manifold and vector-bundle infrastructure exists, but no source-complete canonical-bundle/c1/holomorphic-two-form theorem for compact complex surfaces was identified.', 'complex-surface')
u(30, 'P/Geometry/Manifold; P/AlgebraicTopology',
  'The Chern-number, Euler-number and Hirzebruch signature formula bundle for compact complex surfaces is not present in the searched APIs.', 'complex-surface')
u(31, 'A/Lattices/Valued/Standard.lean; A/Lattices/Valued/Constructions.lean',
  'U and E8 plus orthogonal constructions exist, but no declared E_{a,±b} family with the stated even/unimodular/index package was identified; assembling it would be new source work.', 'classification')
u(32, 'A/Lattices/Valued/Standard.lean :: k3Lattice, k3Lattice_integralSignature, k3Lattice_isUnimodular, k3Lattice_isEven',
  'The abstract K3 lattice is implemented with the right signature/parity/unimodularity, but the source row asserts geometric realization by K3 surfaces and connected-sum realization of a whole family, which are not formalized.', 'complex-surface')
u(33, '', 'No Lean statement/proof of the 11/8 conjecture was found in project, pinned/current Mathlib, formal-conjectures, Reservoir, TauCeti, LeanSearch, Loogle or broad GitHub search.', 'four-manifold')
u(34, 'A/Lattices/Valued/Standard.lean',
  'The consequence uses the 11/8 conjecture, Freedman classification, K3/quadric realizations and the theorem for complex surfaces; these are not jointly formalized.', 'four-manifold')

assert len(out) == 34
Path('/tmp/fc11-continuation/c02-decisions.json').write_text(json.dumps(out, indent=2, ensure_ascii=False))
print('recorded', len(out), 'C02 decisions')
