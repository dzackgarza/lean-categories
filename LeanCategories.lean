module

public import LeanCategories.Lattices.Integral.Unbundled.Basic
public import LeanCategories.Lattices.Integral.Unbundled.DualAndDiscriminant
public import LeanCategories.Lattices.Integral.Unbundled.StandardLattices
public import LeanCategories.Lattices.Integral.Unbundled.DiscriminantForms
public import LeanCategories.Lattices.Integral.Unbundled.CoxeterAndReflectiveLattices
public import LeanCategories.Schemes.Surface.Enriques
public import LeanCategories.Lattices.Integral.Unbundled.NikulinGluing
public import LeanCategories.Lattices.Integral.Unbundled.OverlatticesAndGluing
public import LeanCategories.Fans.Unbundled
public import LeanCategories.Lattices.Integral.Unbundled.Form.Basic
public import LeanCategories.Lattices.Integral.Unbundled.Form.Dual
public import LeanCategories.Lattices.Integral.Unbundled.Form.Discriminant
public import LeanCategories.Lattices.Integral.Unbundled.StandardHierarchy
public import LeanCategories.Stacks.Functors.SemitoroidalFunctor
public import LeanCategories.Stacks.Morphisms.DeformationGroupoid
public import LeanCategories.Stacks.Morphisms.StackMorphism
public import LeanCategories.Stacks.Objects.AlgebraicSpace
public import LeanCategories.Stacks.Objects.IntegralAffineManifold
public import LeanCategories.Stacks.Objects.KSBAStack
public import LeanCategories.Stacks.Objects.KulikovModel
public import LeanCategories.ComplexManifolds.Functors.PeriodMapFunctor
public import LeanCategories.ComplexManifolds.Morphisms.HolomorphicMap
public import LeanCategories.ComplexManifolds.Objects.ArithmeticQuotient
public import LeanCategories.ComplexManifolds.Objects.Domain
public import LeanCategories.ComplexManifolds.Objects.IntegralAffine
public import LeanCategories.Lattices.Discriminant.Functors.GluingFunctor
public import LeanCategories.Lattices.Discriminant.Morphisms.AntiIsometry
public import LeanCategories.Lattices.Discriminant.Objects.Basic
public import LeanCategories.Schemes.Divisor.Functors.PositivityFunctor
public import LeanCategories.Schemes.Divisor.Objects.DivisorClass
public import LeanCategories.Modules.FiniteFreeZ.Functors.ScalarExtension
public import LeanCategories.Modules.FiniteFreeZ.Morphisms.LinearMap
public import LeanCategories.Modules.FiniteFreeZ.Objects.Basic
public import LeanCategories.Lattices.Integral.Functors.DiscFunctor
public import LeanCategories.Lattices.Integral.Morphisms.Embedding
public import LeanCategories.Lattices.Integral.Morphisms.Involution
public import LeanCategories.Lattices.Integral.Morphisms.Overlattice
public import LeanCategories.Lattices.Integral.Morphisms.OverlatticeBijection
public import LeanCategories.Lattices.Integral.Morphisms.PrimitiveEmbeddingExistence
public import LeanCategories.Lattices.Integral.Morphisms.Reflection
public import LeanCategories.Lattices.Integral.Objects.Basic
public import LeanCategories.Lattices.Integral.Objects.Cusps
public import LeanCategories.Lattices.Integral.Objects.Dual
public import LeanCategories.Lattices.Integral.Objects.EvenLat
public import LeanCategories.Lattices.Integral.Objects.Genus
public import LeanCategories.Lattices.Integral.Objects.GramAndSum
public import LeanCategories.Lattices.Integral.Objects.IsotropicQuotient
public import LeanCategories.Lattices.Integral.Objects.Standard
public import LeanCategories.Lattices.Integral.Objects.StandardRootLattices
public import LeanCategories.Lattices.Integral.Objects.TwoElemLat
public import LeanCategories.Schemes.Pair.Functors.SurfaceMMPFunctor
public import LeanCategories.Schemes.Pair.Morphisms.DltContraction
public import LeanCategories.Schemes.Pair.Objects.KSBAModuliProperness
public import LeanCategories.Schemes.Pair.Objects.LogPair
public import LeanCategories.Schemes.Pair.Objects.ReflexiveSheaf
public import LeanCategories.Schemes.Pair.Objects.Singularities
public import LeanCategories.Modules.Quadratic.Functors.DiscriminantFunctor
public import LeanCategories.Modules.Quadratic.Morphisms.Isometry
public import LeanCategories.Fans.Functors.ToricFunctor
public import LeanCategories.Fans.Functors.Wythoff
public import LeanCategories.Fans.Morphisms.FanMorphism
public import LeanCategories.Fans.Objects.Cone
public import LeanCategories.Fans.Objects.Fan
public import LeanCategories.Fans.Objects.Semifan
public import LeanCategories.Groups.Reflection.Functors.FoldingFunctor
public import LeanCategories.Groups.Reflection.Morphisms.ChamberHom
public import LeanCategories.Groups.Reflection.Objects.AffineDiagram
public import LeanCategories.Groups.Reflection.Objects.Chambers
public import LeanCategories.Groups.Reflection.Objects.CoxeterDatum
public import LeanCategories.Groups.Reflection.Objects.OrientedHyperbolic
public import LeanCategories.Groups.Reflection.Objects.Representation
public import LeanCategories.Groups.Reflection.Objects.VinbergTheorem
public import LeanCategories.Schemes.Divisor.Objects.Reflexive
public import LeanCategories.Schemes.Functors.CyclicCover
public import LeanCategories.Schemes.Functors.StructureSheafFunctor
public import LeanCategories.Schemes.Morphisms.AnticanonicalQuotient
public import LeanCategories.Schemes.Morphisms.BlowupMorphism
public import LeanCategories.Schemes.Morphisms.CoverMorphism
public import LeanCategories.Schemes.Morphisms.FamilyMorphism
public import LeanCategories.Schemes.Morphisms.QuotientMorphism
public import LeanCategories.Schemes.Morphisms.RDPResolution
public import LeanCategories.Schemes.Morphisms.RelativeProj
public import LeanCategories.Schemes.Morphisms.RelativeSpec
public import LeanCategories.Schemes.Objects.Curve
public import LeanCategories.Schemes.Objects.DltBoundary
public import LeanCategories.Schemes.Objects.Surface
public import LeanCategories.Modules.Bilinear.Functors.Forget
public import LeanCategories.Modules.Bilinear.Morphisms.Hom
public import LeanCategories.Modules.Bilinear.Objects.Basic

@[expose] public section

/-!
# Master Export Module

This root module imports the full modular architecture across all 12 milestones of the formalization program.
-/

namespace LeanCategories

def program_completion_target : String :=
  "Full 12-Milestone Formalization Program: Lattices, Coxeter Geometry, Fans, Relative Schemes, Surfaces, & KSBA Moduli"

end LeanCategories
