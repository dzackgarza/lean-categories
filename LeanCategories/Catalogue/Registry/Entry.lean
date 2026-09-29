/-
Copyright (c) 2026 Dzack Garza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCategories.Catalogue.Syntax

@[expose] public section

/-!
# Registry entries

Declaration names are stored as Lean `Name` values.  JSON serialization is a
presentation concern; registration and environment lookup retain the checked
identity.
-/

namespace CasCatalogue


/-- Which lifts a registered fibration supplies. -/
inductive FibrationVariance
  /-- Cartesian lifts (`Functor.IsFibered`): reindexing is contravariant. -/
  | cartesian
  /-- Cocartesian lifts (`Functor.IsCofibered`): transport is covariant. -/
  | cocartesian
  deriving DecidableEq, Repr, Inhabited

/-- A fibration registry row (CC-FIB): a registered functor `projection : total ⥤ base`
together with `evidence`, a Lean proof that it is a cartesian (`Functor.IsFibered`) or
cocartesian (`Functor.IsCofibered`) fibration. Its fibres are the categories that vary with an
object of `base`. -/
structure FibrationEntry where
  id : FibrationId
  projection : FunctorId
  variance : FibrationVariance
  evidence : Lean.Name
  deriving Repr

/-- One step of a structural route: a registered structural functor row, or the forgetful
functor `total(c) → host(c)` of a registered classifier. -/
inductive EdgeRef
  | functor (id : FunctorId)
  | classifierForget (id : ClassifierId)
  /-- A functorial constructor applied to a structural edge: `Arr(U)`, `Core(U)`. Derived, never
  registered. -/
  | constructMap (constructor : ConstructorId) (inner : EdgeRef)
  deriving DecidableEq, Repr, Inhabited

/-- How a method's semantic functor consumes its receiver. -/
inductive MethodShape
  /-- The functor's source is the owner category itself. -/
  | object
  /-- The functor's source is `Core(owner)`: an isomorphism invariant of objects of the owner. -/
  | isoInvariant
  deriving DecidableEq, Repr, Inhabited

/-- A method presentation row (#53 §7): the surface name `name` of the registered functor
`functor`, owned at the category `owner` (its lowest generating level, #53 §5). It creates no
semantics: it names checked functor semantics. -/
structure MethodEntry where
  id : MethodId
  name : String
  owner : CategoryExpr
  functor : FunctorId
  shape : MethodShape
  /-- The result is a subobject of the receiver's image, and must be lifted back along every
  step of the route to become a subobject of the receiver itself (CC-LIFT). -/
  returnsToSource : Bool := false
  deriving Repr

/-- What a lift row returns to the source of a functor `U : C ⥤ D` (CC-LIFT). -/
inductive LiftKind
  /-- Subobjects: `evidence` is a `MonoLift U`, and the row's step is `U.mapArrow`. -/
  | subobjects
  /-- Limits of the registered shape `shape`: `evidence` is Mathlib's `CreatesLimitsOfShape J U`
  for the functor `U` of the row's step, where `J` is the shape of the registered limits named
  `shape`. A limit computed in `D` is returned to `C` along it. -/
  | createsLimits (shape : String)
  deriving DecidableEq, Repr

/-- A lift row (CC-LIFT): `evidence` returns results computed along the route step `edge` to its
source, as `kind` says: subobjects (a `MonoLift`), or limits (Mathlib's `CreatesLimitsOfShape`). -/
structure LiftEntry where
  id : LiftId
  edge : EdgeRef
  evidence : Lean.Name
  kind : LiftKind := .subobjects
  deriving Repr

/-- A limit presentation row (CC-UNIV): `declaration` is a family of Mathlib `LimitCone`s (apex,
legs, `IsLimit` with its mediator) of the diagrams of one shape in the registered category
`category`, e.g. `Types.pullbackLimitCone` for pullbacks of sets. -/
structure LimitEntry where
  id : LimitId
  category : CategoryId
  shape : String
  declaration : Lean.Name
  /-- A colimit presentation: `declaration` is a family of Mathlib `ColimitCocone`s. -/
  colimit : Bool := false
  deriving Repr

/-- An adjunction row (CC-CALC): `declaration` is a Mathlib `Adjunction L R` between the registered
functors `left` and `right` (unit, counit, and the transpose `homEquiv`), e.g. `constLimAdj`. -/
structure AdjunctionEntry where
  id : AdjunctionId
  left : FunctorId
  right : FunctorId
  declaration : Lean.Name
  deriving Repr

/-- A named object or object constructor (CC-CALC): `declaration : (parameters) → C`, a Lean
function from typed parameters to the objects of the registered category `category`, e.g.
`n ↦ ℤ/n` in `Sets`. Its parameters are typed terms, never strings. A leaf presents its values by
handles, each with its identification; it never names the object. -/
structure ObjectRefinement where
  /-- The object this one refines, in the target category of `edge`. -/
  base : ObjectId
  /-- The structural route forgetting the refinement: a nonempty chain of structural steps from
  this object's category to the base's. -/
  route : Array EdgeRef
  /-- `∀ params, route.obj (declaration params) ≅ base.declaration params`; its domain is checked
  to be the image along the route. -/
  identification : Lean.Name
  deriving Repr

structure ObjectEntry where
  id : ObjectId
  category : CategoryId
  declaration : Lean.Name
  /-- Its surface name in the language (`ℤ`, `Fin`, `ZMod`), applied to its parameters. An
  unrefined object's name is unique among unrefined objects; a refinement bears its base's name,
  and is named in the language by `X in C`. -/
  name : String
  /-- When this object is another one with more structure: `Fin(n)` in `FiniteSets` refines
  `Fin(n)` in `Sets` along the forgetful functor. -/
  refines : Option ObjectRefinement := none
  deriving Repr

/-- A literal form of a registered category (CC-CALC): `type` is a Lean type of literal values with
decidable equality, and `denotation : type → C` sends each to the object of the category
`category` it denotes, e.g. `n ↦ n` and `ℵ₀ ↦ ℵ₀` in `Card`. A statement comparing a computed
value with a literal compares it with this denotation. -/
structure LiteralEntry where
  id : LiteralId
  category : CategoryId
  type : Lean.Name
  denotation : Lean.Name
  deriving Repr

/-- The element literals of a registered object family: `denotation : ∀ params, ℕ → Option X`,
where `X` is the object at `params`, sends a numeral to the element it names, or to `none` if it
names none (`k ↦ k` in `Fin n` for `k < n`, `k ↦ k mod n` in `ℤ/n`). -/
structure ElementLiteralEntry where
  id : LiteralId
  object : ObjectId
  denotation : Lean.Name
  deriving Repr

/-- The graph literals of a registered category's morphisms: `denotation` sends a finite list of
pairs of elements `l : List (X × Y)` whose first components list every element of `X` exactly once
to the morphism `X ⟶ Y` with that graph. In `Sets`, `{0 ↦ 1, 1 ↦ 0} : Fin 2 → Fin 2`. -/
structure GraphLiteralEntry where
  id : LiteralId
  category : CategoryId
  denotation : Lean.Name
  deriving Repr

/-- A registered inclusion of named objects of one category, `sub ⊆ super`: a monomorphism
`declaration : ∀ params, sub params ⟶ super params` with `mono : ∀ params, Mono (declaration
params)`, at the same parameters (`ℤ ⊆ ℚ ⊆ ℝ ⊆ ℂ` in `Sets`, by the casts). -/
structure InclusionEntry where
  id : InclusionId
  category : CategoryId
  sub : ObjectId
  super : ObjectId
  declaration : Lean.Name
  mono : Lean.Name
  deriving Repr

/-- An element operation of a registered category `C` whose objects refine sets: `declaration :
∀ X, (U X)^arity ⟶ U X` in `Sets`, natural in `X`, where `U X` is the set `X` refines and the power
is Lean's product (`U X × U X` for arity 2, `U X` for arity 1, the terminal set for arity 0). Its
surface name is the language's operator (`+`, `·`, `-`). For rings: addition, multiplication and
negation of elements. -/
structure OperationEntry where
  id : OperationId
  category : CategoryId
  name : String
  arity : Nat
  declaration : Lean.Name
  /-- The set the operation lands in, when it is not the underlying set: `Ω` for a relation
  (`≤ : X × X → Ω`). -/
  result : Option ObjectId := none
  /-- The number of numeral parameters the declaration takes after the object (`x^k`: one). -/
  numerals : Nat := 0
  deriving Repr

/-- A power object of `Sets` in the sense of elementary topos theory (Mac Lane–Moerdijk, *Sheaves
in Geometry and Logic*, IV.1): the family `object : X ↦ 𝒫 X`, the truth values `omega` with their
element `truth : 1 → Ω`, and at each `X`
* `member : X × 𝒫 X ⟶ Ω`, membership;
* `transpose : (X ⟶ Ω) → (1 ⟶ 𝒫 X)`, the subset a predicate classifies;
* `extent : (1 ⟶ 𝒫 X) → Sets`, the set of members of a subset;
* `empty : 1 ⟶ 𝒫 X` and `singleton : X ⟶ 𝒫 X`, and `union`, the name of the operation `∪` on
  the refinement of `𝒫 X`, from which finite subsets `{x₁, …, xₙ}` are formed;
* `terminal : X ⟶ 1`, through which a global element is a generalized one at a stage `X`;
* `image : (X ⟶ Y) → (1 ⟶ 𝒫 Y)`, the image of a map. -/
structure PowerObjectEntry where
  id : PowerObjectId
  object : ObjectId
  omega : ObjectId
  truth : Lean.Name
  member : Lean.Name
  transpose : Lean.Name
  extent : Lean.Name
  empty : Lean.Name
  singleton : Lean.Name
  terminal : Lean.Name
  image : Lean.Name
  union : String
  deriving Repr

/-- A named morphism family of a registered category: `declaration : ∀ params, X ⟶ Y`, with its
surface name in the language (`rev`), unique among the category's objects and morphisms. -/
structure MorphismEntry where
  id : MorphismId
  category : CategoryId
  name : String
  declaration : Lean.Name
  deriving Repr

/-- A cell row (CC-CALC, CC-COHERE): a natural transformation `declaration : L ⟶ R` (or, when `invertible`,
a natural isomorphism `L ≅ R`) between the composites `L`, `R` of the registered functors along
`left` and `right` (the identity of `source` when empty). The cell is Mathlib's; the row names it
so that it can be composed, whiskered and realized. An invertible cell between two distinct
structural routes identifies them (a comparison): a call reached along either runs on the route the
cell's direction designates, and its component carries data between the two. -/
structure CellEntry where
  id : NaturalTransformationId
  source : CategoryExpr
  target : CategoryExpr
  left : Array EdgeRef
  right : Array EdgeRef
  declaration : Lean.Name
  invertible : Bool := false
  deriving Repr

/-- A property presentation row (CC-PROP): the surface name `name` of the registered classifier
`classifier`, which alone owns the property's meaning. With `receiver := some A` it is an alias
available only on `A` (e.g. `is_abelian` on groups for commutativity of the multiplicative port,
#53 §12); it adds no meaning. -/
structure PropertyEntry where
  id : PropertyId
  name : String
  classifier : ClassifierId
  receiver : Option CategoryExpr := none
  deriving Repr

/-- The kind of one argument of a typed category constructor. -/
inductive ConstructorArgKind
  | category
  | object
  | functor
  deriving DecidableEq, Repr, Inhabited

/-- A typed category constructor (#54 §1): its argument signature and the Lean definition that is
its semantics. A category whose expression is `.construct id args` must be definitionally
`semantics` applied to the registered denotations of `args`. -/
structure ConstructorEntry where
  id : ConstructorId
  signature : Array ConstructorArgKind
  semantics : Lean.Name
  /-- For a unary category constructor that is functorial, its action on functors
  (`F : C ⥤ D` to `semantics C ⥤ semantics D`), e.g. `Functor.mapArrow` for `Arr`. -/
  functorialAction : Option Lean.Name := none
  deriving Repr

/-- Named category registry row. -/
structure NamedCategoryEntry where
  id : CategoryId
  declaration : Lean.Name
  expression : CategoryExpr
  /-- Elaborated witness tying this expression to the declared category. -/
  realization : Lean.Name
  /-- Typed pullback witness required when the expression is a refinement. -/
  refinementRealization : Option Lean.Name := none
  /-- Its surface name in the language (`Sets`, `Groups`), or empty if the language does not name
  it. Names are unique among categories. -/
  name : String := ""
  deriving Repr, Inhabited

/--
A parameterized category family, distinct from any selected category node.

The typed realization supplies the parameter data and its category-valued fibre.
The registry records transport orientation separately.
-/
structure CategoryFamilyEntry where
  id : CategoryFamilyId
  schema : CategoryFamilySchema
  realization : Lean.Name
  transport : Lean.Name
  transportSemantics : CategoryFamilyTransportSemantics
  deriving Repr, Inhabited

/-- Classifier registry row. -/
structure ClassifierEntry where
  id : ClassifierId
  declaration : Lean.Name
  host : CategoryExpr
  realization : Lean.Name
  deriving Repr, Inhabited

/-- A typed functor declaration, with expression endpoints checked by Lean. -/
structure FunctorEntry where
  id : FunctorId
  source : CategoryExpr
  target : CategoryExpr
  declaration : Lean.Name
  realization : Lean.Name
  expression : FunctorExpr source target
  /-- Whether this functor sends an object to its *underlying* object (a forgetful functor,
  an inclusion, a fibre inclusion `ι_R : Mod_R → ∫ Mod`): the only kind of registered functor
  along which methods are inherited (#53 §8, CC-UNIFORM). Not structural: construction functors
  (base change, change of values, reindexing along a parameter morphism), which need data the
  receiver does not carry, and a fibration's projection to its base or value parameters
  (`∫ Mod → Ring`, `Bil → ∫ Mod` by values), which reads a parameter of the object rather than
  an object it *is*: a module is not a ring, so it must not inherit the ring's cardinality. -/
  structural : Bool := false
  deriving Repr

/-- Opaque category with typed structural ports. -/
structure StructuralPortEntry where
  id : OpaquePortId
  source : CategoryExpr
  target : CategoryExpr
  declaration : Lean.Name
  realization : Lean.Name
  provenance : String
  deriving Repr, Inhabited

structure OpaqueCategoryEntry where
  id : CategoryId
  declaration : Lean.Name
  realization : Lean.Name
  ports : Array StructuralPortEntry
  reason : String
  deriving Repr, Inhabited

end CasCatalogue
