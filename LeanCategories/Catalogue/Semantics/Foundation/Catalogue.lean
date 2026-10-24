module

public import LeanCategories.Catalogue.Id

@[expose] public section

namespace CasCatalogue


namespace CategoryId
def sets : CategoryId := ⟨"cat.sets"⟩
end CategoryId

namespace ClassifierId
def setsFinite : ClassifierId := ⟨"clf.sets.finite"⟩
def setsGraded : ClassifierId := ⟨"clf.sets.graded"⟩
def setsBinaryOperation : ClassifierId := ⟨"clf.sets.binary_operation"⟩
def setsCountable : ClassifierId := ⟨"clf.sets.countable"⟩
def setsEnumerated : ClassifierId := ⟨"clf.sets.enumerated"⟩
end ClassifierId

namespace FunctorId
def setsIdentity : FunctorId := ⟨"fun.sets.identity"⟩
def finiteToCountable : FunctorId := ⟨"fun.sets.finite_to_countable"⟩
def enumeratedToCountable : FunctorId := ⟨"fun.sets.enumerated_to_countable"⟩
end FunctorId

end CasCatalogue
