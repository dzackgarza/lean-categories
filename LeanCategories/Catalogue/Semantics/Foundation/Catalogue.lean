module

public import LeanCategories.Catalogue.Id

@[expose] public section

namespace CasCatalogue


namespace CategoryId
def sets : CategoryId := ⟨"cat.sets"⟩
def countableSets : CategoryId := ⟨"cat.countable_sets"⟩
def enumeratedSets : CategoryId := ⟨"cat.enumerated_sets"⟩
def partiallyOrderedSets : CategoryId := ⟨"cat.partially_ordered_sets"⟩
def totallyOrderedSets : CategoryId := ⟨"cat.totally_ordered_sets"⟩
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
def partiallyOrderedToSets : FunctorId := ⟨"fun.sets.partially_ordered_to_sets"⟩
def totallyOrderedToSets : FunctorId := ⟨"fun.sets.totally_ordered_to_sets"⟩
end FunctorId

end CasCatalogue
