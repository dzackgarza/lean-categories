module

public import LeanCategories.Catalogue.Id

@[expose] public section

namespace LeanCategories

namespace CategoryId
def sets : CategoryId := ⟨"cat.sets"⟩
end CategoryId

namespace ClassifierId
def setsFinite : ClassifierId := ⟨"clf.sets.finite"⟩
def setsGraded : ClassifierId := ⟨"clf.sets.graded"⟩
def setsBinaryOperation : ClassifierId := ⟨"clf.sets.binary_operation"⟩
end ClassifierId

namespace FunctorId
def setsIdentity : FunctorId := ⟨"fun.sets.identity"⟩
end FunctorId

end LeanCategories
