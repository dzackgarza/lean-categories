module

public import LeanCategories.Catalogue.Id

@[expose] public section

namespace LeanCategories

namespace CategoryId
def modulesR : CategoryId := ⟨"cat.modules_r"⟩
def finitelyGeneratedModules : CategoryId := ⟨"cat.finitelygeneratedmodules"⟩
def finiteRankModules : CategoryId := ⟨"cat.finiterankmodules"⟩
def freeModules : CategoryId := ⟨"cat.freemodules"⟩
end CategoryId

namespace ClassifierId
def modulesFree : ClassifierId := ⟨"clf.modules_free"⟩
def modulesFinitelyGenerated : ClassifierId := ⟨"clf.modules_finitelygenerated"⟩
def modulesFiniteRank : ClassifierId := ⟨"clf.modules_finiterank"⟩
end ClassifierId

namespace CategoryFamilyId
def modules : CategoryFamilyId := ⟨"fam.modules"⟩
end CategoryFamilyId

namespace ParameterId
def r : ParameterId := ⟨"R"⟩
def s : ParameterId := ⟨"S"⟩
def w : ParameterId := ⟨"W"⟩
def wPrime : ParameterId := ⟨"W'"⟩
end ParameterId

namespace ParameterOperationId
def opposite : ParameterOperationId := ⟨"parameter.opposite"⟩
def tensorProduct : ParameterOperationId := ⟨"parameter.tensor_product"⟩
end ParameterOperationId

namespace ParameterKindId
def ringObject : ParameterKindId := ⟨"parameter-kind.ring-object"⟩
def commRingObject : ParameterKindId := ⟨"parameter-kind.comm-ring-object"⟩
def moduleObject : ParameterKindId := ⟨"parameter-kind.module-object"⟩
end ParameterKindId

namespace VarianceId
def restrictionOfScalarsContravariant : VarianceId :=
  ⟨"variance.restriction-of-scalars-contravariant"⟩
def discrete : VarianceId := ⟨"variance.discrete"⟩
end VarianceId

end LeanCategories
