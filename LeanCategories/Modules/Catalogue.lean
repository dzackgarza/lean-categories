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

end LeanCategories
