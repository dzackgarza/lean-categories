module

public import LeanCategories.Catalogue.Id

@[expose] public section

namespace LeanCategories

namespace CategoryId
def modulesR : CategoryId := ⟨"cat.modules_r"⟩
def finitelyGeneratedModules : CategoryId := ⟨"cat.finitelygeneratedmodules"⟩
def finiteRankModules : CategoryId := ⟨"cat.finiterankmodules"⟩
def freeModules : CategoryId := ⟨"cat.freemodules"⟩
def genFrame : CategoryId := ⟨"cat.gen_frame"⟩
def basisFrame : CategoryId := ⟨"cat.basis_frame"⟩
def coord : CategoryId := ⟨"cat.coord"⟩
end CategoryId

namespace ClassifierId
def modulesFree : ClassifierId := ⟨"clf.modules_free"⟩
def modulesFinitelyGenerated : ClassifierId := ⟨"clf.modules_finitelygenerated"⟩
def modulesFiniteRank : ClassifierId := ⟨"clf.modules_finiterank"⟩
end ClassifierId

namespace CategoryFamilyId
def modules : CategoryFamilyId := ⟨"fam.modules"⟩
def genFrame : CategoryFamilyId := ⟨"fam.gen_frame"⟩
def basisFrame : CategoryFamilyId := ⟨"fam.basis_frame"⟩
def coord : CategoryFamilyId := ⟨"fam.coord"⟩

end CategoryFamilyId

namespace FunctorId
def basisFrameToGenFrame : FunctorId := ⟨"fun.basis_frame.to_gen_frame"⟩
def fromBasisFrame : FunctorId := ⟨"fun.coord.from_basis_frame"⟩
def coordForget : FunctorId := ⟨"fun.coord.forget"⟩
end FunctorId

end LeanCategories
