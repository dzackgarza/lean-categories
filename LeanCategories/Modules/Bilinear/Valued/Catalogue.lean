module

public import LeanCategories.Catalogue.Id

@[expose] public section

namespace LeanCategories

namespace CategoryId

def bilinModule : CategoryId := ⟨"cat.bilin_module"⟩
def bilWForm : CategoryId := ⟨"cat.bil_wform"⟩

end CategoryId

namespace FunctorId

def bilinModuleForget : FunctorId := ⟨"fun.bilin_module.forget"⟩
def bilWFormBaseChange : FunctorId := ⟨"fun.bil_wform.base_change"⟩
def bilinModuleChangeValue : FunctorId := ⟨"fun.bilin_module.change_value"⟩
def bilinModuleBaseChange : FunctorId := ⟨"fun.bilin_module.base_change"⟩

end FunctorId

end LeanCategories
