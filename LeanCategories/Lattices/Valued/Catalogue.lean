module

public import LeanCategories.Catalogue.Id

@[expose] public section

namespace LeanCategories

namespace CategoryId

def lattice : CategoryId := ⟨"cat.lattice"⟩
def finiteProjectiveLattice : CategoryId := ⟨"cat.finite_projective_lattice"⟩
def finiteFreeLattice : CategoryId := ⟨"cat.finite_free_lattice"⟩
def evenLattice : CategoryId := ⟨"cat.even_lattice"⟩
def definiteLattice : CategoryId := ⟨"cat.definite_lattice"⟩
def indefiniteLattice : CategoryId := ⟨"cat.indefinite_lattice"⟩

end CategoryId

namespace CategoryFamilyId

def lattice : CategoryFamilyId := ⟨"fam.lattice"⟩
def finiteProjectiveLattice : CategoryFamilyId := ⟨"fam.finite_projective_lattice"⟩
def finiteFreeLattice : CategoryFamilyId := ⟨"fam.finite_free_lattice"⟩
def evenLattice : CategoryFamilyId := ⟨"fam.even_lattice"⟩

end CategoryFamilyId

namespace FunctorId

def latticeChangeValue : FunctorId := ⟨"fun.lattice.change_value"⟩
def latticeBaseChange : FunctorId := ⟨"fun.lattice.base_change"⟩
def finiteProjectiveForget : FunctorId := ⟨"fun.finite_projective_lattice.forget"⟩

end FunctorId

end LeanCategories
