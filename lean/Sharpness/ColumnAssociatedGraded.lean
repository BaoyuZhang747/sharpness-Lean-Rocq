import Sharpness.ColumnFilteredSpectralObject
import Sharpness.ColumnFilteredMonomorphisms
import Sharpness.MonoMappingConeCokernel

/-! The first page is the native cohomology of the actual associated
graded cochain complex. The comparison is induced by the canonical
mapping-cone projection to the cokernel of the adjacent inclusion. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness
open CategoryTheory CategoryTheory.Limits
variable {R : Type u} [CommRing R]
    (K : HomologicalComplex₂ (ModuleCat.{u} R) (ComplexShape.up ℕ) (ComplexShape.up ℕ))

def totalColumnAssociatedGraded (p : ℕ) : CochainComplex (ModuleCat.{u} R) ℤ :=
  cokernel ((totalColumnFiltrationIntFunctor K).map
    (homOfLE (show OrderDual.toDual (p+1) ≤ OrderDual.toDual p from Nat.le_succ p)))

set_option backward.isDefEq.respectTransparency false in
def totalColumnFirstPageAssociatedGradedIso (p q : ℕ) :
    ((totalColumnSpectralSequence K).page 1).X (p,q) ≅
      (totalColumnAssociatedGraded K p).homology ((p : ℤ)+q) := by
  let f := (totalColumnFiltrationIntFunctor K).map
    (homOfLE (show OrderDual.toDual (p+1) ≤ OrderDual.toDual p from Nat.le_succ p))
  letI : Mono f := totalColumnFilteredExtendedMap_mono K (Nat.le_succ p)
  exact totalColumnFirstPageIso K p q ≪≫ monoMappingConeCokernelCohomologyIso f ((p : ℤ)+q)

end Sharpness
