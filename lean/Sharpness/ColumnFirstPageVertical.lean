import Sharpness.ColumnAssociatedGraded
import Sharpness.ColumnNatGradedComplexIso
import Sharpness.ComplexExtensionColimits

/-! The actual first page of the constructed column spectral sequence
is the native vertical cohomology of the actual p-th column. Extension
by zero preserves the actual cokernel, so the integer mapping-cone
construction and the natural-number quotient model are compared here. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness
open CategoryTheory CategoryTheory.Limits
variable {R : Type u} [CommRing R]
    (K : HomologicalComplex₂ (ModuleCat.{u} R) (ComplexShape.up ℕ) (ComplexShape.up ℕ))

set_option backward.isDefEq.respectTransparency false in
def totalColumnAssociatedGradedExtendIso (p : ℕ) :
    totalColumnAssociatedGraded K p ≅
      (totalColumnNatAssociatedGraded K p).extend ComplexShape.embeddingUpNat :=
  (PreservesCokernel.iso (ComplexShape.embeddingUpNat.extendFunctor (ModuleCat.{u} R))
    (totalColumnFilteredMap K (Nat.le_succ p))).symm

def totalColumnFirstPageVerticalIso (p q : ℕ) :
    ((totalColumnSpectralSequence K).page 1).X (p,q) ≅ (K.X p).homology q :=
  totalColumnFirstPageAssociatedGradedIso K p q ≪≫
    (HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℤ) ((p : ℤ)+q)).mapIso
      (totalColumnAssociatedGradedExtendIso K p) ≪≫
    (totalColumnNatAssociatedGraded K p).extendHomologyIso ComplexShape.embeddingUpNat
      (show ComplexShape.embeddingUpNat.f (p+q) = (p : ℤ)+q from by simp) ≪≫
        totalColumnNatGradedCohomologyIso K p q

end Sharpness
