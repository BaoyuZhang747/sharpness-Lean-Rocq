import Sharpness.AlternatingFaceChainDual
import Sharpness.CategoryChainReplacementTotal
import Sharpness.CategoryChainReplacementDual

/-! The actual dual chain replacement bicomplex is isomorphic to the
manuscript's cochain replacement bicomplex, including horizontal and
vertical differentials. Native totalization preserves this proved
bicomplex isomorphism. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness
open CategoryTheory
variable {R C : Type u} [CommRing R] [Category.{u} C]
    (D : C ⥤ ChainComplex (ModuleCat.{u} R) ℕ) (A : ModuleCat.{u} R)

def chainReplacementBicomplexDualIso :
    dualNatBicomplex (chainReplacementBicomplex D) A ≅
      cochainReplacementBicomplex (D.op ⋙ SingularCohomology.chainDualFunctor R A) :=
  alternatingFaceChainDualIso (chainReplacement D) A ≪≫
    (AlgebraicTopology.alternatingCofaceMapComplex (CochainComplex (ModuleCat.{u} R) ℕ)).mapIso
      (chainReplacementDualIso D A)

def chainReplacementDualBicomplexTotalIso :
    (dualNatBicomplex (chainReplacementBicomplex D) A).total (ComplexShape.up ℕ) ≅
      cochainReplacementTotal (D.op ⋙ SingularCohomology.chainDualFunctor R A) :=
  HomologicalComplex₂.total.mapIso (chainReplacementBicomplexDualIso D A) (ComplexShape.up ℕ)

end Sharpness
