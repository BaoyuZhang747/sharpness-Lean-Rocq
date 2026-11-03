import Sharpness.LinkingSubgroupChainReplacement
import Sharpness.CategoryChainReplacementBicomplexDual
import Sharpness.TotalDualDegreeIso

/-! Actual subgroup cochain totalization in every total degree is the
dual of the constructed subgroup total chain module. The bicomplex
comparison includes both differentials. Compatibility of these
degreewise dual isomorphisms with the total differential remains a
separate obligation. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness.FusionSystem.CentricLinkingSystem
open CategoryTheory
variable {S : Type u} [Group S] {F : FusionSystem S}
    (L : F.CentricLinkingSystem) (R : Type u) [CommRing R] (A : ModuleCat.{u} R)

set_option backward.isDefEq.respectTransparency false in
def subgroupBicomplexDualIso :
    dualNatBicomplex (L.subgroupChainBicomplex R) A ≅ L.subgroupBicomplex R A :=
  chainReplacementBicomplexDualIso (L.subgroupChainDiagram R) A

def subgroupDualBicomplexTotalIso :
    (dualNatBicomplex (L.subgroupChainBicomplex R) A).total (ComplexShape.up ℕ) ≅ L.subgroupTotalCochains R A :=
  HomologicalComplex₂.total.mapIso (L.subgroupBicomplexDualIso R A) (ComplexShape.up ℕ)

def subgroupTotalDualDegreeIso (n : ℕ) :
    (L.subgroupTotalCochains R A).X n ≅ ModuleCat.of R ((L.subgroupTotalChains R).X n ⟶ A) :=
  (HomologicalComplex.Hom.isoApp (L.subgroupDualBicomplexTotalIso R A) n).symm ≪≫
    totalDualDegreeIso (L.subgroupChainBicomplex R) A n

end Sharpness.FusionSystem.CentricLinkingSystem
