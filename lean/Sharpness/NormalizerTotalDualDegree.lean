import Sharpness.NormalizerChainReplacement
import Sharpness.CategoryChainReplacementBicomplexDual
import Sharpness.TotalDualDegreeIso

/-! Actual normalizer cochain totalization in every total degree is the
dual of the constructed normalizer total chain module. The bicomplex
comparison includes both differentials. Compatibility of these
degreewise dual isomorphisms with the total differential remains a
separate obligation. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness.FusionSystem.CentricLinkingSystem.LibmanNormalizerInput
open CategoryTheory
variable {S : Type u} [Group S] [Finite S] {F : FusionSystem S}
    {L : F.CentricLinkingSystem} {p : ℕ} [Fact p.Prime]
    {hS : IsPGroup p S} {sat : F.Saturated p}
    (I : L.LibmanNormalizerInput p hS sat) (R : Type u) [CommRing R] (A : ModuleCat.{u} R)

set_option backward.isDefEq.respectTransparency false in
def normalizerBicomplexDualIso :
    dualNatBicomplex (I.normalizerChainBicomplex R) A ≅ I.normalizerBicomplex R A :=
  chainReplacementBicomplexDualIso (I.normalizerChainDiagram R) A

def normalizerDualBicomplexTotalIso :
    (dualNatBicomplex (I.normalizerChainBicomplex R) A).total (ComplexShape.up ℕ) ≅ I.normalizerTotalCochains R A :=
  HomologicalComplex₂.total.mapIso (I.normalizerBicomplexDualIso R A) (ComplexShape.up ℕ)

def normalizerTotalDualDegreeIso (n : ℕ) :
    (I.normalizerTotalCochains R A).X n ≅ ModuleCat.of R ((I.normalizerTotalChains R).X n ⟶ A) :=
  (HomologicalComplex.Hom.isoApp (I.normalizerDualBicomplexTotalIso R A) n).symm ≪≫
    totalDualDegreeIso (I.normalizerChainBicomplex R) A n

end Sharpness.FusionSystem.CentricLinkingSystem.LibmanNormalizerInput
