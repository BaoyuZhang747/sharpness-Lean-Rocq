import Sharpness.EilenbergZilberInput
import Sharpness.NormalizerSingularLinearization
import Sharpness.NormalizerChainsProjective
import Sharpness.NormalizerTotalDualCochain
import Sharpness.ChainDualProjectiveQuasiIso

/-! The uniform Alexander–Whitney theorem is applied to the actual
normalizer bisimplicial singular replacement and transported through
the proved actual total linearization. Its actual cochain dual is a
quasi-isomorphism for every module A by proved degreewise projectivity.
No geometric augmentation quasi-isomorphism is asserted here. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness.FusionSystem.CentricLinkingSystem.LibmanNormalizerInput
open CategoryTheory
variable {S : Type u} [Group S] [Finite S] {F : FusionSystem S}
    {L : F.CentricLinkingSystem} {p : ℕ} [Fact p.Prime]
    {hS : IsPGroup p S} {sat : F.Saturated p}
    (I : L.LibmanNormalizerInput p hS sat) (R : Type u) [CommRing R]
    (ez : EilenbergZilberInput.{u} R)

def normalizerAlexanderWhitney :
    I.normalizerSingularDiagonal.chainComplex (ModuleCat.of R R) ⟶ I.normalizerTotalChains R :=
  ez.alexanderWhitney I.normalizerSingularReplacement ≫ (I.normalizerSingularTotalLinearizationIso R).inv

theorem normalizerAlexanderWhitney_quasiIso : QuasiIso (I.normalizerAlexanderWhitney R ez) := by
  letI : QuasiIso (ez.alexanderWhitney I.normalizerSingularReplacement) := ez.Weibel_8_5_1 _
  exact inferInstanceAs (QuasiIso
    (ez.alexanderWhitney I.normalizerSingularReplacement ≫ (I.normalizerSingularTotalLinearizationIso R).inv))

def normalizerAlexanderWhitneyCochainMap (A : ModuleCat.{u} R) :
    I.normalizerTotalCochains R A ⟶
      ChainComplex.linearYonedaObj (I.normalizerSingularDiagonal.chainComplex (ModuleCat.of R R)) R A :=
  (I.normalizerTotalDualCochainIso R A).hom ≫
    SingularCohomology.chainDualMap R (I.normalizerAlexanderWhitney R ez) A

theorem normalizerAlexanderWhitneyCochainMap_quasiIso (A : ModuleCat.{u} R) :
    QuasiIso (I.normalizerAlexanderWhitneyCochainMap R ez A) := by
  letI : ∀ n, Projective ((I.normalizerSingularDiagonal.chainComplex (ModuleCat.of R R)).X n) :=
    I.normalizerSingularDiagonalChains_projective R
  letI : ∀ n, Projective ((I.normalizerTotalChains R).X n) := I.normalizerTotalChains_projective R
  letI := I.normalizerAlexanderWhitney_quasiIso R ez
  letI := SingularCohomology.chainDualMap_quasiIso_of_projective R A (I.normalizerAlexanderWhitney R ez)
  exact inferInstanceAs (QuasiIso ((I.normalizerTotalDualCochainIso R A).hom ≫
    SingularCohomology.chainDualMap R (I.normalizerAlexanderWhitney R ez) A))

def normalizerAlexanderWhitneyCohomologyIso (A : ModuleCat.{u} R) (n : ℕ) :
    (I.normalizerTotalCochains R A).homology n ≅
      (ChainComplex.linearYonedaObj
        (I.normalizerSingularDiagonal.chainComplex (ModuleCat.of R R)) R A).homology n := by
  letI := I.normalizerAlexanderWhitneyCochainMap_quasiIso R ez A
  exact asIso (HomologicalComplex.homologyMap (I.normalizerAlexanderWhitneyCochainMap R ez A) n)

end Sharpness.FusionSystem.CentricLinkingSystem.LibmanNormalizerInput
