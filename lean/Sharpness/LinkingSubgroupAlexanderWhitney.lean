import Sharpness.EilenbergZilberInput
import Sharpness.LinkingSubgroupSingularLinearization
import Sharpness.LinkingSubgroupChainsProjective
import Sharpness.LinkingSubgroupTotalDualCochain
import Sharpness.ChainDualProjectiveQuasiIso

/-! The uniform Alexander–Whitney theorem is applied to the actual
subgroup bisimplicial singular replacement and transported through
the proved actual total linearization. Its actual cochain dual is a
quasi-isomorphism for every module A by proved degreewise projectivity.
No geometric augmentation quasi-isomorphism is asserted here. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness.FusionSystem.CentricLinkingSystem
open CategoryTheory
variable {S : Type u} [Group S] {F : FusionSystem S}
    (L : F.CentricLinkingSystem) (R : Type u) [CommRing R]
    (ez : EilenbergZilberInput.{u} R)

def subgroupAlexanderWhitney :
    L.subgroupSingularDiagonal.chainComplex (ModuleCat.of R R) ⟶ L.subgroupTotalChains R :=
  ez.alexanderWhitney L.subgroupSingularReplacement ≫ (L.subgroupSingularTotalLinearizationIso R).inv

theorem subgroupAlexanderWhitney_quasiIso : QuasiIso (L.subgroupAlexanderWhitney R ez) := by
  letI : QuasiIso (ez.alexanderWhitney L.subgroupSingularReplacement) := ez.Weibel_8_5_1 _
  exact inferInstanceAs (QuasiIso
    (ez.alexanderWhitney L.subgroupSingularReplacement ≫ (L.subgroupSingularTotalLinearizationIso R).inv))

def subgroupAlexanderWhitneyCochainMap (A : ModuleCat.{u} R) :
    L.subgroupTotalCochains R A ⟶
      ChainComplex.linearYonedaObj (L.subgroupSingularDiagonal.chainComplex (ModuleCat.of R R)) R A :=
  (L.subgroupTotalDualCochainIso R A).hom ≫
    SingularCohomology.chainDualMap R (L.subgroupAlexanderWhitney R ez) A

theorem subgroupAlexanderWhitneyCochainMap_quasiIso (A : ModuleCat.{u} R) :
    QuasiIso (L.subgroupAlexanderWhitneyCochainMap R ez A) := by
  letI : ∀ n, Projective ((L.subgroupSingularDiagonal.chainComplex (ModuleCat.of R R)).X n) :=
    L.subgroupSingularDiagonalChains_projective R
  letI : ∀ n, Projective ((L.subgroupTotalChains R).X n) := L.subgroupTotalChains_projective R
  letI := L.subgroupAlexanderWhitney_quasiIso R ez
  letI := SingularCohomology.chainDualMap_quasiIso_of_projective R A (L.subgroupAlexanderWhitney R ez)
  exact inferInstanceAs (QuasiIso ((L.subgroupTotalDualCochainIso R A).hom ≫
    SingularCohomology.chainDualMap R (L.subgroupAlexanderWhitney R ez) A))

def subgroupAlexanderWhitneyCohomologyIso (A : ModuleCat.{u} R) (n : ℕ) :
    (L.subgroupTotalCochains R A).homology n ≅
      (ChainComplex.linearYonedaObj
        (L.subgroupSingularDiagonal.chainComplex (ModuleCat.of R R)) R A).homology n := by
  letI := L.subgroupAlexanderWhitneyCochainMap_quasiIso R ez A
  exact asIso (HomologicalComplex.homologyMap (L.subgroupAlexanderWhitneyCochainMap R ez A) n)

end Sharpness.FusionSystem.CentricLinkingSystem
