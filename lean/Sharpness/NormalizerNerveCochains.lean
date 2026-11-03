import Sharpness.NormalizerNerveReplacement
import Sharpness.NormalizerAugmentationDual

/-! The actual nerve/singular comparison square after Hom_R(-,A),
including the manuscript's existing geometric cochain augmentation.
All arrows are the actual constructed maps. No unit or diagonal
quasi-isomorphism is an input to these identities. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace Sharpness.FusionSystem.CentricLinkingSystem.LibmanNormalizerInput
open CategoryTheory
variable {S : Type u} [Group S] [Finite S] {F : FusionSystem S}
    {L : F.CentricLinkingSystem} {p : ℕ} [Fact p.Prime]
    {hS : IsPGroup p S} {sat : F.Saturated p}
    (I : L.LibmanNormalizerInput p hS sat) (R : Type u) [CommRing R] (A : ModuleCat.{u} R)

def normalizerNerveUnitCochainMap :
    ChainComplex.linearYonedaObj (I.normalizerSingularDiagonal.chainComplex (ModuleCat.of R R)) R A ⟶
      ChainComplex.linearYonedaObj (I.normalizerNerveDiagonal.chainComplex (ModuleCat.of R R)) R A :=
  SingularCohomology.chainDualMap R (I.normalizerNerveUnitChainMap R) A

def normalizerNerveDiagonalCochainAugmentation :
    ChainComplex.linearYonedaObj ((CategoryTheory.nerve L.Object).chainComplex (ModuleCat.of R R)) R A ⟶
      ChainComplex.linearYonedaObj (I.normalizerNerveDiagonal.chainComplex (ModuleCat.of R R)) R A :=
  SingularCohomology.chainDualMap R (I.normalizerNerveDiagonalChainAugmentation R) A

def normalizerRealizationUnitCochainMap : SingularCohomology.cochains R L.classifyingSpace A ⟶
    ChainComplex.linearYonedaObj ((CategoryTheory.nerve L.Object).chainComplex (ModuleCat.of R R)) R A :=
  SingularCohomology.chainDualMap R (I.normalizerRealizationUnitChainMap R) A

theorem normalizerNerveUnitCochainMap_augmentation :
    SingularCohomology.chainDualMap R (I.normalizerSingularDiagonalChainMap R) A ≫
        I.normalizerNerveUnitCochainMap R A =
      I.normalizerRealizationUnitCochainMap R A ≫ I.normalizerNerveDiagonalCochainAugmentation R A := by
  change SingularCohomology.chainDualMap R (I.normalizerSingularDiagonalChainMap R) A ≫
      SingularCohomology.chainDualMap R (I.normalizerNerveUnitChainMap R) A =
    SingularCohomology.chainDualMap R (I.normalizerRealizationUnitChainMap R) A ≫
      SingularCohomology.chainDualMap R (I.normalizerNerveDiagonalChainAugmentation R) A
  rw [← SingularCohomology.chainDualMap_comp, ← SingularCohomology.chainDualMap_comp,
    normalizerNerveUnitChainMap_augmentation]

theorem normalizerCochainAugmentation_nerveUnit (ez : EilenbergZilberInput.{u} R) :
    I.normalizerCochainAugmentation R A ≫ I.normalizerAlexanderWhitneyCochainMap R ez A ≫
        I.normalizerNerveUnitCochainMap R A =
      I.normalizerRealizationUnitCochainMap R A ≫ I.normalizerNerveDiagonalCochainAugmentation R A := by
  rw [← Category.assoc, normalizerCochainAugmentation_alexanderWhitney,
    normalizerNerveUnitCochainMap_augmentation]

theorem normalizerNerveDiagonalChains_projective (n : ℕ) :
    Projective ((I.normalizerNerveDiagonal.chainComplex (ModuleCat.of R R)).X n) :=
  SingularCohomology.simplicialChains_projective R I.normalizerNerveDiagonal n

theorem normalizerNerveClassifyingChains_projective (n : ℕ) :
    Projective (((CategoryTheory.nerve L.Object).chainComplex (ModuleCat.of R R)).X n) :=
  SingularCohomology.simplicialChains_projective R (CategoryTheory.nerve L.Object) n

end Sharpness.FusionSystem.CentricLinkingSystem.LibmanNormalizerInput
