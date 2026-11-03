import Sharpness.Unconditional.NativeCostructuredAugmentation
import Sharpness.Unconditional.CanonicalLibmanNormalizerInput
import Sharpness.NormalizerNerveAugmentationQuasiIso

/-! Native normalizer augmentations via the actual comma diagonal and actual
evaluation map. Canonical wrappers use the proved Libman construction. Only
the realization-unit theorem remains for the singular/cochain conclusions. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace Sharpness.FusionSystem.CentricLinkingSystem.LibmanNormalizerInput
open CategoryTheory
variable {S : Type u} [Group S] [Finite S] {F : FusionSystem S}
    {L : F.CentricLinkingSystem} {p : ℕ} [Fact p.Prime]
    {hS : IsPGroup p S} {sat : F.Saturated p}
    (I : L.LibmanNormalizerInput p hS sat) (R : Type u) [CommRing R]

theorem evaluationChainMap_quasiIso_native :
    QuasiIso ((simplicialChainsFunctor R).map (CategoryTheory.nerveMap I.evaluation)) := by
  letI : QuasiIso ((simplicialChainsFunctor R).map
      (CategoryTheory.nerveMap (CostructuredArrow.grothendieckProj I.projection))) :=
    nerveAdjunction_right_quasiIso (costructuredGrothendieckAdjunction I.projection)
      (ModuleCat.of R R)
  have h := I.Libman_5_1_1_Weibel R
  change QuasiIso ((simplicialChainsFunctor R).map
    (CategoryTheory.nerveMap (CostructuredArrow.grothendieckProj I.projection) ≫
      CategoryTheory.nerveMap I.evaluation)) at h
  rw [(simplicialChainsFunctor R).map_comp] at h
  letI := h
  exact quasiIso_of_comp_left
    ((simplicialChainsFunctor R).map
      (CategoryTheory.nerveMap (CostructuredArrow.grothendieckProj I.projection))) _

theorem normalizerNerveDiagonalAugmentation_comma :
    I.normalizerNerveDiagonalAugmentation =
      simplicialReplacementDiagonalAugmentation (costructuredNerveDiagram I.projection)
        (costructuredNerveCocone I.projection) ≫ CategoryTheory.nerveMap I.evaluation := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.ext_apply
  rintro ⟨s, x⟩
  rfl

theorem normalizerNerveDiagonalChainAugmentation_quasiIso_native :
    QuasiIso (I.normalizerNerveDiagonalChainAugmentation R) := by
  letI := costructuredDiagonalAugmentation_quasiIso_native R I.projection
  letI := I.evaluationChainMap_quasiIso_native R
  change QuasiIso ((simplicialChainsFunctor R).map I.normalizerNerveDiagonalAugmentation)
  rw [I.normalizerNerveDiagonalAugmentation_comma, (simplicialChainsFunctor R).map_comp]
  infer_instance

theorem normalizerNerveDiagonalCochainAugmentation_quasiIso_native (A : ModuleCat.{u} R) :
    QuasiIso (I.normalizerNerveDiagonalCochainAugmentation R A) := by
  letI (n : ℕ) : Projective ((I.normalizerNerveDiagonal.chainComplex (ModuleCat.of R R)).X n) :=
    I.normalizerNerveDiagonalChains_projective R n
  letI (n : ℕ) : Projective (((CategoryTheory.nerve L.Object).chainComplex (ModuleCat.of R R)).X n) :=
    SingularCohomology.simplicialChains_projective R (CategoryTheory.nerve L.Object) n
  letI := I.normalizerNerveDiagonalChainAugmentation_quasiIso_native R
  exact SingularCohomology.chainDualMap_quasiIso_of_projective R A
    (I.normalizerNerveDiagonalChainAugmentation R)

theorem normalizerSingularDiagonalChainMap_quasiIso_of_realizationUnit
    (real : RealizationUnitInput.{u} R) :
    QuasiIso (I.normalizerSingularDiagonalChainMap R) := by
  letI := I.normalizerNerveUnitChainMap_quasiIso R real
    (canonicalReplacementHomologyInvarianceInput R)
  letI := I.normalizerNerveDiagonalChainAugmentation_quasiIso_native R
  letI : QuasiIso (I.normalizerRealizationUnitChainMap R) :=
    real.May_16_2_Weibel_3_6_1 (CategoryTheory.nerve L.Object)
  haveI : QuasiIso (I.normalizerNerveUnitChainMap R ≫ I.normalizerSingularDiagonalChainMap R) := by
    rw [I.normalizerNerveUnitChainMap_augmentation R]
    infer_instance
  exact quasiIso_of_comp_left (I.normalizerNerveUnitChainMap R) _

theorem normalizerChainAugmentation_quasiIso_of_realizationUnit
    (real : RealizationUnitInput.{u} R) : QuasiIso (I.normalizerChainAugmentation R) :=
  (I.normalizerChainAugmentation_quasiIso_iff_diagonal R (canonicalEilenbergZilberInput R)).mpr
    (I.normalizerSingularDiagonalChainMap_quasiIso_of_realizationUnit R real)

theorem cochainAugmentation_quasiIso_of_realizationUnit
    (A : ModuleCat.{u} R) (real : RealizationUnitInput.{u} R) :
    QuasiIso (I.cochainAugmentation R A) := by
  let ez := canonicalEilenbergZilberInput R
  letI := I.normalizerAlexanderWhitneyCochainMap_quasiIso R ez A
  letI := I.normalizerNerveUnitCochainMap_quasiIso R A real
    (canonicalReplacementHomologyInvarianceInput R)
  letI := I.normalizerNerveDiagonalCochainAugmentation_quasiIso_native R A
  letI := I.normalizerRealizationUnitCochainMap_quasiIso R A real
  have h : QuasiIso (I.cochainAugmentation R A ≫
      (I.normalizerAlexanderWhitneyCochainMap R ez A ≫ I.normalizerNerveUnitCochainMap R A)) := by
    rw [I.normalizerCochainAugmentation_nerveUnit R A ez]
    infer_instance
  exact (quasiIso_iff_comp_right (I.cochainAugmentation R A)
    (I.normalizerAlexanderWhitneyCochainMap R ez A ≫ I.normalizerNerveUnitCochainMap R A)).mp h

def augmentationCohomologyIso_of_realizationUnit
    (A : ModuleCat.{u} R) (real : RealizationUnitInput.{u} R) (n : ℕ) :
    SingularCohomology.cohomology R L.classifyingSpace A n ≅
      (I.toLibmanNormalizerData.totalCochains R A).homology n := by
  letI := I.cochainAugmentation_quasiIso_of_realizationUnit R A real
  exact asIso (HomologicalComplex.homologyMap (I.cochainAugmentation R A) n)

theorem augmentationCohomologyIso_of_realizationUnit_hom
    (A : ModuleCat.{u} R) (real : RealizationUnitInput.{u} R) (n : ℕ) :
    (I.augmentationCohomologyIso_of_realizationUnit R A real n).hom =
      HomologicalComplex.homologyMap (I.cochainAugmentation R A) n := rfl

end Sharpness.FusionSystem.CentricLinkingSystem.LibmanNormalizerInput

namespace Sharpness.FusionSystem.CentricLinkingSystem
open CategoryTheory
variable {S : Type u} [Group S] [Finite S] {F : FusionSystem S}
    (L : F.CentricLinkingSystem) (p : ℕ) [Fact p.Prime]
    (hS : IsPGroup p S) (sat : F.Saturated p) (R : Type u) [CommRing R]

theorem canonicalNormalizerNerveDiagonalChainAugmentation_quasiIso :
    QuasiIso ((L.canonicalLibmanNormalizerInput p hS sat).normalizerNerveDiagonalChainAugmentation R) :=
  (L.canonicalLibmanNormalizerInput p hS sat).normalizerNerveDiagonalChainAugmentation_quasiIso_native R

theorem canonicalNormalizerChainAugmentation_quasiIso_of_realizationUnit
    (real : RealizationUnitInput.{u} R) :
    QuasiIso ((L.canonicalLibmanNormalizerInput p hS sat).normalizerChainAugmentation R) :=
  (L.canonicalLibmanNormalizerInput p hS sat).normalizerChainAugmentation_quasiIso_of_realizationUnit R real

theorem canonicalNormalizerCochainAugmentation_quasiIso_of_realizationUnit
    (A : ModuleCat.{u} R) (real : RealizationUnitInput.{u} R) :
    QuasiIso ((L.canonicalLibmanNormalizerInput p hS sat).cochainAugmentation R A) :=
  (L.canonicalLibmanNormalizerInput p hS sat).cochainAugmentation_quasiIso_of_realizationUnit R A real

def canonicalNormalizerAugmentationCohomologyIso_of_realizationUnit
    (A : ModuleCat.{u} R) (real : RealizationUnitInput.{u} R) (n : ℕ) :
    SingularCohomology.cohomology R L.classifyingSpace A n ≅
      (L.canonicalLibmanNormalizerData.totalCochains R A).homology n :=
  (L.canonicalLibmanNormalizerInput p hS sat).augmentationCohomologyIso_of_realizationUnit R A real n

theorem canonicalNormalizerAugmentationCohomologyIso_of_realizationUnit_hom
    (A : ModuleCat.{u} R) (real : RealizationUnitInput.{u} R) (n : ℕ) :
    (L.canonicalNormalizerAugmentationCohomologyIso_of_realizationUnit p hS sat R A real n).hom =
      HomologicalComplex.homologyMap
        ((L.canonicalLibmanNormalizerInput p hS sat).cochainAugmentation R A) n := rfl

end Sharpness.FusionSystem.CentricLinkingSystem
