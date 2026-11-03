import Sharpness.Unconditional.CanonicalRealizationUnitInput
import Sharpness.Unconditional.NormalizerNativeAugmentation
import Sharpness.Unconditional.NormalizerHigherLimitComparisonCohomology
import Sharpness.ReplacementAugmentationProjection

/-! Unconditional actual canonical normalizer augmentations and the actual
group-cohomology diagram comparison. Every map remains the specified native
map. Inverse-limit edge invertibility and higher-limit vanishing are separate. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace Sharpness.FusionSystem.CentricLinkingSystem
open CategoryTheory
variable {S : Type u} [Group S] [Finite S] {F : FusionSystem S}
    (L : F.CentricLinkingSystem) (R : Type u) [CommRing R]

def normalizerOrdinaryDiagramIso_unconditional (A : ModuleCat.{u} R) (n : ℕ) :
    L.canonicalLibmanNormalizerData.cohomologyDiagram R A n ≅
      L.normalizerOrdinaryDiagram R A n :=
  L.normalizerOrdinaryDiagramIso R A (canonicalRealizationUnitInput R) n

def normalizerOrdinaryHigherLimitIso_unconditional (A : ModuleCat.{u} R) (n k : ℕ) :
    higherLimit (L.canonicalLibmanNormalizerData.cohomologyDiagram R A n) k ≅
      higherLimit (L.normalizerOrdinaryDiagram R A n) k :=
  L.normalizerOrdinaryHigherLimitIso R A (canonicalRealizationUnitInput R) n k

variable (p : ℕ) [Fact p.Prime] (hS : IsPGroup p S) (sat : F.Saturated p)

theorem canonicalNormalizerSingularDiagonalChainMap_quasiIso :
    QuasiIso ((L.canonicalLibmanNormalizerInput p hS sat).normalizerSingularDiagonalChainMap R) :=
  (L.canonicalLibmanNormalizerInput p hS sat).normalizerSingularDiagonalChainMap_quasiIso_of_realizationUnit
    R (canonicalRealizationUnitInput R)

theorem canonicalNormalizerChainAugmentation_quasiIso_unconditional :
    QuasiIso ((L.canonicalLibmanNormalizerInput p hS sat).normalizerChainAugmentation R) :=
  L.canonicalNormalizerChainAugmentation_quasiIso_of_realizationUnit p hS sat R
    (canonicalRealizationUnitInput R)

theorem canonicalNormalizerCochainAugmentation_quasiIso_unconditional (A : ModuleCat.{u} R) :
    QuasiIso ((L.canonicalLibmanNormalizerInput p hS sat).cochainAugmentation R A) :=
  L.canonicalNormalizerCochainAugmentation_quasiIso_of_realizationUnit p hS sat R A
    (canonicalRealizationUnitInput R)

def normalizerDecompositionHomologyIso (n : ℕ) :
    ((L.canonicalLibmanNormalizerInput p hS sat).normalizerTotalChains R).homology n ≅
      ((SingularCohomology.chainsFunctor R).obj L.classifyingSpace).homology n := by
  letI := L.canonicalNormalizerChainAugmentation_quasiIso_unconditional R p hS sat
  exact asIso (HomologicalComplex.homologyMap
    ((L.canonicalLibmanNormalizerInput p hS sat).normalizerChainAugmentation R) n)

theorem normalizerDecompositionHomologyIso_hom (n : ℕ) :
    (L.normalizerDecompositionHomologyIso R p hS sat n).hom =
      HomologicalComplex.homologyMap
        ((L.canonicalLibmanNormalizerInput p hS sat).normalizerChainAugmentation R) n := rfl

def normalizerDecompositionCohomologyIso (A : ModuleCat.{u} R) (n : ℕ) :
    SingularCohomology.cohomology R L.classifyingSpace A n ≅
      (L.canonicalLibmanNormalizerData.totalCochains R A).homology n :=
  L.canonicalNormalizerAugmentationCohomologyIso_of_realizationUnit p hS sat R A
    (canonicalRealizationUnitInput R) n

theorem normalizerDecompositionCohomologyIso_hom (A : ModuleCat.{u} R) (n : ℕ) :
    (L.normalizerDecompositionCohomologyIso R p hS sat A n).hom =
      HomologicalComplex.homologyMap
        ((L.canonicalLibmanNormalizerInput p hS sat).cochainAugmentation R A) n := rfl

def normalizerDecompositionTotalProjection (A : ModuleCat.{u} R) (d : F.NormalizerCategory) :
    L.canonicalLibmanNormalizerData.totalCochains R A ⟶
      SingularCohomology.cochains R (L.canonicalLibmanNormalizerData.diagram.obj d) A :=
  replacementTotalProjection (L.canonicalLibmanNormalizerData.cochainDiagram R A)
    (ComposableArrows.mk₀ d)

theorem canonicalNormalizerCochainAugmentation_comp_projection
    (A : ModuleCat.{u} R) (d : F.NormalizerCategory) :
    (L.canonicalLibmanNormalizerInput p hS sat).cochainAugmentation R A ≫
        L.normalizerDecompositionTotalProjection R A d =
      SingularCohomology.cochainPull R ((L.canonicalLibmanNormalizerInput p hS sat).forgetMap d) A :=
  replacementConeAugmentation_comp_projection
    (L.canonicalLibmanNormalizerData.cochainDiagram R A)
    ((L.canonicalLibmanNormalizerInput p hS sat).cochainRestrictionCone R A)
    (ComposableArrows.mk₀ d)

theorem normalizerDecompositionCohomologyIso_component
    (A : ModuleCat.{u} R) (d : F.NormalizerCategory) (n : ℕ) :
    (L.normalizerDecompositionCohomologyIso R p hS sat A n).hom ≫
        HomologicalComplex.homologyMap (L.normalizerDecompositionTotalProjection R A d) n =
      SingularCohomology.pull R ((L.canonicalLibmanNormalizerInput p hS sat).forgetMap d) A n :=
  (HomologicalComplex.homologyMap_comp _ _ n).symm.trans
    (congrArg (fun f => HomologicalComplex.homologyMap f n)
      (L.canonicalNormalizerCochainAugmentation_comp_projection R p hS sat A d))

end Sharpness.FusionSystem.CentricLinkingSystem
