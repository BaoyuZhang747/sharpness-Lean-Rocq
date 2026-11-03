import Sharpness.LinkingSubgroupAugmentation
import Sharpness.ReplacementAugmentationProjection

/-! The cochain-level augmentation formulas induce the actual
geometric restriction formulas on native cohomology. No invertibility
or identification with the spectral edge is asserted here. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness.FusionSystem.CentricLinkingSystem
open CategoryTheory
variable {S : Type u} [Group S] {F : FusionSystem S}
    (L : F.CentricLinkingSystem) (R : Type u) [CommRing R] (A : ModuleCat.{u} R)

def subgroupTotalProjection (P : F.CentricOrbit) :
    L.subgroupTotalCochains R A ⟶ SingularCohomology.cochains R (L.subgroupDiagram.obj P) A :=
  replacementTotalProjection (L.subgroupCochainDiagram R A) (ComposableArrows.mk₀ P)

theorem subgroupCochainAugmentation_comp_projection (P : F.CentricOrbit) :
    L.subgroupCochainAugmentation R A ≫ L.subgroupTotalProjection R A P =
      SingularCohomology.cochainPull R (L.subgroupDiagramForget P) A :=
  replacementConeAugmentation_comp_projection (L.subgroupCochainDiagram R A)
    (L.subgroupCochainRestrictionCone R A) (ComposableArrows.mk₀ P)

theorem subgroupAugmentationCohomology_component (P : F.CentricOrbit) (n : ℕ) :
    HomologicalComplex.homologyMap (L.subgroupCochainAugmentation R A) n ≫
        HomologicalComplex.homologyMap (L.subgroupTotalProjection R A P) n =
      SingularCohomology.pull R (L.subgroupDiagramForget P) A n :=
  (HomologicalComplex.homologyMap_comp _ _ n).symm.trans
    (congrArg (fun t => HomologicalComplex.homologyMap t n) (L.subgroupCochainAugmentation_comp_projection R A P))

end Sharpness.FusionSystem.CentricLinkingSystem
