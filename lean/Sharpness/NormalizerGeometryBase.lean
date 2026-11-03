import Sharpness.NormalizerGeometricRestriction

/-! Reducible names for the already fixed normalizer objects. They
retain the existing coefficient diagram, total, forgetful maps, and
geometric augmentation literally while the proved chain comparison
machinery is instantiated for this actual comma model. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness.FusionSystem.CentricLinkingSystem.LibmanNormalizerInput
open CategoryTheory
variable {S : Type u} [Group S] [Finite S] {F : FusionSystem S}
    {L : F.CentricLinkingSystem} {p : ℕ} [Fact p.Prime]
    {hS : IsPGroup p S} {sat : F.Saturated p}
    (I : L.LibmanNormalizerInput p hS sat)

abbrev normalizerCategoryDiagram := I.toLibmanNormalizerData.categoryDiagram
abbrev normalizerDiagram := I.toLibmanNormalizerData.diagram
abbrev normalizerDiagramForget := I.forgetMap

theorem normalizerDiagramForget_naturality {d e : F.NormalizerCategory} (a : d ⟶ e) :
    I.normalizerDiagram.map a ≫ I.normalizerDiagramForget e = I.normalizerDiagramForget d :=
  I.forgetMap_naturality a

variable (R : Type u) [CommRing R] (A : ModuleCat.{u} R)

abbrev normalizerCochainDiagram := I.toLibmanNormalizerData.cochainDiagram R A
abbrev normalizerBicomplex := I.toLibmanNormalizerData.bicomplex R A
abbrev normalizerTotalCochains := I.toLibmanNormalizerData.totalCochains R A
abbrev normalizerCochainRestrictionCone := I.cochainRestrictionCone R A
abbrev normalizerCochainAugmentation := I.cochainAugmentation R A

end Sharpness.FusionSystem.CentricLinkingSystem.LibmanNormalizerInput
