import Sharpness.Unconditional.CanonicalRealizationUnitInput
import Sharpness.Unconditional.SubgroupNativeAugmentation
import Sharpness.LinkingAugmentationCohomology
import Sharpness.LinkingAugmentationNaturality

/-! Unconditional actual subgroup decomposition augmentations, for arbitrary
commutative coefficients. These identify geometric cohomology with the actual
total cohomology; no assertion about an inverse-limit edge is made here. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace Sharpness.FusionSystem.CentricLinkingSystem
open CategoryTheory
variable {S : Type u} [Group S] {F : FusionSystem S}
    (L : F.CentricLinkingSystem) (R : Type u) [CommRing R]

theorem subgroupSingularDiagonalChainMap_quasiIso_unconditional :
    QuasiIso (L.subgroupSingularDiagonalChainMap R) :=
  L.subgroupSingularDiagonalChainMap_quasiIso_of_realizationUnit R (canonicalRealizationUnitInput R)

theorem subgroupChainAugmentation_quasiIso_unconditional :
    QuasiIso (L.subgroupChainAugmentation R) :=
  L.subgroupChainAugmentation_quasiIso_of_realizationUnit R (canonicalRealizationUnitInput R)

theorem subgroupCochainAugmentation_quasiIso_unconditional (A : ModuleCat.{u} R) :
    QuasiIso (L.subgroupCochainAugmentation R A) :=
  L.subgroupCochainAugmentation_quasiIso_of_realizationUnit R A (canonicalRealizationUnitInput R)

def subgroupDecompositionHomologyIso (n : ℕ) :
    (L.subgroupTotalChains R).homology n ≅
      ((SingularCohomology.chainsFunctor R).obj L.classifyingSpace).homology n := by
  letI := L.subgroupChainAugmentation_quasiIso_unconditional R
  exact asIso (HomologicalComplex.homologyMap (L.subgroupChainAugmentation R) n)

theorem subgroupDecompositionHomologyIso_hom (n : ℕ) :
    (L.subgroupDecompositionHomologyIso R n).hom =
      HomologicalComplex.homologyMap (L.subgroupChainAugmentation R) n := rfl

def subgroupDecompositionCohomologyIso (A : ModuleCat.{u} R) (n : ℕ) :
    SingularCohomology.cohomology R L.classifyingSpace A n ≅
      (L.subgroupTotalCochains R A).homology n :=
  L.subgroupAugmentationCohomologyIso_of_realizationUnit R A (canonicalRealizationUnitInput R) n

theorem subgroupDecompositionCohomologyIso_hom (A : ModuleCat.{u} R) (n : ℕ) :
    (L.subgroupDecompositionCohomologyIso R A n).hom =
      HomologicalComplex.homologyMap (L.subgroupCochainAugmentation R A) n := rfl

theorem subgroupDecompositionCohomologyIso_component
    (A : ModuleCat.{u} R) (P : F.CentricOrbit) (n : ℕ) :
    (L.subgroupDecompositionCohomologyIso R A n).hom ≫
        HomologicalComplex.homologyMap (L.subgroupTotalProjection R A P) n =
      SingularCohomology.pull R (L.subgroupDiagramForget P) A n :=
  L.subgroupAugmentationCohomology_component R A P n

theorem subgroupDecompositionCohomologyIso_coefficient
    {A B : ModuleCat.{u} R} (a : A ⟶ B) (n : ℕ) :
    HomologicalComplex.homologyMap
        (SingularCohomology.chainDualCoefficientMap R
          ((SingularCohomology.chainsFunctor R).obj L.classifyingSpace) a) n ≫
        (L.subgroupDecompositionCohomologyIso R B n).hom =
      (L.subgroupDecompositionCohomologyIso R A n).hom ≫
        HomologicalComplex.homologyMap (L.subgroupTotalCoefficientMap R a) n := by
  change HomologicalComplex.homologyMap _ n ≫
      HomologicalComplex.homologyMap (L.subgroupCochainAugmentation R B) n =
    HomologicalComplex.homologyMap (L.subgroupCochainAugmentation R A) n ≫
      HomologicalComplex.homologyMap _ n
  rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp,
    subgroupCochainAugmentation_naturality]

end Sharpness.FusionSystem.CentricLinkingSystem

