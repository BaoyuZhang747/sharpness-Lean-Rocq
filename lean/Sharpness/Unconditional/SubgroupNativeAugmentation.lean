import Sharpness.Unconditional.NativeCostructuredAugmentation
import Sharpness.LinkingSubgroupNerveComparisonQuasiIso

/-! Actual subgroup nerve and geometric augmentations using the proved comma
comparison directly. Only the genuine realization-unit theorem remains as a
premise for the singular/cochain statements; no Thomason input is used. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace Sharpness.FusionSystem.CentricLinkingSystem
open CategoryTheory
variable {S : Type u} [Group S] {F : FusionSystem S}
    (L : F.CentricLinkingSystem) (R : Type u) [CommRing R]

theorem subgroupNerveDiagonalChainAugmentation_quasiIso :
    QuasiIso (L.subgroupNerveDiagonalChainAugmentation R) :=
  costructuredDiagonalAugmentation_quasiIso_native R L.orbitProjection

theorem subgroupNerveDiagonalCochainAugmentation_quasiIso (A : ModuleCat.{u} R) :
    QuasiIso (L.subgroupNerveDiagonalCochainAugmentation R A) := by
  letI (n : ℕ) : Projective ((L.subgroupNerveDiagonal.chainComplex (ModuleCat.of R R)).X n) :=
    L.subgroupNerveDiagonalChains_projective R n
  letI (n : ℕ) : Projective (((CategoryTheory.nerve L.Object).chainComplex (ModuleCat.of R R)).X n) :=
    L.subgroupNerveClassifyingChains_projective R n
  letI := L.subgroupNerveDiagonalChainAugmentation_quasiIso R
  exact SingularCohomology.chainDualMap_quasiIso_of_projective R A
    (L.subgroupNerveDiagonalChainAugmentation R)

theorem subgroupSingularDiagonalChainMap_quasiIso_of_realizationUnit
    (real : RealizationUnitInput.{u} R) :
    QuasiIso (L.subgroupSingularDiagonalChainMap R) := by
  letI := L.subgroupNerveUnitChainMap_quasiIso R real
    (canonicalReplacementHomologyInvarianceInput R)
  letI := L.subgroupNerveDiagonalChainAugmentation_quasiIso R
  letI : QuasiIso (L.subgroupRealizationUnitChainMap R) :=
    real.May_16_2_Weibel_3_6_1 (CategoryTheory.nerve L.Object)
  haveI : QuasiIso (L.subgroupNerveUnitChainMap R ≫ L.subgroupSingularDiagonalChainMap R) := by
    rw [L.subgroupNerveUnitChainMap_augmentation R]
    infer_instance
  exact quasiIso_of_comp_left (L.subgroupNerveUnitChainMap R) _

theorem subgroupChainAugmentation_quasiIso_of_realizationUnit
    (real : RealizationUnitInput.{u} R) : QuasiIso (L.subgroupChainAugmentation R) :=
  (L.subgroupChainAugmentation_quasiIso_iff_diagonal R (canonicalEilenbergZilberInput R)).mpr
    (L.subgroupSingularDiagonalChainMap_quasiIso_of_realizationUnit R real)

theorem subgroupCochainAugmentation_quasiIso_of_realizationUnit
    (A : ModuleCat.{u} R) (real : RealizationUnitInput.{u} R) :
    QuasiIso (L.subgroupCochainAugmentation R A) := by
  let ez := canonicalEilenbergZilberInput R
  letI := L.subgroupAlexanderWhitneyCochainMap_quasiIso R ez A
  letI := L.subgroupNerveUnitCochainMap_quasiIso R A real
    (canonicalReplacementHomologyInvarianceInput R)
  letI := L.subgroupNerveDiagonalCochainAugmentation_quasiIso R A
  letI : QuasiIso (L.subgroupRealizationUnitCochainMap R A) :=
    realizationUnitCochainMap_quasiIso R (CategoryTheory.nerve L.Object) A real
  have h : QuasiIso (L.subgroupCochainAugmentation R A ≫
      (L.subgroupAlexanderWhitneyCochainMap R ez A ≫ L.subgroupNerveUnitCochainMap R A)) := by
    rw [L.subgroupCochainAugmentation_nerveUnit R A ez]
    infer_instance
  exact (quasiIso_iff_comp_right (L.subgroupCochainAugmentation R A)
    (L.subgroupAlexanderWhitneyCochainMap R ez A ≫ L.subgroupNerveUnitCochainMap R A)).mp h

def subgroupAugmentationCohomologyIso_of_realizationUnit
    (A : ModuleCat.{u} R) (real : RealizationUnitInput.{u} R) (n : ℕ) :
    SingularCohomology.cohomology R L.classifyingSpace A n ≅
      (L.subgroupTotalCochains R A).homology n := by
  letI := L.subgroupCochainAugmentation_quasiIso_of_realizationUnit R A real
  exact asIso (HomologicalComplex.homologyMap (L.subgroupCochainAugmentation R A) n)

theorem subgroupAugmentationCohomologyIso_of_realizationUnit_hom
    (A : ModuleCat.{u} R) (real : RealizationUnitInput.{u} R) (n : ℕ) :
    (L.subgroupAugmentationCohomologyIso_of_realizationUnit R A real n).hom =
      HomologicalComplex.homologyMap (L.subgroupCochainAugmentation R A) n := rfl

end Sharpness.FusionSystem.CentricLinkingSystem
