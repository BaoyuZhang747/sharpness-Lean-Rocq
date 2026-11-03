import Sharpness.LinkingSubgroupNerveReplacement
import Sharpness.LinkingSubgroupAugmentationDual

/-! The actual nerve/singular comparison square after Hom_R(-,A),
including the manuscript's existing geometric cochain augmentation.
All arrows are the actual constructed maps. No unit or diagonal
quasi-isomorphism is an input to these identities. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace Sharpness.FusionSystem.CentricLinkingSystem
open CategoryTheory
variable {S : Type u} [Group S] {F : FusionSystem S}
    (L : F.CentricLinkingSystem) (R : Type u) [CommRing R] (A : ModuleCat.{u} R)

def subgroupNerveUnitCochainMap :
    ChainComplex.linearYonedaObj (L.subgroupSingularDiagonal.chainComplex (ModuleCat.of R R)) R A ⟶
      ChainComplex.linearYonedaObj (L.subgroupNerveDiagonal.chainComplex (ModuleCat.of R R)) R A :=
  SingularCohomology.chainDualMap R (L.subgroupNerveUnitChainMap R) A

def subgroupNerveDiagonalCochainAugmentation :
    ChainComplex.linearYonedaObj ((CategoryTheory.nerve L.Object).chainComplex (ModuleCat.of R R)) R A ⟶
      ChainComplex.linearYonedaObj (L.subgroupNerveDiagonal.chainComplex (ModuleCat.of R R)) R A :=
  SingularCohomology.chainDualMap R (L.subgroupNerveDiagonalChainAugmentation R) A

def subgroupRealizationUnitCochainMap : SingularCohomology.cochains R L.classifyingSpace A ⟶
    ChainComplex.linearYonedaObj ((CategoryTheory.nerve L.Object).chainComplex (ModuleCat.of R R)) R A :=
  SingularCohomology.chainDualMap R (L.subgroupRealizationUnitChainMap R) A

theorem subgroupNerveUnitCochainMap_augmentation :
    SingularCohomology.chainDualMap R (L.subgroupSingularDiagonalChainMap R) A ≫
        L.subgroupNerveUnitCochainMap R A =
      L.subgroupRealizationUnitCochainMap R A ≫ L.subgroupNerveDiagonalCochainAugmentation R A := by
  change SingularCohomology.chainDualMap R (L.subgroupSingularDiagonalChainMap R) A ≫
      SingularCohomology.chainDualMap R (L.subgroupNerveUnitChainMap R) A =
    SingularCohomology.chainDualMap R (L.subgroupRealizationUnitChainMap R) A ≫
      SingularCohomology.chainDualMap R (L.subgroupNerveDiagonalChainAugmentation R) A
  rw [← SingularCohomology.chainDualMap_comp, ← SingularCohomology.chainDualMap_comp,
    subgroupNerveUnitChainMap_augmentation]

theorem subgroupCochainAugmentation_nerveUnit (ez : EilenbergZilberInput.{u} R) :
    L.subgroupCochainAugmentation R A ≫ L.subgroupAlexanderWhitneyCochainMap R ez A ≫
        L.subgroupNerveUnitCochainMap R A =
      L.subgroupRealizationUnitCochainMap R A ≫ L.subgroupNerveDiagonalCochainAugmentation R A := by
  rw [← Category.assoc, subgroupCochainAugmentation_alexanderWhitney,
    subgroupNerveUnitCochainMap_augmentation]

theorem subgroupNerveDiagonalChains_projective (n : ℕ) :
    Projective ((L.subgroupNerveDiagonal.chainComplex (ModuleCat.of R R)).X n) :=
  SingularCohomology.simplicialChains_projective R L.subgroupNerveDiagonal n

theorem subgroupNerveClassifyingChains_projective (n : ℕ) :
    Projective (((CategoryTheory.nerve L.Object).chainComplex (ModuleCat.of R R)).X n) :=
  SingularCohomology.simplicialChains_projective R (CategoryTheory.nerve L.Object) n

end Sharpness.FusionSystem.CentricLinkingSystem
