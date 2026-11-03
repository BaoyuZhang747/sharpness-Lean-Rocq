import Sharpness.LinkingSubgroupNerveGrothendieck
import Sharpness.LinkingSubgroupNerveCochains

/-! The complete actual comparison triangle after arbitrary-module
duality. It relates the manuscript's cochain augmentation to the
actual singular Grothendieck projection, not merely abstractly
isomorphic cohomology objects. No geometric quasi-isomorphism is
asserted or assumed by these identities. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace Sharpness.FusionSystem.CentricLinkingSystem
open CategoryTheory
variable {S : Type u} [Group S] {F : FusionSystem S}
    (L : F.CentricLinkingSystem) (R : Type u) [CommRing R] (A : ModuleCat.{u} R)

def subgroupNerveGrothendieckCochainMap :
    ChainComplex.linearYonedaObj ((CategoryTheory.nerve L.subgroupGrothendieck).chainComplex
      (ModuleCat.of R R)) R A ⟶
    ChainComplex.linearYonedaObj (L.subgroupNerveDiagonal.chainComplex (ModuleCat.of R R)) R A :=
  SingularCohomology.chainDualMap R (L.subgroupNerveGrothendieckChainMap R) A

def subgroupGrothendieckNerveProjectionCochainMap :
    ChainComplex.linearYonedaObj ((CategoryTheory.nerve L.Object).chainComplex (ModuleCat.of R R)) R A ⟶
    ChainComplex.linearYonedaObj ((CategoryTheory.nerve L.subgroupGrothendieck).chainComplex
      (ModuleCat.of R R)) R A :=
  SingularCohomology.chainDualMap R (L.subgroupGrothendieckNerveProjectionChainMap R) A

theorem subgroupNerveGrothendieckCochainMap_projection :
    L.subgroupGrothendieckNerveProjectionCochainMap R A ≫ L.subgroupNerveGrothendieckCochainMap R A =
      L.subgroupNerveDiagonalCochainAugmentation R A := by
  change SingularCohomology.chainDualMap R (L.subgroupGrothendieckNerveProjectionChainMap R) A ≫
    SingularCohomology.chainDualMap R (L.subgroupNerveGrothendieckChainMap R) A =
    SingularCohomology.chainDualMap R (L.subgroupNerveDiagonalChainAugmentation R) A
  rw [← SingularCohomology.chainDualMap_comp, subgroupNerveGrothendieckChainMap_projection]

def subgroupGrothendieckRealizationUnitChainMap :
    (CategoryTheory.nerve L.subgroupGrothendieck).chainComplex (ModuleCat.of R R) ⟶
      (SingularCohomology.chainsFunctor R).obj L.subgroupGrothendieckSpace :=
  (simplicialChainsFunctor R).map (realizationSingularUnit (CategoryTheory.nerve L.subgroupGrothendieck))

theorem subgroupGrothendieckRealizationUnitChainMap_projection :
    L.subgroupGrothendieckNerveProjectionChainMap R ≫ L.subgroupRealizationUnitChainMap R =
      L.subgroupGrothendieckRealizationUnitChainMap R ≫
        (SingularCohomology.chainsFunctor R).map L.subgroupHomotopyColimitMap := by
  calc
    _ = (simplicialChainsFunctor R).map
        (CategoryTheory.nerveMap L.subgroupGrothendieckProjection ≫
          realizationSingularUnit (CategoryTheory.nerve L.Object)) :=
      ((simplicialChainsFunctor R).map_comp _ _).symm
    _ = (simplicialChainsFunctor R).map
        (realizationSingularUnit (CategoryTheory.nerve L.subgroupGrothendieck) ≫
          realizationSingularFunctor.map (CategoryTheory.nerveMap L.subgroupGrothendieckProjection)) :=
      congrArg (fun f => (simplicialChainsFunctor R).map f)
        (realizationSingularUnit_naturality (CategoryTheory.nerveMap L.subgroupGrothendieckProjection))
    _ = _ := (simplicialChainsFunctor R).map_comp _ _

def subgroupGrothendieckRealizationUnitCochainMap :
    SingularCohomology.cochains R L.subgroupGrothendieckSpace A ⟶
      ChainComplex.linearYonedaObj ((CategoryTheory.nerve L.subgroupGrothendieck).chainComplex
        (ModuleCat.of R R)) R A :=
  SingularCohomology.chainDualMap R (L.subgroupGrothendieckRealizationUnitChainMap R) A

theorem subgroupGrothendieckRealizationUnitCochainMap_projection :
    L.subgroupRealizationUnitCochainMap R A ≫ L.subgroupGrothendieckNerveProjectionCochainMap R A =
      SingularCohomology.cochainPull R L.subgroupHomotopyColimitMap A ≫
        L.subgroupGrothendieckRealizationUnitCochainMap R A := by
  change SingularCohomology.chainDualMap R (L.subgroupRealizationUnitChainMap R) A ≫
      SingularCohomology.chainDualMap R (L.subgroupGrothendieckNerveProjectionChainMap R) A =
    SingularCohomology.chainDualMap R ((SingularCohomology.chainsFunctor R).map L.subgroupHomotopyColimitMap) A ≫
      SingularCohomology.chainDualMap R (L.subgroupGrothendieckRealizationUnitChainMap R) A
  rw [← SingularCohomology.chainDualMap_comp, ← SingularCohomology.chainDualMap_comp,
    subgroupGrothendieckRealizationUnitChainMap_projection]

theorem subgroupCochainAugmentation_grothendieckTriangle (ez : EilenbergZilberInput.{u} R) :
    L.subgroupCochainAugmentation R A ≫ L.subgroupAlexanderWhitneyCochainMap R ez A ≫
        L.subgroupNerveUnitCochainMap R A =
      SingularCohomology.cochainPull R L.subgroupHomotopyColimitMap A ≫
        L.subgroupGrothendieckRealizationUnitCochainMap R A ≫
          L.subgroupNerveGrothendieckCochainMap R A := by
  rw [subgroupCochainAugmentation_nerveUnit,
    ← subgroupNerveGrothendieckCochainMap_projection, ← Category.assoc,
    subgroupGrothendieckRealizationUnitCochainMap_projection, Category.assoc]

end Sharpness.FusionSystem.CentricLinkingSystem
