import Sharpness.CostructuredDiagonalComparison
import Sharpness.LinkingSubgroupNerveReplacement

/-! The concrete comma-diagonal comparison for the manuscript's
actual linking system. Its composite with the actual Grothendieck
projection is the previously constructed nerve augmentation, also
after passing to the actual unnormalized chain complexes. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace Sharpness.FusionSystem.CentricLinkingSystem
open CategoryTheory Simplicial Opposite
variable {S : Type u} [Group S] {F : FusionSystem S} (L : F.CentricLinkingSystem)

def subgroupNerveGrothendieckComparison : L.subgroupNerveDiagonal ⟶
    CategoryTheory.nerve L.subgroupGrothendieck :=
  costructuredDiagonalGrothendieckMap L.orbitProjection

theorem subgroupNerveGrothendieckComparison_projection :
    L.subgroupNerveGrothendieckComparison ≫
        CategoryTheory.nerveMap L.subgroupGrothendieckProjection =
      L.subgroupNerveDiagonalAugmentation :=
  costructuredDiagonalGrothendieckMap_projection L.orbitProjection

def subgroupNerveGrothendieckChainMap (R : Type u) [CommRing R] :
    L.subgroupNerveDiagonal.chainComplex (ModuleCat.of R R) ⟶
      (CategoryTheory.nerve L.subgroupGrothendieck).chainComplex (ModuleCat.of R R) :=
  (simplicialChainsFunctor R).map L.subgroupNerveGrothendieckComparison

def subgroupGrothendieckNerveProjectionChainMap (R : Type u) [CommRing R] :
    (CategoryTheory.nerve L.subgroupGrothendieck).chainComplex (ModuleCat.of R R) ⟶
      (CategoryTheory.nerve L.Object).chainComplex (ModuleCat.of R R) :=
  (simplicialChainsFunctor R).map (CategoryTheory.nerveMap L.subgroupGrothendieckProjection)

theorem subgroupNerveGrothendieckChainMap_projection (R : Type u) [CommRing R] :
    L.subgroupNerveGrothendieckChainMap R ≫ L.subgroupGrothendieckNerveProjectionChainMap R =
      L.subgroupNerveDiagonalChainAugmentation R := by
  calc
    _ = (simplicialChainsFunctor R).map
        (L.subgroupNerveGrothendieckComparison ≫
          CategoryTheory.nerveMap L.subgroupGrothendieckProjection) :=
      ((simplicialChainsFunctor R).map_comp _ _).symm
    _ = _ := congrArg (fun f => (simplicialChainsFunctor R).map f)
      L.subgroupNerveGrothendieckComparison_projection

def subgroupNerveGrothendieckRealization :
    SSet.toTop.obj L.subgroupNerveDiagonal ⟶ L.subgroupGrothendieckSpace :=
  SSet.toTop.map L.subgroupNerveGrothendieckComparison

theorem subgroupNerveGrothendieckRealization_projection :
    L.subgroupNerveGrothendieckRealization ≫ L.subgroupHomotopyColimitMap =
      SSet.toTop.map L.subgroupNerveDiagonalAugmentation := by
  calc
    _ = SSet.toTop.map (L.subgroupNerveGrothendieckComparison ≫
        CategoryTheory.nerveMap L.subgroupGrothendieckProjection) :=
      (SSet.toTop.map_comp _ _).symm
    _ = _ := congrArg (fun f => SSet.toTop.map f) L.subgroupNerveGrothendieckComparison_projection

end Sharpness.FusionSystem.CentricLinkingSystem
