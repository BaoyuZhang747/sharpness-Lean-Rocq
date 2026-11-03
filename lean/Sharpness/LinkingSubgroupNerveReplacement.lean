import Sharpness.RealizationDiagramUnit
import Sharpness.LinkingSubgroupSingularAugmentation
import Sharpness.LinkingSubgroupRestriction
import Sharpness.SimplicialReplacementLinearization

/-! The actual nerve-valued subgroup diagram, its diagonal
replacement and augmentation, and the actual realization-unit
comparison to the existing singular replacement. The resulting
augmentation square commutes as simplicial maps and as chain maps.
No geometric quasi-isomorphism or Thomason theorem is assumed here. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace Sharpness.FusionSystem.CentricLinkingSystem
open CategoryTheory Simplicial Opposite
variable {S : Type u} [Group S] {F : FusionSystem S} (L : F.CentricLinkingSystem)

def subgroupNerveDiagram : F.CentricOrbit ⥤ SSet.{u} :=
  L.subgroupCategoryDiagram ⋙ CategoryTheory.nerveFunctor

def subgroupNerveReplacement : SimplicialObject SSet.{u} :=
  simplicialSetReplacement L.subgroupNerveDiagram

def subgroupNerveDiagonal : SSet.{u} := simplicialReplacementDiagonal L.subgroupNerveDiagram

def subgroupNerveCocone : L.subgroupNerveDiagram ⟶
    (Functor.const F.CentricOrbit).obj (CategoryTheory.nerve L.Object) where
  app P := CategoryTheory.nerveMap (CostructuredArrow.proj L.orbitProjection P)
  naturality {P Q} f := by
    change CategoryTheory.nerveMap (CostructuredArrow.map f) ≫
        CategoryTheory.nerveMap (CostructuredArrow.proj L.orbitProjection Q) =
      CategoryTheory.nerveMap (CostructuredArrow.proj L.orbitProjection P) ≫ 𝟙 _
    exact (Category.comp_id _).symm

def subgroupNerveDiagonalAugmentation : L.subgroupNerveDiagonal ⟶ CategoryTheory.nerve L.Object :=
  simplicialReplacementDiagonalAugmentation L.subgroupNerveDiagram L.subgroupNerveCocone

def subgroupNerveSingularUnit : L.subgroupNerveDiagram ⟶ L.subgroupSingularDiagram :=
  realizationDiagramUnit L.subgroupNerveDiagram

def subgroupNerveReplacementUnit : L.subgroupNerveDiagonal ⟶ L.subgroupSingularDiagonal :=
  realizationReplacementUnit L.subgroupNerveDiagram

theorem subgroupNerveReplacementUnit_component (i : SimplexCategoryᵒᵖ)
    (s : ComposableArrows F.CentricOrbit i.unop.len)
    (x : (L.subgroupNerveDiagram.obj (chainHead s)).obj i) :
    L.subgroupNerveReplacementUnit.app i ⟨s, x⟩ =
      replacementSimplex L.subgroupSingularDiagram i.unop i s
        ((realizationSingularUnit (L.subgroupNerveDiagram.obj (chainHead s))).app i x) := rfl

theorem subgroupNerveReplacementUnit_augmentation :
    L.subgroupNerveReplacementUnit ≫ L.subgroupSingularDiagonalAugmentation =
      L.subgroupNerveDiagonalAugmentation ≫ realizationSingularUnit (CategoryTheory.nerve L.Object) :=
  realizationReplacementUnit_augmentation L.subgroupNerveDiagram L.subgroupNerveCocone

def subgroupNerveUnitChainMap (R : Type u) [CommRing R] :
    L.subgroupNerveDiagonal.chainComplex (ModuleCat.of R R) ⟶
      L.subgroupSingularDiagonal.chainComplex (ModuleCat.of R R) :=
  SSet.chainComplexMap L.subgroupNerveReplacementUnit (ModuleCat.of R R)

def subgroupNerveDiagonalChainAugmentation (R : Type u) [CommRing R] :
    L.subgroupNerveDiagonal.chainComplex (ModuleCat.of R R) ⟶
      (CategoryTheory.nerve L.Object).chainComplex (ModuleCat.of R R) :=
  SSet.chainComplexMap L.subgroupNerveDiagonalAugmentation (ModuleCat.of R R)

def subgroupRealizationUnitChainMap (R : Type u) [CommRing R] :
    (CategoryTheory.nerve L.Object).chainComplex (ModuleCat.of R R) ⟶
      (SingularCohomology.chainsFunctor R).obj L.classifyingSpace :=
  SSet.chainComplexMap (realizationSingularUnit (CategoryTheory.nerve L.Object)) (ModuleCat.of R R)

theorem subgroupNerveUnitChainMap_augmentation (R : Type u) [CommRing R] :
    L.subgroupNerveUnitChainMap R ≫ L.subgroupSingularDiagonalChainMap R =
      L.subgroupNerveDiagonalChainAugmentation R ≫ L.subgroupRealizationUnitChainMap R := by
  calc
    _ = (simplicialChainsFunctor R).map
        (L.subgroupNerveReplacementUnit ≫ L.subgroupSingularDiagonalAugmentation) :=
      ((simplicialChainsFunctor R).map_comp _ _).symm
    _ = (simplicialChainsFunctor R).map
        (L.subgroupNerveDiagonalAugmentation ≫ realizationSingularUnit (CategoryTheory.nerve L.Object)) :=
      congrArg (fun f => (simplicialChainsFunctor R).map f) L.subgroupNerveReplacementUnit_augmentation
    _ = _ := (simplicialChainsFunctor R).map_comp _ _

end Sharpness.FusionSystem.CentricLinkingSystem
