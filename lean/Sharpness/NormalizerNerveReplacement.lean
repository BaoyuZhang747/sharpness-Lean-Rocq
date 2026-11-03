import Sharpness.RealizationDiagramUnit
import Sharpness.NormalizerSingularAugmentation
import Sharpness.NormalizerGeometryBase
import Sharpness.SimplicialReplacementLinearization

/-! The actual nerve-valued normalizer diagram, its diagonal
replacement and augmentation, and the actual realization-unit
comparison to the existing singular replacement. The resulting
augmentation square commutes as simplicial maps and as chain maps.
No geometric quasi-isomorphism or Thomason theorem is assumed here. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace Sharpness.FusionSystem.CentricLinkingSystem.LibmanNormalizerInput
open CategoryTheory Simplicial Opposite
variable {S : Type u} [Group S] [Finite S] {F : FusionSystem S}
    {L : F.CentricLinkingSystem} {p : ℕ} [Fact p.Prime]
    {hS : IsPGroup p S} {sat : F.Saturated p}
    (I : L.LibmanNormalizerInput p hS sat)

def normalizerNerveDiagram : F.NormalizerCategory ⥤ SSet.{u} :=
  I.normalizerCategoryDiagram ⋙ CategoryTheory.nerveFunctor

def normalizerNerveReplacement : SimplicialObject SSet.{u} :=
  simplicialSetReplacement I.normalizerNerveDiagram

def normalizerNerveDiagonal : SSet.{u} := simplicialReplacementDiagonal I.normalizerNerveDiagram

def normalizerNerveCocone : I.normalizerNerveDiagram ⟶
    (Functor.const F.NormalizerCategory).obj (CategoryTheory.nerve L.Object) := I.nerveCocone

def normalizerNerveDiagonalAugmentation : I.normalizerNerveDiagonal ⟶ CategoryTheory.nerve L.Object :=
  simplicialReplacementDiagonalAugmentation I.normalizerNerveDiagram I.normalizerNerveCocone

def normalizerNerveSingularUnit : I.normalizerNerveDiagram ⟶ I.normalizerSingularDiagram :=
  realizationDiagramUnit I.normalizerNerveDiagram

def normalizerNerveReplacementUnit : I.normalizerNerveDiagonal ⟶ I.normalizerSingularDiagonal :=
  realizationReplacementUnit I.normalizerNerveDiagram

theorem normalizerNerveReplacementUnit_component (i : SimplexCategoryᵒᵖ)
    (s : ComposableArrows F.NormalizerCategory i.unop.len)
    (x : (I.normalizerNerveDiagram.obj (chainHead s)).obj i) :
    I.normalizerNerveReplacementUnit.app i ⟨s, x⟩ =
      replacementSimplex I.normalizerSingularDiagram i.unop i s
        ((realizationSingularUnit (I.normalizerNerveDiagram.obj (chainHead s))).app i x) := rfl

theorem normalizerNerveReplacementUnit_augmentation :
    I.normalizerNerveReplacementUnit ≫ I.normalizerSingularDiagonalAugmentation =
      I.normalizerNerveDiagonalAugmentation ≫ realizationSingularUnit (CategoryTheory.nerve L.Object) :=
  realizationReplacementUnit_augmentation I.normalizerNerveDiagram I.normalizerNerveCocone

def normalizerNerveUnitChainMap (R : Type u) [CommRing R] :
    I.normalizerNerveDiagonal.chainComplex (ModuleCat.of R R) ⟶
      I.normalizerSingularDiagonal.chainComplex (ModuleCat.of R R) :=
  SSet.chainComplexMap I.normalizerNerveReplacementUnit (ModuleCat.of R R)

def normalizerNerveDiagonalChainAugmentation (R : Type u) [CommRing R] :
    I.normalizerNerveDiagonal.chainComplex (ModuleCat.of R R) ⟶
      (CategoryTheory.nerve L.Object).chainComplex (ModuleCat.of R R) :=
  SSet.chainComplexMap I.normalizerNerveDiagonalAugmentation (ModuleCat.of R R)

def normalizerRealizationUnitChainMap (_I : L.LibmanNormalizerInput p hS sat)
    (R : Type u) [CommRing R] :
    (CategoryTheory.nerve L.Object).chainComplex (ModuleCat.of R R) ⟶
      (SingularCohomology.chainsFunctor R).obj L.classifyingSpace :=
  SSet.chainComplexMap (realizationSingularUnit (CategoryTheory.nerve L.Object)) (ModuleCat.of R R)

theorem normalizerNerveUnitChainMap_augmentation (R : Type u) [CommRing R] :
    I.normalizerNerveUnitChainMap R ≫ I.normalizerSingularDiagonalChainMap R =
      I.normalizerNerveDiagonalChainAugmentation R ≫ I.normalizerRealizationUnitChainMap R := by
  calc
    _ = (simplicialChainsFunctor R).map
        (I.normalizerNerveReplacementUnit ≫ I.normalizerSingularDiagonalAugmentation) :=
      ((simplicialChainsFunctor R).map_comp _ _).symm
    _ = (simplicialChainsFunctor R).map
        (I.normalizerNerveDiagonalAugmentation ≫ realizationSingularUnit (CategoryTheory.nerve L.Object)) :=
      congrArg (fun f => (simplicialChainsFunctor R).map f) I.normalizerNerveReplacementUnit_augmentation
    _ = _ := (simplicialChainsFunctor R).map_comp _ _

end Sharpness.FusionSystem.CentricLinkingSystem.LibmanNormalizerInput
