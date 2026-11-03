import Sharpness.Unconditional.RealizationNerveHomotopy
import Sharpness.Unconditional.HeterogeneousNerve
import Sharpness.Unconditional.LinkingCommaReflection
import Sharpness.CategoryRealizationHomotopyInput
import Sharpness.LinkingSubgroupComparisonInput

/-! Unconditional construction of the actual categorical realization homotopy
input and the BLO subgroup comparison, from the explicit linking comma adjunction. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace Sharpness
open CategoryTheory

/-- The published category-realization homotopy input is now a constructed theorem. -/
def canonicalCategoryRealizationHomotopyInput : CategoryRealizationHomotopyInput.{u} where
  AKO_III_2_1 α := ⟨nerveRealizationHomotopy α⟩

namespace FusionSystem.CentricLinkingSystem
variable {S : Type u} [Group S] {F : FusionSystem S} (L : F.CentricLinkingSystem)

/-- The actual inverse comparison is induced by the proved comma reflection functor. -/
def canonicalSubgroupComparisonInverse (P : L.Object) :
    L.subgroupDiagram.obj (L.orbitProjection.obj P) ⟶ L.groupClassifyingSpace P :=
  SSet.toTop.map (heterogeneousNerveMap (L.linkingCommaReflection P))

/-- The adjunction counit gives the first actual topological inverse homotopy. -/
def canonicalSubgroupComparison_left (P : L.Object) :
    TopCat.Homotopy (L.subgroupComparison P ≫ L.canonicalSubgroupComparisonInverse P)
      (𝟙 (L.groupClassifyingSpace P)) := by
  have h := nerveRealizationHomotopy (L.linkingCommaAdjunction P).counit
  have hc : SSet.toTop.map (nerveMap
      (L.subgroupComparisonFunctor P ⋙ L.linkingCommaReflection P)) =
      L.subgroupComparison P ≫ L.canonicalSubgroupComparisonInverse P :=
    SSet.toTop.map_comp (nerveMapSingleObj P.as.val (L.subgroupComparisonFunctor P))
      (heterogeneousNerveMap (L.linkingCommaReflection P))
  have hi : SSet.toTop.map (nerveMap (𝟭 (SingleObj P.as.val))) =
      𝟙 (L.groupClassifyingSpace P) := SSet.toTop.map_id _
  simpa only [hc, hi] using h

/-- The reverse of the adjunction unit gives the second actual inverse homotopy. -/
def canonicalSubgroupComparison_right (P : L.Object) :
    TopCat.Homotopy (L.canonicalSubgroupComparisonInverse P ≫ L.subgroupComparison P)
      (𝟙 (L.subgroupDiagram.obj (L.orbitProjection.obj P))) := by
  have h := (nerveRealizationHomotopy (L.linkingCommaAdjunction P).unit).symm
  have hc : SSet.toTop.map (nerveMap
      (L.linkingCommaReflection P ⋙ L.subgroupComparisonFunctor P)) =
      L.canonicalSubgroupComparisonInverse P ≫ L.subgroupComparison P :=
    SSet.toTop.map_comp (heterogeneousNerveMap (L.linkingCommaReflection P))
      (nerveMapSingleObj P.as.val (L.subgroupComparisonFunctor P))
  have hi : SSet.toTop.map (nerveMap
      (𝟭 (L.subgroupDiagramCategory (L.orbitProjection.obj P)))) =
      𝟙 (L.subgroupDiagram.obj (L.orbitProjection.obj P)) := SSet.toTop.map_id _
  simpa only [hc, hi] using h

/-- The actual distinguished linking arrow realizes the required naturality homotopy. -/
def canonicalSubgroupComparison_naturality {P Q : L.Object} (f : P ⟶ Q) :
    TopCat.Homotopy
      (L.subgroupComparison P ≫ L.subgroupDiagram.map (L.orbitProjection.map f))
      (L.classifyingMapOfProjection f ≫ L.subgroupComparison Q) := by
  have h := realizationHomotopy
    (heterogeneousNerveHomotopy (L.linkingCommaComparisonNaturality f))
  have hl : SSet.toTop.map (heterogeneousNerveMap
      (L.subgroupComparisonFunctor P ⋙ CostructuredArrow.map (L.orbitProjection.map f))) =
      L.subgroupComparison P ≫ L.subgroupDiagram.map (L.orbitProjection.map f) :=
    SSet.toTop.map_comp (nerveMapSingleObj P.as.val (L.subgroupComparisonFunctor P))
      (nerveMap (CostructuredArrow.map (L.orbitProjection.map f)))
  have hr : SSet.toTop.map (heterogeneousNerveMap
      ((L.projection.map f).val.toFunctor ⋙ L.subgroupComparisonFunctor Q)) =
      L.classifyingMapOfProjection f ≫ L.subgroupComparison Q :=
    SSet.toTop.map_comp (nerveMap (L.projection.map f).val.toFunctor)
      (nerveMapSingleObj Q.as.val (L.subgroupComparisonFunctor Q))
  simpa only [hl, hr] using h

/-- All fields of the original BLO subgroup comparison input are supplied by
actual constructions and proved homotopies, with its full stated generality. -/
def canonicalBLOSubgroupComparisonInput [Finite S] (p : ℕ) [Fact p.Prime]
    (hS : IsPGroup p S) (sat : F.Saturated p) : L.BLOSubgroupComparisonInput p hS sat where
  comparisonInverse := L.canonicalSubgroupComparisonInverse
  comparison_left := L.canonicalSubgroupComparison_left
  comparison_right := L.canonicalSubgroupComparison_right
  comparison_naturality := L.canonicalSubgroupComparison_naturality

end FusionSystem.CentricLinkingSystem
end Sharpness
