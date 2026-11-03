import Sharpness.LinkingSubgroupAugmentation
import Sharpness.LinkingSubgroupCoefficientCochains
import Sharpness.ZeroColumnTotalNaturality

/-! The actual geometric augmentation is natural for every homomorphism
of the arbitrary constant coefficient modules. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness.FusionSystem.CentricLinkingSystem
open CategoryTheory Simplicial Opposite
variable {S : Type u} [Group S] {F : FusionSystem S}
    (L : F.CentricLinkingSystem) (R : Type u) [CommRing R]
    {A B : ModuleCat.{u} R} (a : A ⟶ B)

set_option backward.isDefEq.respectTransparency false in
theorem subgroupAugmentationColumn_naturality :
    SingularCohomology.chainDualCoefficientMap R ((SingularCohomology.chainsFunctor R).obj L.classifyingSpace) a ≫
      replacementConeColumnMap (L.subgroupCochainDiagram R B) (L.subgroupCochainRestrictionCone R B) ⦋0⦌ =
    replacementConeColumnMap (L.subgroupCochainDiagram R A) (L.subgroupCochainRestrictionCone R A) ⦋0⦌ ≫
      (L.subgroupBicomplexCoefficientMap R a).f 0 := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  funext s
  change ((SingularCohomology.chainsFunctor R).map (L.subgroupDiagramForget (chainHead s))).f n ≫ (z ≫ a) =
    (((SingularCohomology.chainsFunctor R).map (L.subgroupDiagramForget (chainHead s))).f n ≫ z) ≫ a
  exact (Category.assoc _ _ _).symm

set_option backward.isDefEq.respectTransparency false in
theorem subgroupCochainAugmentation_naturality :
    SingularCohomology.chainDualCoefficientMap R ((SingularCohomology.chainsFunctor R).obj L.classifyingSpace) a ≫
      L.subgroupCochainAugmentation R B =
    L.subgroupCochainAugmentation R A ≫ L.subgroupTotalCoefficientMap R a :=
  zeroColumnTotalMap_naturality (L.subgroupBicomplex R A) (L.subgroupBicomplex R B)
    (L.subgroupBicomplexCoefficientMap R a)
    (replacementConeColumnMap _ (L.subgroupCochainRestrictionCone R A) ⦋0⦌)
    (replacementConeColumnMap_horizontal_zero _ (L.subgroupCochainRestrictionCone R A))
    (replacementConeColumnMap _ (L.subgroupCochainRestrictionCone R B) ⦋0⦌)
    (replacementConeColumnMap_horizontal_zero _ (L.subgroupCochainRestrictionCone R B))
    (SingularCohomology.chainDualCoefficientMap R ((SingularCohomology.chainsFunctor R).obj L.classifyingSpace) a)
    (L.subgroupAugmentationColumn_naturality R a)

end Sharpness.FusionSystem.CentricLinkingSystem
