import Sharpness.LinkingSubgroupSingularReplacement
import Sharpness.SimplicialReplacementAugmentation
import Sharpness.LinkingSubgroupRestriction
import Sharpness.SingularChainsProjective

/-! The actual subgroup-forgetful maps give a simplicial augmentation
of the diagonal singular replacement to Sing(|L|), and hence an
actual map of nonnegative chain complexes. No quasi-isomorphism
property is assumed here. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness.FusionSystem.CentricLinkingSystem
open CategoryTheory Simplicial Opposite
variable {S : Type u} [Group S] {F : FusionSystem S} (L : F.CentricLinkingSystem)

def subgroupSingularCocone : L.subgroupSingularDiagram ⟶
    (Functor.const F.CentricOrbit).obj (TopCat.toSSet.obj L.classifyingSpace) where
  app P := TopCat.toSSet.map (L.subgroupDiagramForget P)
  naturality {P Q} f := by
    change TopCat.toSSet.map (L.subgroupDiagram.map f) ≫
        TopCat.toSSet.map (L.subgroupDiagramForget Q) =
      TopCat.toSSet.map (L.subgroupDiagramForget P) ≫ 𝟙 _
    rw [← TopCat.toSSet.map_comp, L.subgroupDiagramForget_naturality, Category.comp_id]

def subgroupSingularDiagonalAugmentation :
    L.subgroupSingularDiagonal ⟶ TopCat.toSSet.obj L.classifyingSpace :=
  simplicialReplacementDiagonalAugmentation L.subgroupSingularDiagram L.subgroupSingularCocone

theorem subgroupSingularDiagonalAugmentation_component (i : SimplexCategoryᵒᵖ)
    (s : ComposableArrows F.CentricOrbit i.unop.len)
    (x : (TopCat.toSSet.obj (L.subgroupDiagram.obj (chainHead s))).obj i) :
    L.subgroupSingularDiagonalAugmentation.app i ⟨s, x⟩ =
      (TopCat.toSSet.map (L.subgroupDiagramForget (chainHead s))).app i x := rfl

def subgroupSingularDiagonalChainMap (R : Type u) [CommRing R] :
    L.subgroupSingularDiagonal.chainComplex (ModuleCat.of R R) ⟶
      (SingularCohomology.chainsFunctor R).obj L.classifyingSpace :=
  SSet.chainComplexMap L.subgroupSingularDiagonalAugmentation (ModuleCat.of R R)

theorem subgroupSingularDiagonalChainMap_simplex (R : Type u) [CommRing R]
    (n : ℕ) (s : ComposableArrows F.CentricOrbit n)
    (x : (TopCat.toSSet.obj (L.subgroupDiagram.obj (chainHead s))).obj (op ⦋n⦌)) :
    L.subgroupSingularDiagonal.ιChainComplex (R := ModuleCat.of R R) ⟨s, x⟩ ≫
        (L.subgroupSingularDiagonalChainMap R).f n =
      (TopCat.toSSet.obj L.classifyingSpace).ιChainComplex
        ((TopCat.toSSet.map (L.subgroupDiagramForget (chainHead s))).app (op ⦋n⦌) x) :=
  SSet.ι_chainComplexMap_f L.subgroupSingularDiagonal (TopCat.toSSet.obj L.classifyingSpace)
    L.subgroupSingularDiagonalAugmentation (ModuleCat.of R R) ⟨s, x⟩

theorem subgroupSingularDiagonalChains_projective (R : Type u) [CommRing R] (n : ℕ) :
    Projective ((L.subgroupSingularDiagonal.chainComplex (ModuleCat.of R R)).X n) :=
  SingularCohomology.simplicialChains_projective R L.subgroupSingularDiagonal n

end Sharpness.FusionSystem.CentricLinkingSystem
