import Sharpness.CategorySimplicialReplacement
import Sharpness.LinkingSubgroupDiagram
import Sharpness.SingularCochains

/-! The actual bisimplicial singular replacement of the subgroup
diagram, its diagonal, and the concrete action on all simplices. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness.FusionSystem.CentricLinkingSystem
open CategoryTheory Simplicial Opposite
variable {S : Type u} [Group S] {F : FusionSystem S} (L : F.CentricLinkingSystem)

def subgroupSingularDiagram : F.CentricOrbit ⥤ SSet.{u} :=
  L.subgroupDiagram ⋙ TopCat.toSSet

def subgroupSingularReplacement : SimplicialObject SSet.{u} :=
  simplicialSetReplacement L.subgroupSingularDiagram

def subgroupSingularDiagonal : SSet.{u} :=
  simplicialReplacementDiagonal L.subgroupSingularDiagram

theorem subgroupSingularReplacement_term (p q : ℕ) :
    (L.subgroupSingularReplacement.obj (op ⦋p⦌)).obj (op ⦋q⦌) =
      (Σ s : ComposableArrows F.CentricOrbit p,
        (TopCat.toSSet.obj (L.subgroupDiagram.obj (chainHead s))).obj (op ⦋q⦌)) := rfl

theorem subgroupSingularDiagonal_map {i j : SimplexCategoryᵒᵖ} (f : i ⟶ j)
    (s : ComposableArrows F.CentricOrbit i.unop.len)
    (x : (TopCat.toSSet.obj (L.subgroupDiagram.obj (chainHead s))).obj i) :
    L.subgroupSingularDiagonal.map f ⟨s, x⟩ =
      ⟨restrictCategoryChain f.unop s,
        (L.subgroupSingularDiagram.obj (chainHead (restrictCategoryChain f.unop s))).map f
          ((L.subgroupSingularDiagram.map (categoryChainHeadArrow f.unop s)).app i x)⟩ := rfl

end Sharpness.FusionSystem.CentricLinkingSystem
