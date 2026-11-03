import Sharpness.CategorySimplicialReplacement
import Sharpness.NormalizerGeometryBase
import Sharpness.SingularCochains

/-! The actual bisimplicial singular replacement of the normalizer
diagram, its diagonal, and the concrete action on all simplices. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness.FusionSystem.CentricLinkingSystem.LibmanNormalizerInput
open CategoryTheory Simplicial Opposite
variable {S : Type u} [Group S] [Finite S] {F : FusionSystem S}
    {L : F.CentricLinkingSystem} {p : ℕ} [Fact p.Prime]
    {hS : IsPGroup p S} {sat : F.Saturated p}
    (I : L.LibmanNormalizerInput p hS sat)

def normalizerSingularDiagram : F.NormalizerCategory ⥤ SSet.{u} :=
  I.normalizerDiagram ⋙ TopCat.toSSet

def normalizerSingularReplacement : SimplicialObject SSet.{u} :=
  simplicialSetReplacement I.normalizerSingularDiagram

def normalizerSingularDiagonal : SSet.{u} :=
  simplicialReplacementDiagonal I.normalizerSingularDiagram

theorem normalizerSingularReplacement_term (p q : ℕ) :
    (I.normalizerSingularReplacement.obj (op ⦋p⦌)).obj (op ⦋q⦌) =
      (Σ s : ComposableArrows F.NormalizerCategory p,
        (TopCat.toSSet.obj (I.normalizerDiagram.obj (chainHead s))).obj (op ⦋q⦌)) := rfl

theorem normalizerSingularDiagonal_map {i j : SimplexCategoryᵒᵖ} (f : i ⟶ j)
    (s : ComposableArrows F.NormalizerCategory i.unop.len)
    (x : (TopCat.toSSet.obj (I.normalizerDiagram.obj (chainHead s))).obj i) :
    I.normalizerSingularDiagonal.map f ⟨s, x⟩ =
      ⟨restrictCategoryChain f.unop s,
        (I.normalizerSingularDiagram.obj (chainHead (restrictCategoryChain f.unop s))).map f
          ((I.normalizerSingularDiagram.map (categoryChainHeadArrow f.unop s)).app i x)⟩ := rfl

end Sharpness.FusionSystem.CentricLinkingSystem.LibmanNormalizerInput
