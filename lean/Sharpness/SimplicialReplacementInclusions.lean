import Sharpness.CategorySimplicialReplacement

/-! Actual inclusions of every simplicial-set summand, and their
compatibility with every horizontal order map of the replacement. -/
set_option autoImplicit false
universe u
namespace Sharpness
open CategoryTheory Simplicial Opposite
variable {C : Type u} [Category.{u} C] (D : C ⥤ SSet.{u})

def simplicialReplacementInclusion (i : SimplexCategory) (s : ComposableArrows C i.len) :
    D.obj (chainHead s) ⟶ simplicialReplacementColumn D i where
  app j := ↾fun x => ⟨s, x⟩
  naturality {j k} f := rfl

theorem simplicialReplacementInclusion_map {i j : SimplexCategory} (f : i ⟶ j)
    (s : ComposableArrows C j.len) :
    simplicialReplacementInclusion D j s ≫ simplicialReplacementMap D f =
      D.map (categoryChainHeadArrow f s) ≫
        simplicialReplacementInclusion D i (restrictCategoryChain f s) := rfl

end Sharpness
