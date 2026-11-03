import Sharpness.Unconditional.CostructuredHorizontalRows

/-! The actual comma cocone augments the whole bisimplicial replacement.
After flipping, its column maps are the horizontal row augmentations. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace Sharpness
open CategoryTheory Simplicial Opposite
variable {C D : Type u} [Category.{u} C] [Category.{u} D] (T : C ⥤ D)

def costructuredBisimplicialAugmentation :
    simplicialSetReplacement (costructuredNerveDiagram T) ⟶
      (CategoryTheory.Functor.const SimplexCategoryᵒᵖ).obj (CategoryTheory.nerve C) where
  app p := simplicialReplacementColumnAugmentation (costructuredNerveDiagram T)
    (costructuredNerveCocone T) p.unop
  naturality {p r} f := by
    exact (simplicialReplacementColumnAugmentation_naturality
      (costructuredNerveDiagram T) (costructuredNerveCocone T) f.unop).trans
        (Category.comp_id _).symm

def costructuredFlippedAugmentation :=
  (flipFunctor SimplexCategoryᵒᵖ SimplexCategoryᵒᵖ (Type u)).map
    (costructuredBisimplicialAugmentation T)

theorem costructuredFlippedAugmentation_row (q : ℕ) :
    (costructuredFlippedAugmentation T).app (op (.mk q)) =
      costructuredHorizontalRowAugmentation T q := rfl

theorem costructuredBisimplicialAugmentation_diagonal (p : SimplexCategoryᵒᵖ) :
    ((costructuredBisimplicialAugmentation T).app p).app p =
      (simplicialReplacementDiagonalAugmentation (costructuredNerveDiagram T)
        (costructuredNerveCocone T)).app p := rfl

end Sharpness
