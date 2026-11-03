import Sharpness.SimplicialReplacementFunctor
import Sharpness.SimplicialReplacementAugmentation

/-! An actual commuting square of diagram cocones gives a commuting
square of the actual diagonal augmentation maps, on all simplices. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u
namespace Sharpness
open CategoryTheory Simplicial Opposite
variable {C : Type u} [Category.{u} C] {D E : C ⥤ SSet.{u}}
    {X Y : SSet.{u}} (a : D ⟶ E) (b : D ⟶ (Functor.const C).obj X)
    (c : E ⟶ (Functor.const C).obj Y) (f : X ⟶ Y)

theorem simplicialReplacementDiagonalAugmentation_naturality
    (h : ∀ P, a.app P ≫ c.app P = b.app P ≫ f) :
    simplicialReplacementDiagonalMap a ≫ simplicialReplacementDiagonalAugmentation E c =
      simplicialReplacementDiagonalAugmentation D b ≫ f := by
  apply NatTrans.ext
  funext i
  apply ConcreteCategory.ext_apply
  rintro ⟨s, x⟩
  change (c.app (chainHead s)).app i ((a.app (chainHead s)).app i x) =
    f.app i ((b.app (chainHead s)).app i x)
  exact congrArg (fun t => t.app i x) (h (chainHead s))

end Sharpness
