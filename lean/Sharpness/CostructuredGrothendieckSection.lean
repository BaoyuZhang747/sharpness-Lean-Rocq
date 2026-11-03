import Mathlib.CategoryTheory.Comma.StructuredArrow.Functor
import Mathlib.CategoryTheory.Adjunction.Basic

/-! The actual projection from the Grothendieck category of comma
categories has an explicit section. The canonical arrow from the
section of an object's projection back to the object is natural. -/
set_option autoImplicit false
universe u
namespace Sharpness
open CategoryTheory
variable {C D : Type u} [Category.{u} C] [Category.{u} D] (T : C ⥤ D)

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
def costructuredGrothendieckSection : C ⥤ Grothendieck (CostructuredArrow.functor T) where
  obj X := ⟨T.obj X, CostructuredArrow.mk (𝟙 (T.obj X))⟩
  map f := ⟨T.map f, CostructuredArrow.homMk f (by
    change T.map f ≫ 𝟙 _ = 𝟙 _ ≫ T.map f
    simp)⟩
  map_id X := by
    apply Grothendieck.ext _ _ (T.map_id X)
    apply CostructuredArrow.hom_ext
    simp [CostructuredArrow.functor, CostructuredArrow.map, Comma.mapRight]
  map_comp f g := by
    apply Grothendieck.ext _ _ (T.map_comp f g)
    apply CostructuredArrow.hom_ext
    simp [CostructuredArrow.functor, CostructuredArrow.map, Comma.mapRight]

theorem costructuredGrothendieckSection_projection :
    costructuredGrothendieckSection T ⋙ CostructuredArrow.grothendieckProj T = 𝟭 C := rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
def costructuredGrothendieckCounit :
    CostructuredArrow.grothendieckProj T ⋙ costructuredGrothendieckSection T ⟶
      𝟭 (Grothendieck (CostructuredArrow.functor T)) where
  app X := ⟨X.fiber.hom, CostructuredArrow.homMk (𝟙 X.fiber.left) (by
    change T.map (𝟙 X.fiber.left) ≫ X.fiber.hom = 𝟙 _ ≫ X.fiber.hom
    simp)⟩
  naturality {X Y} f := by
    apply Grothendieck.ext _ _ (by
      change T.map f.fiber.left ≫ Y.fiber.hom = X.fiber.hom ≫ f.base
      exact CostructuredArrow.w f.fiber)
    apply CostructuredArrow.hom_ext
    simp [costructuredGrothendieckSection, CostructuredArrow.functor,
      CostructuredArrow.map, Comma.mapRight]

end Sharpness
