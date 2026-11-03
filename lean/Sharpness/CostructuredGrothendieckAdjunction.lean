import Sharpness.CostructuredGrothendieckSection

/-! The explicit comma-Grothendieck section is left adjoint to the
actual projection. Both triangle identities are checked on the actual
base and fiber arrows. -/
set_option autoImplicit false
universe u
namespace Sharpness
open CategoryTheory
variable {C D : Type u} [Category.{u} C] [Category.{u} D] (T : C ⥤ D)

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
def costructuredGrothendieckAdjunction :
    costructuredGrothendieckSection T ⊣ CostructuredArrow.grothendieckProj T where
  unit := 𝟙 (𝟭 C)
  counit := costructuredGrothendieckCounit T
  left_triangle_components X := by
    change (costructuredGrothendieckSection T).map (𝟙 X) ≫
      (costructuredGrothendieckCounit T).app ((costructuredGrothendieckSection T).obj X) = _
    rw [(costructuredGrothendieckSection T).map_id, Category.id_comp]
    refine Grothendieck.ext
      ((costructuredGrothendieckCounit T).app ((costructuredGrothendieckSection T).obj X))
      (𝟙 ((costructuredGrothendieckSection T).obj X)) rfl ?_
    apply CostructuredArrow.hom_ext
    simp [costructuredGrothendieckCounit, costructuredGrothendieckSection,
      CostructuredArrow.functor, CostructuredArrow.map, Comma.mapRight]
  right_triangle_components X := by
    change (𝟙 X.fiber.left) ≫ 𝟙 X.fiber.left = 𝟙 X.fiber.left
    exact Category.id_comp _

end Sharpness
