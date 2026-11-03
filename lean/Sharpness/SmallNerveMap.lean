import Mathlib.AlgebraicTopology.SimplicialSet.Nerve
import Mathlib.CategoryTheory.SingleObj

/-! The native nerve map from a one-object group category to a category
whose object universe may be larger. Both nerves have the same universe
because the one-object category has the group's morphism universe. -/
set_option autoImplicit false
universe u
namespace Sharpness
open CategoryTheory
variable (M : Type u) [Monoid M] {C D : Type u} [Category.{u} C] [Category.{u} D]

def nerveMapSingleObj (F : SingleObj M ⥤ C) :
    CategoryTheory.nerve (SingleObj M) ⟶ CategoryTheory.nerve C :=
  { app _ := ↾fun X => (F.mapComposableArrows _).obj X }

theorem nerveMapSingleObj_comp (F : SingleObj M ⥤ C) (G : C ⥤ D) :
    nerveMapSingleObj M (F ⋙ G) = nerveMapSingleObj M F ≫ CategoryTheory.nerveMap G := by
  apply NatTrans.ext
  funext n
  rfl

end Sharpness
