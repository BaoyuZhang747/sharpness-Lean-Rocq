import Sharpness.HigherLimits

/-! The native ModuleCat-valued covariant part of a full Mackey functor. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness.MackeyModule
open CategoryTheory
variable {R C : Type u} [CommRing R] [Category.{u} C] {B : MackeyShape C}
    (M : MackeyModule.{u,u,u} R C B)

def covariant : C ⥤ ModuleCat.{u} R where
  obj P := ModuleCat.of R (M.Value P)
  map f := ModuleCat.ofHom (M.push f)
  map_id P := by
    apply ModuleCat.hom_ext
    exact M.push_id P
  map_comp f g := by
    apply ModuleCat.hom_ext
    exact M.push_comp f g

end Sharpness.MackeyModule
