import Sharpness.CostructuredGrothendieckSection

/-! The actual fiber inclusion followed by the actual comma-Grothendieck
projection is the comma forgetful functor, as an equality of functors. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
noncomputable section
universe u
namespace Sharpness
open CategoryTheory
variable {C D : Type u} [Category.{u} C] [Category.{u} D] (T : C ⥤ D)

theorem costructuredGrothendieckFiber_projection (d : D) :
    Grothendieck.ι (CostructuredArrow.functor T) d ⋙
        CostructuredArrow.grothendieckProj T = CostructuredArrow.proj T d := by
  refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
  intro X Y f
  have h := (CostructuredArrow.ιCompGrothendieckProj T d).hom.naturality f
  change (Grothendieck.ι (CostructuredArrow.functor T) d ⋙
    CostructuredArrow.grothendieckProj T).map f ≫ 𝟙 _ =
      𝟙 _ ≫ (CostructuredArrow.proj T d).map f at h
  simpa only [eqToHom_refl, Category.comp_id, Category.id_comp] using h

end Sharpness
