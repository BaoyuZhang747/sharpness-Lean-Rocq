import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.Data.Fintype.EquivFin

set_option autoImplicit false
universe u
namespace Sharpness
open CategoryTheory

instance fullSubcategoryFinite {J : Type u} [Category.{u} J] [Finite J]
    (P : ObjectProperty J) : Finite P.FullSubcategory := by
  apply Finite.of_injective (fun X : P.FullSubcategory => X.obj)
  intro X Y h
  cases X
  cases Y
  cases h
  rfl

instance fullSubcategoryHomFinite {J : Type u} [Category.{u} J]
    [∀ X Y : J, Finite (X ⟶ Y)] (P : ObjectProperty J) (X Y : P.FullSubcategory) :
    Finite (X ⟶ Y) :=
  Finite.of_injective (fun f : X ⟶ Y => f.hom) (fun _ _ h => InducedCategory.hom_ext h)

end Sharpness
