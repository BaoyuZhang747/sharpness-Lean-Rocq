import Sharpness.Unconditional.CommaKanExactTerminal
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal

/-! A pointwise right-Kan unit is an isomorphism when the comma category
has an initial object whose structural arrow is an isomorphism. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace Sharpness
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite

variable (R : Type u) [CommRing R]
    {A B : Type u} [Category.{u} A] [Category.{u} B] (L : A ⥤ B)

theorem ran_unit_isIso_app_of_initial (D : B ⥤ ModuleCat.{u} R) (b : B)
    (X : StructuredArrow b L) (hX : IsInitial X) [IsIso X.hom] :
    IsIso (((L.ranAdjunction (ModuleCat.{u} R)).unit.app D).app b) := by
  let η : D ⟶ L.ran.obj (L ⋙ D) := (L.ranAdjunction (ModuleCat.{u} R)).unit.app D
  let ι := L.ranObjObjIsoLimit (L ⋙ D) b
  let π := limit.π (StructuredArrow.proj b L ⋙ (L ⋙ D)) X
  haveI : IsIso π := isIso_π_of_isInitial hX _
  have hh : η.app b ≫ (ι.hom ≫ π) = D.map X.hom := by
    dsimp only [ι, π]
    rw [L.ranObjObjIsoLimit_hom_π, ← Category.assoc, ← η.naturality,
      Category.assoc, L.ranCounit_app_app_ranAdjunction_unit_app_app]
    exact Category.comp_id _
  haveI : IsIso (η.app b ≫ (ι.hom ≫ π)) := by rw [hh]; infer_instance
  exact IsIso.of_isIso_comp_right _ (ι.hom ≫ π)

theorem ran_op_unit_isIso_app_of_terminal (D : Bᵒᵖ ⥤ ModuleCat.{u} R) (b : B)
    (X : CostructuredArrow L b) (hX : IsTerminal X) [IsIso X.hom] :
    IsIso (((L.op.ranAdjunction (ModuleCat.{u} R)).unit.app D).app (op b)) := by
  let e := costructuredArrowOpEquivalence L b
  let Y := e.functor.obj (op X)
  have hY : IsInitial Y := hX.op.isInitialObj e.functor (op X)
  haveI : IsIso Y.hom := by
    change IsIso X.hom.op
    infer_instance
  exact ran_unit_isIso_app_of_initial R L.op D (op b) Y hY

end Sharpness
