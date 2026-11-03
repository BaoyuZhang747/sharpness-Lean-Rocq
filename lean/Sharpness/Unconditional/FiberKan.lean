import Sharpness.Unconditional.FiberComma
import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
import Mathlib.Algebra.Category.ModuleCat.Limits

/-! Right Kan extension is computed by limits over actual fibers of a
prefibered functor. The comparison is natural in the coefficient diagram. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
noncomputable section
universe u

namespace Sharpness
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor

variable (R : Type u) [CommRing R]
    {A B : Type u} [Category.{u} A] [Category.{u} B]
    (p : A ⥤ B) [p.IsPreFibered] (b : B)

/-- Evaluation of the right Kan extension is the limit over the actual fiber. -/
def ranFiberIso (D : A ⥤ ModuleCat.{u} R) :
    (p.ran.obj D).obj b ≅ limit (Fiber.fiberInclusion (p := p) (S := b) ⋙ D) :=
  p.ranObjObjIsoLimit D b ≪≫ (fiberCommaLimitIso p b D).symm

@[reassoc]
theorem ranFiberIso_hom_π (D : A ⥤ ModuleCat.{u} R) (X : Fiber p b) :
    (ranFiberIso R p b D).hom ≫ limit.π _ X =
      (p.ran.obj D).map (eqToHom X.property.symm) ≫ (p.ranCounit.app D).app X.val := by
  change (p.ranObjObjIsoLimit D b).hom ≫
    limit.pre (StructuredArrow.proj b p ⋙ D) (fiberToComma p b) ≫
      limit.π (fiberToComma p b ⋙ (StructuredArrow.proj b p ⋙ D)) X = _
  rw [limit.pre_π, p.ranObjObjIsoLimit_hom_π]
  rfl

/-- The fiber-limit calculation is natural in the coefficient diagram. -/
def ranEvaluationFiberLimitIso :
    p.ran ⋙ (evaluation B (ModuleCat.{u} R)).obj b ≅
      (whiskeringLeft (Fiber p b) A (ModuleCat.{u} R)).obj Fiber.fiberInclusion ⋙ lim :=
  NatIso.ofComponents (ranFiberIso R p b) (by
    intro D E α
    change (p.ran.map α).app b ≫ (ranFiberIso R p b E).hom =
      (ranFiberIso R p b D).hom ≫ limMap (Functor.whiskerLeft Fiber.fiberInclusion α)
    apply limit.hom_ext
    intro X
    simp only [Category.assoc, limMap_π, ranFiberIso_hom_π, ranFiberIso_hom_π_assoc,
      Functor.whiskerLeft_app]
    rw [← Category.assoc]
    rw [← (p.ran.map α).naturality]
    simp only [Category.assoc]
    congr 1
    exact congr_app (p.ranCounit.naturality α) X.val)

end Sharpness
