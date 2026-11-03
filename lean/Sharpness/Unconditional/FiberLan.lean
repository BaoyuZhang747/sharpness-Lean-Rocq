import Sharpness.Unconditional.FiberLanComma
import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory

/-! Left Kan extension from the strict fiber of a prefibered functor is exact
for module-valued diagrams. Consequently, restriction to a fiber preserves
injective objects. The argument uses the actual cartesian lifts and AB4. -/

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

instance fiberLanComma_hasExactColimits (a : A) :
    HasExactColimitsOfShape (FiberLanComma p b a) (ModuleCat.{u} R) :=
  hasExactColimitsOfShape_of_final (ModuleCat.{u} R) (fiberLanTerminals p b a)

/-- The pointwise left-Kan formula is natural in the coefficient diagram. -/
def fiberLanColimitEvaluationIso (a : A) :
    (whiskeringLeft (FiberLanComma p b a) (Fiber p b) (ModuleCat.{u} R)).obj
        (CostructuredArrow.proj Fiber.fiberInclusion a) ⋙ colim ≅
      Fiber.fiberInclusion.lan ⋙ (evaluation A (ModuleCat.{u} R)).obj a :=
  NatIso.ofComponents
    (fun D => (Fiber.fiberInclusion.leftKanExtensionObjIsoColimit D a).symm) (by
      intro D E α
      apply colimit.hom_ext
      intro X
      change colimit.ι _ X ≫ colimMap (Functor.whiskerLeft _ α) ≫
          (Fiber.fiberInclusion.leftKanExtensionObjIsoColimit E a).inv =
        colimit.ι _ X ≫ (Fiber.fiberInclusion.leftKanExtensionObjIsoColimit D a).inv ≫
          (Fiber.fiberInclusion.lan.map α).app a
      simp only [ι_colimMap_assoc, Functor.whiskerLeft_app,
        Functor.ι_leftKanExtensionObjIsoColimit_inv_assoc,
        Functor.ι_leftKanExtensionObjIsoColimit_inv]
      change α.app X.left ≫ (Fiber.fiberInclusion.lanUnit.app E).app X.left ≫
          (Fiber.fiberInclusion.lan.obj E).map X.hom =
        (Fiber.fiberInclusion.lanUnit.app D).app X.left ≫
          (Fiber.fiberInclusion.lan.obj D).map X.hom ≫
            (Fiber.fiberInclusion.lan.map α).app a
      rw [(Fiber.fiberInclusion.lan.map α).naturality X.hom]
      simp only [← Category.assoc]
      congr 1
      exact congr_app (Fiber.fiberInclusion.lanUnit.naturality α) X.left)

instance fiberLan_preservesFiniteLimits :
    PreservesFiniteLimits (Fiber.fiberInclusion.lan :
      (Fiber p b ⥤ ModuleCat.{u} R) ⥤ (A ⥤ ModuleCat.{u} R)) := by
  apply preservesFiniteLimits_of_evaluation
  intro a
  letI : PreservesFiniteLimits
      ((whiskeringLeft (FiberLanComma p b a) (Fiber p b) (ModuleCat.{u} R)).obj
        (CostructuredArrow.proj Fiber.fiberInclusion a)) := ⟨fun _ => inferInstance⟩
  exact preservesFiniteLimits_of_natIso (fiberLanColimitEvaluationIso R p b a)

/-- Restricting an injective module diagram to a fiber remains injective. -/
instance fiberRestriction_preservesInjectiveObjects :
    ((whiskeringLeft (Fiber p b) A (ModuleCat.{u} R)).obj
      Fiber.fiberInclusion).PreservesInjectiveObjects :=
  Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (Fiber.fiberInclusion.lanAdjunction (ModuleCat.{u} R))

theorem fiberRestriction_injective (D : A ⥤ ModuleCat.{u} R) [Injective D] :
    Injective (Fiber.fiberInclusion (p := p) (S := b) ⋙ D) :=
  Functor.injective_obj
    ((whiskeringLeft (Fiber p b) A (ModuleCat.{u} R)).obj Fiber.fiberInclusion) D

end Sharpness
