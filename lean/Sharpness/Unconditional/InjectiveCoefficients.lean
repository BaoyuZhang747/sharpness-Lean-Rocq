import Mathlib.CategoryTheory.Adjunction.Evaluation
import Mathlib.Algebra.Category.ModuleCat.EnoughInjectives

/-! Injective presentations of module-valued diagrams, obtained by taking
products of right adjoints to evaluation applied to injective presentations.
This is used for the centralizer-cover derived-limit argument. -/

set_option autoImplicit false
noncomputable section
universe u

namespace Sharpness.Unconditional
open CategoryTheory CategoryTheory.Limits

variable (R : Type u) [Ring R] (J : Type u) [Category.{u} J]

set_option backward.isDefEq.respectTransparency false in
/-- Every small module-valued diagram has an injective presentation. -/
def moduleDiagramInjectivePresentation (F : J ⥤ ModuleCat.{u} R) :
    InjectivePresentation F := by
  let I : J → J ⥤ ModuleCat.{u} R := fun j =>
    (evaluationRightAdjoint (ModuleCat.{u} R) j).obj (Injective.under (F.obj j))
  let f : ∀ j, F ⟶ I j := fun j =>
    (evaluationAdjunctionLeft (ModuleCat.{u} R) j).homEquiv F _
      (Injective.ι (F.obj j))
  haveI : ∀ j, Injective (I j) := fun j =>
    (evaluationAdjunctionLeft (ModuleCat.{u} R) j).map_injective _ inferInstance
  refine { J := ∏ᶜ I, f := Limits.Pi.lift f, injective := inferInstance, mono := ?_ }
  constructor
  intro G α β h
  apply NatTrans.ext
  funext j
  apply (cancel_mono (Injective.ι (F.obj j))).1
  have hj : α ≫ f j = β ≫ f j := by
    simpa only [Category.assoc, Limits.Pi.lift_π] using
      congrArg (fun η => η ≫ Limits.Pi.π I j) h
  have he := congrArg
    ((evaluationAdjunctionLeft (ModuleCat.{u} R) j).homEquiv G _).symm hj
  simpa only [Adjunction.homEquiv_naturality_left_symm, f, Equiv.symm_apply_apply,
    evaluation_obj_map, evaluation_obj_obj] using he

/-- Small module-valued functor categories have enough injectives. -/
instance moduleDiagramEnoughInjectives : EnoughInjectives (J ⥤ ModuleCat.{u} R) where
  presentation F := ⟨moduleDiagramInjectivePresentation R J F⟩

end Sharpness.Unconditional
