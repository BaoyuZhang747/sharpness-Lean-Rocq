import Sharpness.ProjectiveCoefficientInput
import Mathlib.CategoryTheory.Adjunction.Evaluation
import Mathlib.Algebra.Category.ModuleCat.Projective

/-!
# Projective presentations of module-valued diagrams

For each object of a diagram, take a projective object surjecting onto its
value and apply the left adjoint to evaluation. Their coproduct is projective and maps
epimorphically to the original diagram. This constructs both fields of the
projective-coefficient input used by the sharpness proof.
-/

set_option autoImplicit false

noncomputable section

universe u

namespace Sharpness.Unconditional

open CategoryTheory CategoryTheory.Limits

variable (R : Type u) [Ring R] (J : Type u) [Category.{u} J]

set_option backward.isDefEq.respectTransparency false in
/-- Every module-valued diagram admits a projective presentation. -/
def moduleDiagramProjectivePresentation (F : J ⥤ ModuleCat.{u} R) :
    ProjectivePresentation F := by
  let P : J → J ⥤ ModuleCat.{u} R := fun j =>
    (evaluationLeftAdjoint (ModuleCat.{u} R) j).obj (Projective.over (F.obj j))
  let f : ∀ j, P j ⟶ F := fun j =>
    ((evaluationAdjunctionRight (ModuleCat.{u} R) j).homEquiv _ F).symm
      (Projective.π (F.obj j))
  haveI : ∀ j, Projective (P j) := fun j =>
    (evaluationAdjunctionRight (ModuleCat.{u} R) j).map_projective _ inferInstance
  refine { p := ∐ P, f := Limits.Sigma.desc f, projective := inferInstance, epi := ?_ }
  constructor
  intro G α β h
  apply NatTrans.ext
  funext j
  apply (cancel_epi (Projective.π (F.obj j))).1
  have hj : f j ≫ α = f j ≫ β := by
    simpa only [← Category.assoc, Limits.Sigma.ι_desc] using
      congrArg (fun η => Limits.Sigma.ι P j ≫ η) h
  have he := congrArg ((evaluationAdjunctionRight (ModuleCat.{u} R) j).homEquiv _ G) hj
  simpa only [Adjunction.homEquiv_naturality_right, f, Equiv.apply_symm_apply,
    evaluation_obj_map, evaluation_obj_obj] using he

/-- Small module-valued functor categories have enough projectives. -/
theorem moduleDiagramEnoughProjectives : EnoughProjectives (J ⥤ ModuleCat.{u} R) where
  presentation F := ⟨moduleDiagramProjectivePresentation R J F⟩

/-- The sharpness proof's projective-coefficient input, constructed without
reference assumptions. -/
instance projectiveCoefficientInput : ProjectiveCoefficientInput.{u} where
  contravariant R _ J _ := moduleDiagramEnoughProjectives R Jᵒᵖ
  covariant R _ J _ := moduleDiagramEnoughProjectives R J

end Sharpness.Unconditional
