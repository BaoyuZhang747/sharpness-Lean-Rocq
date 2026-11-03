import Mathlib.Algebra.Homology.Embedding.Extend
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero

/-! Extension by zero along an embedding of complex shapes preserves
colimits. Evaluation in the image is naturally ordinary evaluation;
outside the image it is an actual zero functor. -/
set_option autoImplicit false
noncomputable section
universe u v t t' w w'
namespace Sharpness
open CategoryTheory CategoryTheory.Limits
variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] [HasZeroObject C]
    {ι : Type t} {ι' : Type t'} {c : ComplexShape ι} {c' : ComplexShape ι'}
    (e : c.Embedding c')

set_option backward.isDefEq.respectTransparency false in
def extensionEvaluationIso {i : ι} {i' : ι'} (hi : e.f i = i') :
    e.extendFunctor C ⋙ HomologicalComplex.eval C c' i' ≅ HomologicalComplex.eval C c i :=
  NatIso.ofComponents (fun K => K.extendXIso e hi) (by
    intro K L φ
    change (HomologicalComplex.extendMap φ e).f i' ≫ (L.extendXIso e hi).hom =
      (K.extendXIso e hi).hom ≫ φ.f i
    simp only [HomologicalComplex.extendMap_f φ e hi, Category.assoc,
      Iso.inv_hom_id, Category.comp_id])

instance extensionFunctor_preservesColimitsOfShape
    (J : Type w) [Category.{w'} J] [HasColimitsOfShape J C] :
    PreservesColimitsOfShape J (e.extendFunctor C) :=
  HomologicalComplex.preservesColimitsOfShape_of_eval _ (fun i' => by
    by_cases hi' : ∃ i, e.f i = i'
    · obtain ⟨i, hi⟩ := hi'
      exact preservesColimitsOfShape_of_natIso (extensionEvaluationIso e hi).symm
    · exact Functor.preservesColimitsOfShape_of_isZero _
        (Functor.isZero _ (fun K => K.isZero_extend_X e i' (fun i hi => hi' ⟨i, hi⟩))) J)

end Sharpness
