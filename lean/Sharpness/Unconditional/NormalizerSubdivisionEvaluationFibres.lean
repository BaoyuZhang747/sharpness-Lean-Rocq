import Sharpness.Unconditional.NormalizerSubdivisionEvaluationPoint
import Sharpness.Unconditional.NerveAdjunctionChains

/-! The actual nerve-chain contraction of every undercategory of
normalizer subdivision evaluation. No Quillen-A conclusion is assumed here. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u v w

namespace Sharpness.FusionSystem.CentricLinkingSystem
open CategoryTheory CategoryTheory.Limits
variable {S : Type u} [Group S] [Finite S] {F : FusionSystem S}
    (L : F.CentricLinkingSystem)

def normalizerEvaluationPointAdjunction (P : L.Object) :
    (Functor.star.{u} (L.NormalizerEvaluationPointed P)) ⊣
      Functor.fromPUnit (L.normalizerEvaluationPoint P) :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun X Y =>
        { toFun := fun _ => L.normalizerEvaluationPointArrow P X
          invFun := fun _ => eqToHom (Subsingleton.elim _ _)
          left_inv := fun _ => Subsingleton.elim _ _
          right_inv := fun f => (L.normalizerEvaluationPointArrow_unique P X f).symm }
      homEquiv_naturality_left_symm := by intros; apply Subsingleton.elim
      homEquiv_naturality_right := by
        intros
        apply (L.normalizerEvaluationPoint_isTerminal P).hom_ext }

variable {A : Type v} [Category.{w} A] [Preadditive A]
    [HasCoproducts.{u} A] [CategoryWithHomology A]

/-- The literal nerve map from the evaluation undercategory to a point
is a quasi-isomorphism, for arbitrary preadditive homology coefficients. -/
theorem normalizerEvaluationUnderProjection_quasiIso (P : L.Object) (R : A) :
    QuasiIso (SSet.chainComplexMap
      (nerveMap (Functor.star.{u} (L.NormalizerEvaluationUnder P))) R) := by
  haveI : QuasiIso (SSet.chainComplexMap (nerveMap (L.normalizerEvaluationCoreflection P)) R) :=
    nerveAdjunction_right_quasiIso (L.normalizerEvaluationCoreflectionAdjunction P) R
  haveI : QuasiIso (SSet.chainComplexMap
      (nerveMap (Functor.star.{u} (L.NormalizerEvaluationPointed P))) R) :=
    nerveAdjunction_left_quasiIso (L.normalizerEvaluationPointAdjunction P) R
  have he : L.normalizerEvaluationCoreflection P ⋙
      Functor.star.{u} (L.NormalizerEvaluationPointed P) =
      Functor.star.{u} (L.NormalizerEvaluationUnder P) := Functor.punit_ext' _ _
  have hc : SSet.chainComplexMap
      (nerveMap (Functor.star.{u} (L.NormalizerEvaluationUnder P))) R =
      SSet.chainComplexMap (nerveMap (L.normalizerEvaluationCoreflection P)) R ≫
        SSet.chainComplexMap (nerveMap (Functor.star.{u} (L.NormalizerEvaluationPointed P))) R := by
    rw [← he]
    exact ((SSet.chainComplexFunctor A).obj R).map_comp _ _
  rw [hc]
  infer_instance

end Sharpness.FusionSystem.CentricLinkingSystem
