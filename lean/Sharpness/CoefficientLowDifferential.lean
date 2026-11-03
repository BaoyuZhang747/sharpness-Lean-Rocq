import Sharpness.CategoryLowChains
import Sharpness.CoefficientCochainFormula

/-! The actual degree-zero bar differential, expressed on the actual
one-arrow evaluation maps. -/
set_option autoImplicit false
noncomputable section
universe u v t
namespace Sharpness
open CategoryTheory Simplicial Opposite

theorem alternatingCoface_zero_d {D : Type v} [Category.{t} D] [Preadditive D]
    (X : CosimplicialObject D) :
    ((AlgebraicTopology.alternatingCofaceMapComplex D).obj X).d 0 1 = X.δ (0 : Fin 2)-X.δ (1 : Fin 2) := by
  rw [alternatingCoface_d, Fin.sum_univ_two]
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_smul, neg_one_zsmul, sub_eq_add_neg]

variable {R C : Type u} [CommRing R] [Category.{u} C]
    (M : Cᵒᵖ ⥤ ModuleCat.{u} R)

def coefficientZeroEvaluation (P : C) : (coefficientCochains M).X 0 ⟶ M.obj (op P) :=
  ModuleCat.ofHom (LinearMap.proj (ComposableArrows.mk₀ P))

def coefficientOneEvaluation {P Q : C} (f : P ⟶ Q) : (coefficientCochains M).X 1 ⟶ M.obj (op P) :=
  ModuleCat.ofHom (LinearMap.proj (ComposableArrows.mk₁ f))

set_option backward.isDefEq.respectTransparency false in
theorem coefficientCofaceZero_evaluation {P Q : C} (f : P ⟶ Q) :
    (coefficientReplacement M).δ (0 : Fin 2) ≫ coefficientOneEvaluation M f =
      coefficientZeroEvaluation M Q ≫ M.map f.op := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change M.map f.op (x (restrictCategoryChain (SimplexCategory.δ (0 : Fin 2)) (ComposableArrows.mk₁ f))) =
    M.map f.op (x (ComposableArrows.mk₀ Q))
  exact congrArg (fun y => M.map f.op y)
    (eq_of_heq (congr_arg_heq x (categoryChain_coface_zero_mk₁ f)))

set_option backward.isDefEq.respectTransparency false in
theorem coefficientCofaceOne_evaluation {P Q : C} (f : P ⟶ Q) :
    (coefficientReplacement M).δ (1 : Fin 2) ≫ coefficientOneEvaluation M f = coefficientZeroEvaluation M P := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change M.map (𝟙 (op P)) (x (restrictCategoryChain (SimplexCategory.δ (1 : Fin 2)) (ComposableArrows.mk₁ f))) =
    x (ComposableArrows.mk₀ P)
  rw [M.map_id]
  change x (restrictCategoryChain (SimplexCategory.δ (1 : Fin 2)) (ComposableArrows.mk₁ f)) = x (ComposableArrows.mk₀ P)
  exact eq_of_heq (congr_arg_heq x (categoryChain_coface_one_mk₁ f))

set_option backward.isDefEq.respectTransparency false in
theorem coefficientZeroDifferential_evaluation {P Q : C} (f : P ⟶ Q) :
    (coefficientCochains M).d 0 1 ≫ coefficientOneEvaluation M f =
      coefficientZeroEvaluation M Q ≫ M.map f.op - coefficientZeroEvaluation M P := by
  have hd := alternatingCoface_zero_d (coefficientReplacement M)
  calc
    _ = ((coefficientReplacement M).δ (0 : Fin 2)-(coefficientReplacement M).δ (1 : Fin 2)) ≫
        coefficientOneEvaluation M f := congrArg (fun t => t ≫ coefficientOneEvaluation M f) hd
    _ = (coefficientReplacement M).δ (0 : Fin 2) ≫ coefficientOneEvaluation M f -
        (coefficientReplacement M).δ (1 : Fin 2) ≫ coefficientOneEvaluation M f := Preadditive.sub_comp _ _ _
    _ = _ := congrArg₂ (fun x y => x-y) (coefficientCofaceZero_evaluation M f) (coefficientCofaceOne_evaluation M f)

end Sharpness
