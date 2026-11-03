import Sharpness.AlternatingCofaceFunctorIso

/-! The first actual alternating-coface differential kills a map on
which the first two cofaces agree. This is a direct calculation in an
arbitrary preadditive category. -/
set_option autoImplicit false
noncomputable section
universe u v
namespace Sharpness
open CategoryTheory Simplicial
variable {C : Type u} [Category.{v} C] [Preadditive C]

theorem alternatingCoface_coaugmentation_zero (X : CosimplicialObject C) {A : C}
    (a : A ⟶ X.obj ⦋0⦌) (b : A ⟶ X.obj ⦋1⦌)
    (h₀ : a ≫ X.δ (0 : Fin 2)=b) (h₁ : a ≫ X.δ (1 : Fin 2)=b) :
    a ≫ ((AlgebraicTopology.alternatingCofaceMapComplex C).obj X).d 0 1 = 0 := by
  have hd : ((AlgebraicTopology.alternatingCofaceMapComplex C).obj X).d 0 1 =
      X.δ (0 : Fin 2) - X.δ (1 : Fin 2) := by
    rw [alternatingCoface_d, Fin.sum_univ_two]
    simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_smul, neg_one_zsmul, sub_eq_add_neg]
  calc
    _ = a ≫ (X.δ (0 : Fin 2) - X.δ (1 : Fin 2)) := congrArg (fun t => a ≫ t) hd
    _ = a ≫ X.δ (0 : Fin 2) - a ≫ X.δ (1 : Fin 2) :=
      Preadditive.comp_sub a _ _
    _ = b-b := congrArg₂ (fun f g => f-g) h₀ h₁
    _ = 0 := sub_self b

end Sharpness
