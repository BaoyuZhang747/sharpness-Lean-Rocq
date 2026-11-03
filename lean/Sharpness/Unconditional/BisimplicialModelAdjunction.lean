import Sharpness.Unconditional.BisimplicialRepresentable

/-! Evaluation on a representable model is right adjoint to the actual
free coefficient functor on bisimplices. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
noncomputable section
universe u v w

namespace Sharpness
open CategoryTheory CategoryTheory.Limits Simplicial Opposite

@[reassoc]
theorem bisimplicialRepresentableMap_comp {X Y : SimplicialObject SSet.{u}} (φ : X ⟶ Y)
    {p q : ℕ} (x : (X.obj (op ⦋p⦌)).obj (op ⦋q⦌)) :
    bisimplicialRepresentableMap X x ≫ φ =
      bisimplicialRepresentableMap Y ((φ.app (op ⦋p⦌)).app (op ⦋q⦌) x) := by
  apply bisimplicialRepresentable_hom_ext
  change (φ.app (op ⦋p⦌)).app (op ⦋q⦌)
      (((bisimplicialRepresentableMap X x).app (op ⦋p⦌)).app (op ⦋q⦌)
        (bisimplicialRepresentableGenerator p q)) = _
  rw [bisimplicialRepresentableMap_generator, bisimplicialRepresentableMap_generator]

@[simp]
theorem bisimplicialRepresentableMap_identity (p q : ℕ) :
    bisimplicialRepresentableMap (bisimplicialRepresentable.{u} p q)
      (bisimplicialRepresentableGenerator p q) = 𝟙 _ := by
  apply bisimplicialRepresentable_hom_ext
  rw [bisimplicialRepresentableMap_generator]
  rfl

def bisimplicialEvaluationFunctor (p q : ℕ) : SimplicialObject SSet.{u} ⥤ Type u :=
  (evaluation _ _).obj (op ⦋p⦌) ⋙ (evaluation _ _).obj (op ⦋q⦌)

def bisimplicialDegreeFunctor (C : Type w) [Category.{v} C] [HasCoproducts.{u} C]
    (p q : ℕ) : C ⥤ (SimplicialObject SSet.{u} ⥤ C) :=
  sigmaConst ⋙ (Functor.whiskeringLeft _ _ _).obj (bisimplicialEvaluationFunctor p q)

attribute [local simp] bisimplicialDegreeFunctor bisimplicialEvaluationFunctor
attribute [local simp←] bisimplicialRepresentableMap_comp

/-- The free coefficient functor in a bidegree is corepresented by the actual
product of standard simplices. This is the evaluation adjunction used to lift
natural maps from degreewise model generators. -/
def bisimplicialDegreeAdjunction (C : Type w) [Category.{v} C] [HasCoproducts.{u} C]
    (p q : ℕ) :
    bisimplicialDegreeFunctor C p q ⊣
      (evaluation _ _).obj (bisimplicialRepresentable.{u} p q) where
  unit.app M := Sigma.ι (fun _ : ((bisimplicialRepresentable p q).obj (op ⦋p⦌)).obj
    (op ⦋q⦌) => M) (bisimplicialRepresentableGenerator p q)
  counit.app F := { app X := Sigma.desc fun x => F.map (bisimplicialRepresentableMap X x) }
  left_triangle_components M := by
    apply NatTrans.ext
    funext X
    apply Sigma.hom_ext
    intro x
    dsimp
    simp [bisimplicialRepresentableMap_generator]
  right_triangle_components F := by
    dsimp
    simp

end Sharpness
