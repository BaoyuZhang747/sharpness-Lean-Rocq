import Sharpness.Unconditional.CentricKanAcyclicity

/-! The actual span evaluations of the right Kan coefficient, with their
source and target naturality identities. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
noncomputable section
universe u
namespace Sharpness
open CategoryTheory CategoryTheory.Limits Opposite

variable (R : Type u) [CommRing R] {C : Type u} [Category.{u} C]
    (P : C) (M : CoefficientCategory R C)

abbrev overRanCoefficient : CoefficientCategory R C :=
  (Over.forget P).op.ran.obj ((Over.forget P).op ⋙ M)

/-- Evaluation at an actual span, using the Kan counit. -/
def overRanEvaluation {X Q : C} (a : X ⟶ P) (b : X ⟶ Q) :
    (overRanCoefficient R P M).obj (op Q) ⟶ M.obj (op X) :=
  (overRanCoefficient R P M).map b.op ≫
    ((Over.forget P).op.ranCounit.app ((Over.forget P).op ⋙ M)).app (op (Over.mk a))

/-- Changing the right target is the actual contravariant functor map. -/
@[reassoc]
theorem overRanEvaluation_postcomp {X Q Q' : C} (a : X ⟶ P) (b : X ⟶ Q')
    (f : Q' ⟶ Q) :
    (overRanCoefficient R P M).map f.op ≫ overRanEvaluation R P M a b =
      overRanEvaluation R P M a (b ≫ f) := by
  simp only [overRanEvaluation, op_comp, Functor.map_comp, Category.assoc]

/-- Changing the span apex is restriction along its actual arrow. -/
@[reassoc]
theorem overRanEvaluation_precomp {X Y Q : C} (h : X ⟶ Y)
    (a : Y ⟶ P) (b : Y ⟶ Q) :
    overRanEvaluation R P M (h ≫ a) (h ≫ b) =
      overRanEvaluation R P M a b ≫ M.map h.op := by
  let k : Over.mk (h ≫ a) ⟶ Over.mk a := Over.homMk h
  have hn := (((Over.forget P).op.ranCounit.app
    ((Over.forget P).op ⋙ M)).naturality k.op)
  change (overRanCoefficient R P M).map h.op ≫ _ = _ ≫ M.map h.op at hn
  simp only [overRanEvaluation, op_comp, Functor.map_comp, Category.assoc]
  rw [hn]

/-- Span evaluation is the corresponding coordinate of the product formula. -/
theorem overRanEvaluation_eq_coordinate {Q : C} (E : ProductDecomposition P Q)
    (i : E.Index) :
    overRanEvaluation R P M (E.left i) (E.right i) =
      (overRanObjIsoProduct R P Q E ((Over.forget P).op ⋙ M)).hom ≫ Pi.π _ i :=
  (overRanObjIsoProduct_hom_π R P Q E ((Over.forget P).op ⋙ M) i).symm

end Sharpness
