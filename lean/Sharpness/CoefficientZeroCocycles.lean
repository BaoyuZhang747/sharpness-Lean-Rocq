import Sharpness.CoefficientLowDifferential

/-! Degree-zero cocycles in the actual coefficient complex are exactly
compatible families. This is an explicit calculation of the first
actual differential, without a higher-limit comparison input. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness
open CategoryTheory Simplicial Opposite
variable {R C : Type u} [CommRing R] [Category.{u} C]
    (M : Cᵒᵖ ⥤ ModuleCat.{u} R)

set_option backward.isDefEq.respectTransparency false in
theorem coefficientZeroDifferential_component (x : (coefficientCochains M).X 0) {P Q : C} (f : P ⟶ Q) :
    (coefficientCochains M).d 0 1 x (ComposableArrows.mk₁ f) =
      M.map f.op (x (ComposableArrows.mk₀ Q)) - (show M.obj (op P) from x (ComposableArrows.mk₀ P)) := by
  exact congrArg (fun t => t x) (coefficientZeroDifferential_evaluation M f)

set_option backward.isDefEq.respectTransparency false in
theorem coefficientZero_closed_iff (x : (coefficientCochains M).X 0) :
    (coefficientCochains M).d 0 1 x=0 ↔
      ∀ {P Q : C} (f : P ⟶ Q), M.map f.op (x (ComposableArrows.mk₀ Q))=x (ComposableArrows.mk₀ P) := by
  constructor
  · intro hx P Q f
    apply sub_eq_zero.mp
    exact (coefficientZeroDifferential_component M x f).symm.trans
      (congrArg (fun y => y (ComposableArrows.mk₁ f)) hx)
  · intro hx
    apply funext
    intro s
    obtain ⟨P,Q,f,rfl⟩ := ComposableArrows.mk₁_surjective s
    exact (coefficientZeroDifferential_component M x f).trans (sub_eq_zero.mpr (hx f))

set_option backward.isDefEq.respectTransparency false in
theorem coefficientZero_hom_ext {X : ModuleCat.{u} R} {f g : X ⟶ (coefficientCochains M).X 0}
    (h : ∀ P : C, f ≫ coefficientZeroEvaluation M P = g ≫ coefficientZeroEvaluation M P) : f=g := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply funext
  intro s
  obtain ⟨P,rfl⟩ := ComposableArrows.mk₀_surjective s
  exact congrArg (fun t => t x) (h P)

end Sharpness
