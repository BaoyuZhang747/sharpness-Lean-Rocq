import Sharpness.Unconditional.BurnsideSliceAlgebra
import Sharpness.Unconditional.BurnsideTopMarks

/-! The actual top-product operator is invertible on every restricted
Mackey module over the prime-local coefficient ring. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u w

namespace Sharpness.FusionSystem
open CategoryTheory
variable {S : Type u} [Group S] [Finite S] (F : FusionSystem S)
    (p : ℕ) [Fact p.Prime] (hS : IsPGroup p S) (sat : F.Saturated p)
    (M : RestrictedMackeyModule.{u,u,w} (PrimeLocalRing.{u} p) F.Orbit F.mackeyShape
      (fun P => F.IsCentric P.as.subgroup)) {P : F.CentricOrbit}
    (D : ProductDecomposition P F.centricTopObject)

include hS sat

/-- The top-product virtual slice has unit marks, hence acts as an actual
invertible linear operator. Saturation enters through the proved Hom counts. -/
theorem topProductAction_isUnit :
    IsUnit (M.virtualSliceAction P (D.virtualProductSlice (PrimeLocalRing.{u} p))) :=
  F.centricSliceAction_isUnit_of_marks (PrimeLocalRing.{u} p) M P _
    (fun i => F.virtualTopProduct_marks_isUnit p hS sat D i)

/-- The same statement as invertibility of a morphism in the project's
actual coefficient category. -/
theorem topProductAction_isIso :
    IsIso (ModuleCat.ofHom
      (M.virtualSliceAction P (D.virtualProductSlice (PrimeLocalRing.{u} p)))) := by
  rw [ConcreteCategory.isIso_iff_bijective]
  exact (Module.End.isUnit_iff _).mp (F.topProductAction_isUnit p hS sat M D)

omit hS sat in
theorem topProductAction_eq_sum :
    letI := Fintype.ofFinite D.Index
    M.virtualSliceAction P (D.virtualProductSlice (PrimeLocalRing.{u} p)) =
      ∑ i : D.Index, (M.push (D.left i)).comp (M.pull (D.left i)) := by
  classical
  letI := Fintype.ofFinite D.Index
  rw [ProductDecomposition.virtualProductSlice, map_sum]
  simp only [M.virtualSliceAction_object, RestrictedMackeyModule.sliceOperator]
  rfl

/-- A directly usable version for the pull--transfer composite, expressed
entirely through the actual legs of the finite top-product decomposition. -/
theorem topProductPushPull_isUnit :
    letI := Fintype.ofFinite D.Index
    IsUnit (∑ i : D.Index, (M.push (D.left i)).comp (M.pull (D.left i))) := by
  classical
  letI := Fintype.ofFinite D.Index
  rw [← F.topProductAction_eq_sum p M D]
  exact F.topProductAction_isUnit p hS sat M D

theorem topProductPushPull_isIso :
    letI := Fintype.ofFinite D.Index
    IsIso (ModuleCat.ofHom
      (∑ i : D.Index, (M.push (D.left i)).comp (M.pull (D.left i)))) := by
  classical
  letI := Fintype.ofFinite D.Index
  rw [ConcreteCategory.isIso_iff_bijective]
  exact (Module.End.isUnit_iff _).mp (F.topProductPushPull_isUnit p hS sat M D)

end Sharpness.FusionSystem
