import Sharpness.Unconditional.BurnsideSliceMarks
import Sharpness.Unconditional.BurnsideMarkedAlgebra

/-! The actual unital centric slice Burnside algebra and its action on every
restricted Mackey module. Unit detection uses its genuine table of marks. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u v w

namespace Sharpness.FusionSystem
open CategoryTheory Burnside
variable {S : Type v} [Group S] [Finite S] (F : FusionSystem S)
    (R : Type u) [CommRing R]

local instance centricFinite : Finite F.CentricOrbit :=
  Finite.of_injective (fun X : F.CentricOrbit => X.obj)
    (fun _ _ h => ObjectProperty.FullSubcategory.ext h)

local instance centricSliceAlgebraHomFinite (X Y : F.CentricOrbit) : Finite (X ⟶ Y) :=
  Finite.of_injective (fun f : X ⟶ Y => f.hom) (fun _ _ h => InducedCategory.hom_ext h)

/-- Actual marks, product, and unit data; every field is constructed from
the centric orbit category and its concrete double-coset spans. -/
def centricSliceMarkedAlgebra [IsDomain R] [CharZero R] (P : F.CentricOrbit) :
    MarkedAlgebraData R (Skeleton (Over P)) where
  mark := virtualObjectMarks R
  mark_injective := by
    classical
    letI := Fintype.ofFinite (Skeleton (Over P))
    rw [virtualObjectMarks_eq_matrix]
    exact (centric_slice_additiveMarkMap_injective (R := R) F P).comp
      (Finsupp.linearEquivFunOnFinite R R (Skeleton (Over P))).injective
  unit := F.virtualSliceUnit R P
  mul := F.virtualSliceProduct R P
  mark_unit := F.virtualSliceUnit_marks R P
  mark_mul := F.virtualSliceProduct_marks R P

theorem centricSliceMarkedAlgebra_table_det [IsDomain R] [CharZero R]
    (P : F.CentricOrbit) :
    letI := Fintype.ofFinite (Skeleton (Over P))
    letI := Classical.decEq (Skeleton (Over P))
    (F.centricSliceMarkedAlgebra R P).table.det ≠ 0 := by
  classical
  letI := Fintype.ofFinite (Skeleton (Over P))
  have heq : (F.centricSliceMarkedAlgebra R P).table =
      homCountMatrix R (fromSkeleton (Over P)).obj := by
    ext i j
    simp [MarkedAlgebraData.table, centricSliceMarkedAlgebra, objectMark, homCountMatrix]
  rw [heq]
  exact centric_slice_markMatrix_det_ne_zero F P

variable (M : RestrictedMackeyModule.{u,v,w} R F.Orbit F.mackeyShape
    (fun P => F.IsCentric P.as.subgroup)) (P : F.CentricOrbit)

theorem virtualSliceAction_unit : M.virtualSliceAction P (F.virtualSliceUnit R P) = 1 := by
  change M.virtualSliceAction P (Finsupp.single (toSkeleton (Over.mk (𝟙 P))) 1) = 1
  rw [M.virtualSliceAction_object, M.sliceOperator_id]
  rfl

theorem virtualSliceAction_generators (A B : Over P) :
    M.virtualSliceAction P (F.virtualSliceProductGenerators R P A B) =
      M.sliceOperator A * M.sliceOperator B := by
  rw [virtualSliceProductGenerators, map_sum]
  simp only [M.virtualSliceAction_object]
  exact (F.centricSliceOperator_comp M A.hom B.hom).symm

theorem virtualSliceAction_mul (a b : Skeleton (Over P) →₀ R) :
    M.virtualSliceAction P (F.virtualSliceProduct R P a b) =
      M.virtualSliceAction P a * M.virtualSliceAction P b := by
  induction a using Finsupp.induction_linear with
  | zero => simp
  | add a₁ a₂ h₁ h₂ => simp [map_add, h₁, h₂, add_mul]
  | single A r =>
    induction b using Finsupp.induction_linear with
    | zero => simp
    | add b₁ b₂ h₁ h₂ => simp [map_add, h₁, h₂, mul_add]
    | single B s =>
      rw [F.virtualSliceProduct_single, map_smul, map_smul,
        F.virtualSliceAction_generators R M P]
      simp [M.virtualSliceAction_single, smul_smul, mul_comm]

/-- An actual virtual centric slice object whose marks are all units acts
invertibly on every restricted Mackey module. -/
theorem centricSliceAction_isUnit_of_marks [IsDomain R] [CharZero R]
    (a : Skeleton (Over P) →₀ R)
    (ha : ∀ i, IsUnit (virtualObjectMarks R a i)) :
    IsUnit (M.virtualSliceAction P a) := by
  classical
  letI := Fintype.ofFinite (Skeleton (Over P))
  exact (F.centricSliceMarkedAlgebra R P).isUnit_action_of_marks
    (M.virtualSliceAction P) (F.virtualSliceAction_unit R M P)
    (F.virtualSliceAction_mul R M P)
    (F.centricSliceMarkedAlgebra_table_det R P) a ha

end Sharpness.FusionSystem
