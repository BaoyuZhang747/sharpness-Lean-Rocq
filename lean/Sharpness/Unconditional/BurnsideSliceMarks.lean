import Sharpness.Unconditional.BurnsideSliceProduct
import Mathlib.LinearAlgebra.Finsupp.VectorSpace

/-! Concrete additive marks and products for the centric slice Burnside
algebra. The multiplication is defined by actual intersection subgroups. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u v w

namespace Sharpness.Burnside
open CategoryTheory
variable (R : Type u) [CommRing R] {C : Type v} [Category.{v} C]

def objectMark (A : C) : Skeleton C → R :=
  fun X => (Nat.card ((fromSkeleton C).obj X ⟶ A) : R)

def virtualObjectMarks : (Skeleton C →₀ R) →ₗ[R] (Skeleton C → R) :=
  Finsupp.linearCombination R (fun A => objectMark R ((fromSkeleton C).obj A))

theorem objectMark_eq_of_iso {A B : C} (e : A ≅ B) : objectMark R A = objectMark R B := by
  funext X
  exact congrArg (Nat.cast : ℕ → R) (Nat.card_congr e.homToEquiv)

@[simp] theorem virtualObjectMarks_single (A : Skeleton C) (r : R) :
    virtualObjectMarks R (Finsupp.single A r) = r • objectMark R ((fromSkeleton C).obj A) := by
  simp [virtualObjectMarks]

theorem virtualObjectMarks_object (A : C) :
    virtualObjectMarks R (Finsupp.single (toSkeleton A) 1) = objectMark R A := by
  rw [virtualObjectMarks_single, one_smul]
  exact objectMark_eq_of_iso R (fromSkeletonToSkeletonIso A)

theorem virtualObjectMarks_eq_matrix [Finite C] :
    letI := Fintype.ofFinite (Skeleton C)
    virtualObjectMarks (C := C) R =
      (additiveMarkMap R (fromSkeleton C).obj).comp
        (Finsupp.linearEquivFunOnFinite R R (Skeleton C)).toLinearMap := by
  classical
  letI := Fintype.ofFinite (Skeleton C)
  apply Finsupp.lhom_ext
  intro A r
  ext X
  simp [virtualObjectMarks_single, objectMark, additiveMarkMap, homCountMatrix,
    Matrix.mulVec, dotProduct, Pi.single_apply, mul_comm]

theorem virtualObjectMarks_injective [Finite C] [∀ A B : C, Finite (A ⟶ B)]
    [IsDomain R] [CharZero R]
    (rank : C → ℕ)
    (rank_mono : ∀ {A B : C}, (A ⟶ B) → rank A ≤ rank B)
    (iso_of_rank : ∀ {A B : C} (f : A ⟶ B), rank A = rank B → IsIso f) :
    Function.Injective (virtualObjectMarks (C := C) R) := by
  classical
  letI := Fintype.ofFinite (Skeleton C)
  rw [virtualObjectMarks_eq_matrix]
  exact (additiveMarkMap_injective rank rank_mono iso_of_rank (fromSkeleton C).obj
    (fun i j e => skeleton_skeletal C ⟨(fromSkeleton C).preimageIso e⟩)).comp
      (Finsupp.linearEquivFunOnFinite R R (Skeleton C)).injective

end Sharpness.Burnside

namespace Sharpness.FusionSystem
open CategoryTheory Burnside
variable {S : Type v} [Group S] [Finite S] (F : FusionSystem S)
    (R : Type u) [CommRing R] (P : F.CentricOrbit)

def virtualSliceUnit : Skeleton (Over P) →₀ R :=
  Finsupp.single (toSkeleton (Over.mk (𝟙 P))) 1

def virtualSliceProductGenerators (A B : Over P) : Skeleton (Over P) →₀ R :=
  ∑ i : RestrictedTerm F.mackeyShape (fun Q => F.IsCentric Q.as.subgroup) A.hom B.hom,
    Finsupp.single (toSkeleton (F.centricSliceProductTerm A B i)) 1

def virtualSliceProduct : (Skeleton (Over P) →₀ R) →ₗ[R]
    (Skeleton (Over P) →₀ R) →ₗ[R] (Skeleton (Over P) →₀ R) :=
  Finsupp.linearCombination R (fun A => Finsupp.linearCombination R
    (fun B => F.virtualSliceProductGenerators R P
      ((fromSkeleton (Over P)).obj A) ((fromSkeleton (Over P)).obj B)))

theorem virtualSliceProduct_single (A B : Skeleton (Over P)) (r s : R) :
    F.virtualSliceProduct R P (Finsupp.single A r) (Finsupp.single B s) =
      r • s • F.virtualSliceProductGenerators R P
        ((fromSkeleton (Over P)).obj A) ((fromSkeleton (Over P)).obj B) := by
  simp [virtualSliceProduct]

omit [Finite S] in
theorem virtualSliceUnit_marks :
    virtualObjectMarks R (F.virtualSliceUnit R P) = 1 := by
  rw [virtualSliceUnit, virtualObjectMarks_object]
  ext X
  letI : Unique ((fromSkeleton (Over P)).obj X ⟶ Over.mk (𝟙 P)) :=
    { default := (Over.mkIdTerminal (X := P)).from _
      uniq := fun a => (Over.mkIdTerminal (X := P)).hom_ext a _ }
  change (Nat.card ((fromSkeleton (Over P)).obj X ⟶ Over.mk (𝟙 P)) : R) = 1
  rw [Nat.card_unique, Nat.cast_one]

theorem virtualSliceProductGenerators_marks (A B : Over P) :
    virtualObjectMarks R (F.virtualSliceProductGenerators R P A B) =
      objectMark R A * objectMark R B := by
  classical
  rw [virtualSliceProductGenerators, map_sum]
  simp only [virtualObjectMarks_object]
  ext X
  simp only [Finset.sum_apply, Pi.mul_apply]
  change (∑ i : RestrictedTerm F.mackeyShape (fun Q => F.IsCentric Q.as.subgroup) A.hom B.hom,
    (Nat.card ((fromSkeleton (Over P)).obj X ⟶ F.centricSliceProductTerm A B i) : R)) =
    (Nat.card ((fromSkeleton (Over P)).obj X ⟶ A) : R) *
      (Nat.card ((fromSkeleton (Over P)).obj X ⟶ B) : R)
  simpa only [Nat.cast_sum, Nat.cast_mul] using!
    congrArg (fun n : ℕ => (n : R))
      (F.centricSliceProduct_card A B ((fromSkeleton (Over P)).obj X))

theorem virtualSliceProduct_marks (a b : Skeleton (Over P) →₀ R) :
    virtualObjectMarks R (F.virtualSliceProduct R P a b) =
      virtualObjectMarks R a * virtualObjectMarks R b := by
  induction a using Finsupp.induction_linear with
  | zero => simp
  | add a₁ a₂ h₁ h₂ => simp [map_add, h₁, h₂, add_mul]
  | single A r =>
    induction b using Finsupp.induction_linear with
    | zero => simp
    | add b₁ b₂ h₁ h₂ => simp [map_add, h₁, h₂, mul_add]
    | single B s =>
      rw [F.virtualSliceProduct_single, map_smul, map_smul,
        F.virtualSliceProductGenerators_marks]
      simp [smul_smul, mul_comm]

end Sharpness.FusionSystem
