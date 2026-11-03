import Sharpness.ColumnConnectingLifts
import Sharpness.ColumnNatAssociatedGraded
import Sharpness.CochainCokernelConnecting

/-! Compute the actual adjacent-quotient connecting map on the lifted
vertical cycles. The output class is represented by the actual
horizontal differential; no connecting-map formula is assumed. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness
open CategoryTheory CategoryTheory.Limits
variable {R : Type u} [CommRing R]
    (K : HomologicalComplex₂ (ModuleCat.{u} R) (ComplexShape.up ℕ) (ComplexShape.up ℕ))

def totalColumnConnectingSource (p q : ℕ) :
    (K.X p).cycles q ⟶ (totalColumnFilteredComplex K p).X (p+q) :=
  (K.X p).iCycles q ≫ totalColumnSummandLift K p q

def totalColumnConnectingTarget (p q : ℕ) :
    (K.X p).cycles q ⟶ (totalColumnFilteredComplex K (p+1)).X (p+q+1) :=
  (K.X p).iCycles q ≫ (K.d p (p+1)).f q ≫
    totalColumnSummandLiftAt K (p+1) q (p+q+1) (by omega)

theorem totalColumnConnecting_lift (p q : ℕ) :
    totalColumnConnectingTarget K p q ≫ (totalColumnFilteredMap K (Nat.le_succ p)).f (p+q+1) =
      totalColumnConnectingSource K p q ≫ (totalColumnFilteredComplex K p).d (p+q) (p+q+1) :=
  totalColumnCycle_filtered_d K p q

def totalColumnConnectingQuotientCycle (p q : ℕ) :
    (K.X p).cycles q ⟶ (totalColumnNatAssociatedGraded K p).X (p+q) :=
  totalColumnConnectingSource K p q ≫ (cokernel.π (totalColumnFilteredMap K (Nat.le_succ p))).f (p+q)

theorem totalColumnConnectingQuotientCycle_closed (p q : ℕ) :
    totalColumnConnectingQuotientCycle K p q ≫
      (totalColumnNatAssociatedGraded K p).d (p+q) (p+q+1) = 0 :=
  cochainCokernel_projection_cycle (totalColumnFilteredMap K (Nat.le_succ p))
    (p+q) (p+q+1) (totalColumnConnectingSource K p q)
      (totalColumnConnectingTarget K p q) (totalColumnConnecting_lift K p q)

theorem totalColumnConnectingTarget_closed (p q : ℕ) :
    totalColumnConnectingTarget K p q ≫
      (totalColumnFilteredComplex K (p+1)).d (p+q+1) (p+q+1+1) = 0 := by
  letI := totalColumnFilteredMap_mono K (Nat.le_succ p)
  apply (cancel_mono ((totalColumnFilteredMap K (Nat.le_succ p)).f (p+q+1+1))).mp
  calc
    _ = (totalColumnConnectingTarget K p q ≫
        (totalColumnFilteredMap K (Nat.le_succ p)).f (p+q+1)) ≫
        (totalColumnFilteredComplex K p).d (p+q+1) (p+q+1+1) := by
      rw [Category.assoc, ← (totalColumnFilteredMap K (Nat.le_succ p)).comm]
      exact (Category.assoc _ _ _).symm
    _ = 0 := by
      rw [totalColumnConnecting_lift, Category.assoc, HomologicalComplex.d_comp_d, comp_zero]
    _ = _ := (zero_comp).symm

def totalColumnNatVerticalCycleClass (p q : ℕ) :
    (K.X p).cycles q ⟶ (totalColumnNatAssociatedGraded K p).homology (p+q) :=
  (totalColumnNatAssociatedGraded K p).liftCycles (totalColumnConnectingQuotientCycle K p q)
      (p+q+1) ((ComplexShape.up ℕ).next_eq' rfl)
      (totalColumnConnectingQuotientCycle_closed K p q) ≫
    (totalColumnNatAssociatedGraded K p).homologyπ (p+q)

set_option backward.isDefEq.respectTransparency false in
theorem totalColumnNatVerticalCycleClass_delta (p q : ℕ) :
    letI := totalColumnFilteredMap_mono K (Nat.le_succ p)
    totalColumnNatVerticalCycleClass K p q ≫
      (cochainCokernelSequence_shortExact (totalColumnFilteredMap K (Nat.le_succ p))).δ
        (p+q) (p+q+1) rfl =
    (totalColumnFilteredComplex K (p+1)).liftCycles (totalColumnConnectingTarget K p q)
        (p+q+1+1) ((ComplexShape.up ℕ).next_eq' rfl)
        (totalColumnConnectingTarget_closed K p q) ≫
      (totalColumnFilteredComplex K (p+1)).homologyπ (p+q+1) := by
  letI := totalColumnFilteredMap_mono K (Nat.le_succ p)
  exact (cochainCokernelSequence_shortExact (totalColumnFilteredMap K (Nat.le_succ p))).δ_eq
    (p+q) (p+q+1) rfl (totalColumnConnectingQuotientCycle K p q)
      (totalColumnConnectingQuotientCycle_closed K p q)
      (totalColumnConnectingSource K p q) rfl (totalColumnConnectingTarget K p q)
      (totalColumnConnecting_lift K p q) (p+q+1+1) ((ComplexShape.up ℕ).next_eq' rfl)

def totalColumnNatCokernelDifferential (p q : ℕ) :
    (totalColumnNatAssociatedGraded K p).homology (p+q) ⟶
      (totalColumnNatAssociatedGraded K (p+1)).homology (p+q+1) := by
  letI := totalColumnFilteredMap_mono K (Nat.le_succ p)
  exact (cochainCokernelSequence_shortExact (totalColumnFilteredMap K (Nat.le_succ p))).δ
      (p+q) (p+q+1) rfl ≫
    HomologicalComplex.homologyMap (cokernel.π (totalColumnFilteredMap K (Nat.le_succ (p+1)))) (p+q+1)

set_option backward.isDefEq.respectTransparency false in
theorem totalColumnNatVerticalCycleClass_d (p q : ℕ) :
    totalColumnNatVerticalCycleClass K p q ≫ totalColumnNatCokernelDifferential K p q =
    (totalColumnFilteredComplex K (p+1)).liftCycles (totalColumnConnectingTarget K p q)
        (p+q+1+1) ((ComplexShape.up ℕ).next_eq' rfl)
        (totalColumnConnectingTarget_closed K p q) ≫
      (totalColumnFilteredComplex K (p+1)).homologyπ (p+q+1) ≫
        HomologicalComplex.homologyMap
          (cokernel.π (totalColumnFilteredMap K (Nat.le_succ (p+1)))) (p+q+1) := by
  have h := congrArg (fun t => t ≫ HomologicalComplex.homologyMap
      (cokernel.π (totalColumnFilteredMap K (Nat.le_succ (p+1)))) (p+q+1))
    (totalColumnNatVerticalCycleClass_delta K p q)
  simpa only [totalColumnNatCokernelDifferential, Category.assoc] using h

end Sharpness
