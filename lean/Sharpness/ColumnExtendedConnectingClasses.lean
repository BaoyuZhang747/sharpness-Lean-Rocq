import Sharpness.ColumnConnectingClasses
import Sharpness.ColumnFirstCokernelDifferential
import Sharpness.ColumnFirstPageVertical
import Sharpness.ExtensionConnectingClasses

/-! Actual integer-indexed lifts for the native column spectral object.
The canonical quotient comparison sends their cycle class to the
previously computed natural-number quotient cycle class. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness
open CategoryTheory CategoryTheory.Limits
variable {R : Type u} [CommRing R]
    (K : HomologicalComplex₂ (ModuleCat.{u} R) (ComplexShape.up ℕ) (ComplexShape.up ℕ))

def totalColumnExtendedConnectingSource (p q : ℕ) :
    (K.X p).cycles q ⟶ ((totalColumnFiltrationIntFunctor K).obj (OrderDual.toDual p)).X ((p : ℤ)+q) :=
  extensionDegreeLift ComplexShape.embeddingUpNat (totalColumnFilteredComplex K p)
    (p+q) ((p : ℤ)+q) (by simp) (totalColumnConnectingSource K p q)

def totalColumnExtendedConnectingTarget (p q : ℕ) :
    (K.X p).cycles q ⟶ ((totalColumnFiltrationIntFunctor K).obj (OrderDual.toDual (p+1))).X (((p+1 : ℕ) : ℤ)+q) :=
  extensionDegreeLift ComplexShape.embeddingUpNat (totalColumnFilteredComplex K (p+1))
    (p+q+1) (((p+1 : ℕ) : ℤ)+q) (by simp; omega) (totalColumnConnectingTarget K p q)

set_option backward.isDefEq.respectTransparency false in
theorem totalColumnExtendedConnecting_lift (p q : ℕ) :
    totalColumnExtendedConnectingTarget K p q ≫
        (totalColumnAdjacentIntMap K p).f (((p+1 : ℕ) : ℤ)+q) =
    totalColumnExtendedConnectingSource K p q ≫
      ((totalColumnFiltrationIntFunctor K).obj (OrderDual.toDual p)).d
        ((p : ℤ)+q) (((p+1 : ℕ) : ℤ)+q) :=
  extensionConnectingLift_relation ComplexShape.embeddingUpNat
    (totalColumnFilteredMap K (Nat.le_succ p)) (p+q) (p+q+1)
      ((p : ℤ)+q) (((p+1 : ℕ) : ℤ)+q) (by simp) (by simp; omega)
      (totalColumnConnectingSource K p q) (totalColumnConnectingTarget K p q)
      (totalColumnConnecting_lift K p q)

def totalColumnExtendedQuotientCycle (p q : ℕ) :
    (K.X p).cycles q ⟶ (totalColumnAssociatedGraded K p).X ((p : ℤ)+q) :=
  totalColumnExtendedConnectingSource K p q ≫ (cokernel.π (totalColumnAdjacentIntMap K p)).f ((p : ℤ)+q)

theorem totalColumnExtendedQuotientCycle_closed (p q : ℕ) :
    totalColumnExtendedQuotientCycle K p q ≫ (totalColumnAssociatedGraded K p).d
      ((p : ℤ)+q) (((p+1 : ℕ) : ℤ)+q) = 0 :=
  cochainCokernel_projection_cycle (totalColumnAdjacentIntMap K p)
    ((p : ℤ)+q) (((p+1 : ℕ) : ℤ)+q) (totalColumnExtendedConnectingSource K p q)
      (totalColumnExtendedConnectingTarget K p q) (totalColumnExtendedConnecting_lift K p q)

def totalColumnIntVerticalCycleClass (p q : ℕ) :
    (K.X p).cycles q ⟶ (totalColumnAssociatedGraded K p).homology ((p : ℤ)+q) :=
  (totalColumnAssociatedGraded K p).liftCycles (totalColumnExtendedQuotientCycle K p q)
      (((p+1 : ℕ) : ℤ)+q) ((ComplexShape.up ℤ).next_eq' (by change (p : ℤ)+q+1=(((p+1 : ℕ) : ℤ)+q); omega))
      (totalColumnExtendedQuotientCycle_closed K p q) ≫
    (totalColumnAssociatedGraded K p).homologyπ ((p : ℤ)+q)

set_option backward.isDefEq.respectTransparency false in
theorem totalColumnIntVerticalCycleClass_comparison (p q : ℕ) :
    totalColumnIntVerticalCycleClass K p q ≫
      HomologicalComplex.homologyMap (totalColumnAssociatedGradedExtendIso K p).hom ((p : ℤ)+q) ≫
        ((totalColumnNatAssociatedGraded K p).extendHomologyIso ComplexShape.embeddingUpNat (by simp)).hom =
    totalColumnNatVerticalCycleClass K p q :=
  extensionCokernelCycleClass_comparison ComplexShape.embeddingUpNat
    (totalColumnFilteredMap K (Nat.le_succ p)) (p+q) (p+q+1)
      ((p : ℤ)+q) (((p+1 : ℕ) : ℤ)+q) (by simp) (by simp; omega)
      ((ComplexShape.up ℕ).next_eq' rfl)
      ((ComplexShape.up ℤ).next_eq' (by change (p : ℤ)+q+1=(((p+1 : ℕ) : ℤ)+q); omega))
      (totalColumnConnectingSource K p q) (totalColumnConnectingQuotientCycle_closed K p q)
      (totalColumnExtendedQuotientCycle_closed K p q)

end Sharpness
