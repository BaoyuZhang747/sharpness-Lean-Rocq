import Sharpness.ColumnGradedExtensionCohomology

/-! The actual adjacent-filtration connecting map commutes with the
canonical extension cohomology comparison. This is proved on the
epic family of actual vertical cycle classes, using both native
short-exact-sequence connecting maps. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness
open CategoryTheory CategoryTheory.Limits
variable {R : Type u} [CommRing R]
    (K : HomologicalComplex₂ (ModuleCat.{u} R) (ComplexShape.up ℕ) (ComplexShape.up ℕ))

theorem totalColumnExtendedConnectingTarget_closed (p q : ℕ) :
    totalColumnExtendedConnectingTarget K p q ≫
      ((totalColumnFiltrationIntFunctor K).obj (OrderDual.toDual (p+1))).d
        (((p+1 : ℕ) : ℤ)+q) (((p+1 : ℕ) : ℤ)+q+1) = 0 :=
  extensionDegreeLift_closed ComplexShape.embeddingUpNat (totalColumnFilteredComplex K (p+1))
    (p+q+1) (p+q+1+1) (((p+1 : ℕ) : ℤ)+q) (((p+1 : ℕ) : ℤ)+q+1)
      (by simp; omega) (by simp; omega)
      (totalColumnConnectingTarget K p q) (totalColumnConnectingTarget_closed K p q)

def totalColumnExtendedTargetClass (p q : ℕ) :
    (K.X p).cycles q ⟶
      ((totalColumnFiltrationIntFunctor K).obj (OrderDual.toDual (p+1))).homology (((p+1 : ℕ) : ℤ)+q) :=
  ((totalColumnFiltrationIntFunctor K).obj (OrderDual.toDual (p+1))).liftCycles
      (totalColumnExtendedConnectingTarget K p q) (((p+1 : ℕ) : ℤ)+q+1)
      ((ComplexShape.up ℤ).next_eq' rfl) (totalColumnExtendedConnectingTarget_closed K p q) ≫
    ((totalColumnFiltrationIntFunctor K).obj (OrderDual.toDual (p+1))).homologyπ (((p+1 : ℕ) : ℤ)+q)

set_option backward.isDefEq.respectTransparency false in
theorem totalColumnIntVerticalCycleClass_delta (p q : ℕ) :
    letI := totalColumnAdjacentIntMap_mono K p
    totalColumnIntVerticalCycleClass K p q ≫
      (monoCokernelShortComplex_shortExact (totalColumnAdjacentIntMap K p)).δ
        ((p : ℤ)+q) (((p+1 : ℕ) : ℤ)+q) (by change (p : ℤ)+q+1=(((p+1 : ℕ) : ℤ)+q); omega) =
    totalColumnExtendedTargetClass K p q := by
  letI := totalColumnAdjacentIntMap_mono K p
  exact (monoCokernelShortComplex_shortExact (totalColumnAdjacentIntMap K p)).δ_eq
    ((p : ℤ)+q) (((p+1 : ℕ) : ℤ)+q) (by change (p : ℤ)+q+1=(((p+1 : ℕ) : ℤ)+q); omega)
    (totalColumnExtendedQuotientCycle K p q) (totalColumnExtendedQuotientCycle_closed K p q)
    (totalColumnExtendedConnectingSource K p q) rfl (totalColumnExtendedConnectingTarget K p q)
    (totalColumnExtendedConnecting_lift K p q) (((p+1 : ℕ) : ℤ)+q+1) ((ComplexShape.up ℤ).next_eq' rfl)

set_option backward.isDefEq.respectTransparency false in
theorem totalColumnExtendedTargetClass_nat (p q : ℕ) :
    totalColumnExtendedTargetClass K p q ≫
      ((totalColumnFilteredComplex K (p+1)).extendHomologyIso ComplexShape.embeddingUpNat
        (show ComplexShape.embeddingUpNat.f (p+q+1)=(((p+1 : ℕ) : ℤ)+q) from by simp; omega)).hom =
    (totalColumnFilteredComplex K (p+1)).liftCycles (totalColumnConnectingTarget K p q)
        (p+q+1+1) ((ComplexShape.up ℕ).next_eq' rfl) (totalColumnConnectingTarget_closed K p q) ≫
      (totalColumnFilteredComplex K (p+1)).homologyπ (p+q+1) := by
  exact extensionDegreeLiftCycleClass ComplexShape.embeddingUpNat (totalColumnFilteredComplex K (p+1))
    (p+q+1) (p+q+1+1) (((p+1 : ℕ) : ℤ)+q) (((p+1 : ℕ) : ℤ)+q+1) (by simp; omega)
      ((ComplexShape.up ℕ).next_eq' rfl) ((ComplexShape.up ℤ).next_eq' rfl)
      (totalColumnConnectingTarget K p q) (totalColumnConnectingTarget_closed K p q)
      (totalColumnExtendedConnectingTarget_closed K p q)

set_option backward.isDefEq.respectTransparency false in
theorem totalColumnConnectingDelta_extension (p q : ℕ) :
    letI := totalColumnAdjacentIntMap_mono K p
    letI := totalColumnFilteredMap_mono K (Nat.le_succ p)
    (monoCokernelShortComplex_shortExact (totalColumnAdjacentIntMap K p)).δ
        ((p : ℤ)+q) (((p+1 : ℕ) : ℤ)+q) (by change (p : ℤ)+q+1=(((p+1 : ℕ) : ℤ)+q); omega) ≫
      ((totalColumnFilteredComplex K (p+1)).extendHomologyIso ComplexShape.embeddingUpNat
        (show ComplexShape.embeddingUpNat.f (p+q+1)=(((p+1 : ℕ) : ℤ)+q) from by simp; omega)).hom =
    (totalColumnGradedExtensionCohomologyIso K p (p+q) ((p : ℤ)+q) (by simp)).hom ≫
      (cochainCokernelSequence_shortExact (totalColumnFilteredMap K (Nat.le_succ p))).δ (p+q) (p+q+1) rfl := by
  letI := totalColumnAdjacentIntMap_mono K p
  letI := totalColumnFilteredMap_mono K (Nat.le_succ p)
  letI := totalColumnIntVerticalCycleClass_epi K p q
  apply (cancel_epi (totalColumnIntVerticalCycleClass K p q)).mp
  calc
    _ = totalColumnExtendedTargetClass K p q ≫
        ((totalColumnFilteredComplex K (p+1)).extendHomologyIso ComplexShape.embeddingUpNat (by simp; omega)).hom := by
      rw [← Category.assoc, totalColumnIntVerticalCycleClass_delta]
    _ = _ := (totalColumnExtendedTargetClass_nat K p q).trans
      ((totalColumnNatVerticalCycleClass_delta K p q).symm.trans (by
        rw [← totalColumnGradedExtensionCohomologyIso_class K p q, Category.assoc]))

end Sharpness
