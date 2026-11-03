import Sharpness.ColumnConnectingExtensionDelta
import Sharpness.ExtensionCokernelCohomology

/-! The actual integer quotient differential agrees with the actual
natural-number quotient differential under the canonical comparisons. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness
open CategoryTheory CategoryTheory.Limits
variable {R : Type u} [CommRing R]
    (K : HomologicalComplex₂ (ModuleCat.{u} R) (ComplexShape.up ℕ) (ComplexShape.up ℕ))

set_option backward.isDefEq.respectTransparency false in
theorem totalColumnCokernelProjection_extension (p q : ℕ) :
    HomologicalComplex.homologyMap (cokernel.π (totalColumnAdjacentIntMap K (p+1))) (((p+1 : ℕ) : ℤ)+q) ≫
      (totalColumnGradedExtensionCohomologyIso K (p+1) (p+q+1) (((p+1 : ℕ) : ℤ)+q) (by simp; omega)).hom =
    ((totalColumnFilteredComplex K (p+1)).extendHomologyIso ComplexShape.embeddingUpNat
      (show ComplexShape.embeddingUpNat.f (p+q+1)=(((p+1 : ℕ) : ℤ)+q) from by simp; omega)).hom ≫
        HomologicalComplex.homologyMap (cokernel.π (totalColumnFilteredMap K (Nat.le_succ (p+1)))) (p+q+1) := by
  exact extensionCokernelProjection_cohomology ComplexShape.embeddingUpNat
    (totalColumnFilteredMap K (Nat.le_succ (p+1))) (p+q+1) (((p+1 : ℕ) : ℤ)+q) (by simp; omega)

set_option backward.isDefEq.respectTransparency false in
theorem totalColumnCokernelDifferential_extension (p q : ℕ) :
    totalColumnCokernelDifferential K p q ≫
      (totalColumnGradedExtensionCohomologyIso K (p+1) (p+q+1) (((p+1 : ℕ) : ℤ)+q) (by simp; omega)).hom =
    (totalColumnGradedExtensionCohomologyIso K p (p+q) ((p : ℤ)+q) (by simp)).hom ≫
      totalColumnNatCokernelDifferential K p q := by
  letI := totalColumnAdjacentIntMap_mono K p
  letI := totalColumnFilteredMap_mono K (Nat.le_succ p)
  calc
    _ = (monoCokernelShortComplex_shortExact (totalColumnAdjacentIntMap K p)).δ
        ((p : ℤ)+q) (((p+1 : ℕ) : ℤ)+q) (by change (p : ℤ)+q+1=(((p+1 : ℕ) : ℤ)+q); omega) ≫
      ((totalColumnFilteredComplex K (p+1)).extendHomologyIso ComplexShape.embeddingUpNat
        (show ComplexShape.embeddingUpNat.f (p+q+1)=(((p+1 : ℕ) : ℤ)+q) from by simp; omega)).hom ≫
      HomologicalComplex.homologyMap (cokernel.π (totalColumnFilteredMap K (Nat.le_succ (p+1)))) (p+q+1) := by
      simp only [totalColumnCokernelDifferential, Category.assoc, totalColumnCokernelProjection_extension]
    _ = _ := by
      rw [← Category.assoc, totalColumnConnectingDelta_extension]
      simp only [totalColumnNatCokernelDifferential, Category.assoc]

end Sharpness
