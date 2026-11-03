import Sharpness.ColumnExtendedConnectingClasses
import Sharpness.ColumnNatGradedClassesAt

/-! The canonical integer-to-natural graded cohomology isomorphism,
with its formula on actual lifted vertical classes and their epimorphy. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness
open CategoryTheory CategoryTheory.Limits
variable {R : Type u} [CommRing R]
    (K : HomologicalComplex₂ (ModuleCat.{u} R) (ComplexShape.up ℕ) (ComplexShape.up ℕ))

def totalColumnGradedExtensionCohomologyIso (p n : ℕ) (n' : ℤ)
    (hn : ComplexShape.embeddingUpNat.f n=n') :
    (totalColumnAssociatedGraded K p).homology n' ≅ (totalColumnNatAssociatedGraded K p).homology n :=
  (HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℤ) n').mapIso
      (totalColumnAssociatedGradedExtendIso K p) ≪≫
    (totalColumnNatAssociatedGraded K p).extendHomologyIso ComplexShape.embeddingUpNat hn

set_option backward.isDefEq.respectTransparency false in
theorem totalColumnGradedExtensionCohomologyIso_class (p q : ℕ) :
    totalColumnIntVerticalCycleClass K p q ≫
      (totalColumnGradedExtensionCohomologyIso K p (p+q) ((p : ℤ)+q) (by simp)).hom =
    totalColumnNatVerticalCycleClass K p q := by
  simpa only [totalColumnGradedExtensionCohomologyIso, Iso.trans_hom, Functor.mapIso_hom,
    HomologicalComplex.homologyFunctor_map, Category.assoc] using totalColumnIntVerticalCycleClass_comparison K p q

theorem totalColumnIntVerticalCycleClass_epi (p q : ℕ) : Epi (totalColumnIntVerticalCycleClass K p q) := by
  letI := totalColumnNatVerticalCycleClass_epi K p q
  apply (epi_comp_iff_of_isIso _
    (totalColumnGradedExtensionCohomologyIso K p (p+q) ((p : ℤ)+q) (by simp)).hom).mp
  rw [totalColumnGradedExtensionCohomologyIso_class]
  infer_instance

end Sharpness
