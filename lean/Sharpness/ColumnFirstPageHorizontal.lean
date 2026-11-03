import Sharpness.ColumnCokernelDifferentialExtension
import Sharpness.ColumnNatHorizontalDifferential

/-! Under the actual first-page vertical cohomology isomorphisms,
the native d1 is exactly the actual horizontal cohomology map. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness
open CategoryTheory CategoryTheory.Limits
variable {R : Type u} [CommRing R]
    (K : HomologicalComplex₂ (ModuleCat.{u} R) (ComplexShape.up ℕ) (ComplexShape.up ℕ))

set_option backward.isDefEq.respectTransparency false in
theorem totalColumnGradedVerticalComparison_degree (p q n : ℕ) (n' : ℤ) (hn : p+q=n)
    (hn' : ComplexShape.embeddingUpNat.f n=n') :
    (totalColumnGradedExtensionCohomologyIso K p n n' hn').hom ≫
      (totalColumnNatGradedCohomologyIsoAt K p q n hn).hom =
    HomologicalComplex.homologyMap (totalColumnAssociatedGradedExtendIso K p).hom n' ≫
      ((totalColumnNatAssociatedGraded K p).extendHomologyIso ComplexShape.embeddingUpNat
        (show ComplexShape.embeddingUpNat.f (p+q)=n' from hn ▸ hn')).hom ≫
          (totalColumnNatGradedCohomologyIso K p q).hom := by
  subst n
  simp only [totalColumnGradedExtensionCohomologyIso, totalColumnNatGradedCohomologyIsoAt,
    Iso.trans_hom, Functor.mapIso_hom, HomologicalComplex.homologyFunctor_map,
    eqToIso_refl, Iso.refl_hom, Category.id_comp, Category.assoc]

set_option backward.isDefEq.respectTransparency false in
theorem totalColumnCokernelDifferential_vertical (p q : ℕ) :
    totalColumnCokernelDifferential K p q ≫
      (totalColumnGradedExtensionCohomologyIso K (p+1) (p+q+1) (((p+1 : ℕ) : ℤ)+q) (by simp; omega)).hom ≫
        (totalColumnNatGradedCohomologyIsoAt K (p+1) q (p+q+1) (by omega)).hom =
    (totalColumnGradedExtensionCohomologyIso K p (p+q) ((p : ℤ)+q) (by simp)).hom ≫
      (totalColumnNatGradedCohomologyIso K p q).hom ≫ HomologicalComplex.homologyMap (K.d p (p+1)) q := by
  calc
    _ = ((totalColumnGradedExtensionCohomologyIso K p (p+q) ((p : ℤ)+q) (by simp)).hom ≫
        totalColumnNatCokernelDifferential K p q) ≫
        (totalColumnNatGradedCohomologyIsoAt K (p+1) q (p+q+1) (by omega)).hom := by
      rw [← Category.assoc, totalColumnCokernelDifferential_extension]
    _ = _ := by rw [Category.assoc, totalColumnNatCokernelDifferential_horizontal]

set_option backward.isDefEq.respectTransparency false in
theorem totalColumnFirstPageVerticalIso_d (p q : ℕ) :
    ((totalColumnSpectralSequence K).page 1).d (p,q) (p+1,q) ≫
        (totalColumnFirstPageVerticalIso K (p+1) q).hom =
      (totalColumnFirstPageVerticalIso K p q).hom ≫
        HomologicalComplex.homologyMap (K.d p (p+1)) q := by
  have hn := totalColumnGradedVerticalComparison_degree K (p+1) q (p+q+1)
    (((p+1 : ℕ) : ℤ)+q) (by omega) (by simp; omega)
  calc
    _ = (((totalColumnSpectralSequence K).page 1 (hr := le_rfl)).d (p,q) (p+1,q) ≫
          (totalColumnFirstPageAssociatedGradedIso K (p+1) q).hom) ≫
        (totalColumnGradedExtensionCohomologyIso K (p+1) (p+q+1) (((p+1 : ℕ) : ℤ)+q) (by simp; omega)).hom ≫
          (totalColumnNatGradedCohomologyIsoAt K (p+1) q (p+q+1) (by omega)).hom := by
      rw [Category.assoc, hn]
      simp only [totalColumnFirstPageVerticalIso, Iso.trans_hom, Functor.mapIso_hom,
        HomologicalComplex.homologyFunctor_map, Category.assoc]
    _ = (totalColumnFirstPageAssociatedGradedIso K p q).hom ≫
        totalColumnCokernelDifferential K p q ≫
          (totalColumnGradedExtensionCohomologyIso K (p+1) (p+q+1) (((p+1 : ℕ) : ℤ)+q) (by simp; omega)).hom ≫
            (totalColumnNatGradedCohomologyIsoAt K (p+1) q (p+q+1) (by omega)).hom := by
      rw [totalColumnFirstPageAssociatedGradedIso_d, Category.assoc]
    _ = (totalColumnFirstPageAssociatedGradedIso K p q).hom ≫
        (totalColumnGradedExtensionCohomologyIso K p (p+q) ((p : ℤ)+q) (by simp)).hom ≫
          (totalColumnNatGradedCohomologyIso K p q).hom ≫ HomologicalComplex.homologyMap (K.d p (p+1)) q := by
      rw [totalColumnCokernelDifferential_vertical]
    _ = _ := by
      simp only [totalColumnFirstPageVerticalIso, totalColumnGradedExtensionCohomologyIso,
        Iso.trans_hom, Functor.mapIso_hom, HomologicalComplex.homologyFunctor_map, Category.assoc]

end Sharpness
