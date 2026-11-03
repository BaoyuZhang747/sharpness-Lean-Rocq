import Sharpness.TotalDualHorizontal
import Sharpness.TotalDualVertical

/-! The canonical degreewise comparison commutes with the full signed
total differential. It is consequently an isomorphism of actual
cochain complexes for arbitrary coefficient module A. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness
open CategoryTheory
variable {R : Type u} [CommRing R]
    (K : HomologicalComplex₂ (ModuleCat.{u} R) (ComplexShape.down ℕ) (ComplexShape.down ℕ))
    (A : ModuleCat.{u} R)

set_option backward.isDefEq.respectTransparency false in
theorem totalDualDegreeIso_inv_comm (n : ℕ) :
    (totalDualDegreeIso K A n).inv ≫ ((dualNatBicomplex K A).total (ComplexShape.up ℕ)).d n (n+1) =
      (ChainComplex.linearYonedaObj (K.total (ComplexShape.down ℕ)) R A).d n (n+1) ≫
        (totalDualDegreeIso K A (n+1)).inv := by
  rw [HomologicalComplex₂.total_d, Preadditive.comp_add, totalDualDegreeIso_inv_horizontal,
    totalDualDegreeIso_inv_vertical, ← Preadditive.add_comp, ← totalDualDifferential_eq_add]

def totalDualCochainIso :
    ChainComplex.linearYonedaObj (K.total (ComplexShape.down ℕ)) R A ≅
      (dualNatBicomplex K A).total (ComplexShape.up ℕ) :=
  HomologicalComplex.Hom.isoOfComponents (fun n => (totalDualDegreeIso K A n).symm) (by
    intro i j hij
    have hj : i+1=j := hij
    subst j
    exact totalDualDegreeIso_inv_comm K A i)

theorem totalDualCochainIso_hom_f (n : ℕ) :
    (totalDualCochainIso K A).hom.f n = (totalDualDegreeIso K A n).inv := rfl

theorem totalDualCochainIso_inv_f (n : ℕ) :
    (totalDualCochainIso K A).inv.f n = (totalDualDegreeIso K A n).hom := rfl

end Sharpness
