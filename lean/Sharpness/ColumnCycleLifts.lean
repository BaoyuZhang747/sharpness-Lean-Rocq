import Sharpness.CochainSubmoduleSections
import Sharpness.ColumnFiltrationFunctor

/-! Actual vertical cycles have lifts to the filtered total complex.
Their total differential is the horizontal differential, with the
vertical signed term vanishing on cycles. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness
open CategoryTheory CategoryTheory.Limits
variable {R : Type u} [CommRing R]
    (K : HomologicalComplex₂ (ModuleCat.{u} R) (ComplexShape.up ℕ) (ComplexShape.up ℕ))

def totalColumnSummandLift (p q : ℕ) :
    (K.X p).X q ⟶ (totalColumnFilteredComplex K p).X (p+q) :=
  (totalColumnSubmodules K p).degreeLift (p+q)
    (K.ιTotal (ComplexShape.up ℕ) p q (p+q) rfl)
    (totalColumnFiltration_summand_mem K p p q (p+q) rfl (le_refl p))

@[reassoc]
theorem totalColumnSummandLift_inclusion (p q : ℕ) :
    totalColumnSummandLift K p q ≫ (totalColumnFilteredInclusion K p).f (p+q) =
      K.ιTotal (ComplexShape.up ℕ) p q (p+q) rfl :=
  CochainSubmodules.degreeLift_inclusion _ _ _ _

set_option backward.isDefEq.respectTransparency false in
theorem totalColumnCycle_d (p q : ℕ) :
    (K.X p).iCycles q ≫ K.ιTotal (ComplexShape.up ℕ) p q (p+q) rfl ≫
        (K.total (ComplexShape.up ℕ)).d (p+q) (p+q+1) =
      (K.X p).iCycles q ≫ (K.d p (p+1)).f q ≫
        K.ιTotal (ComplexShape.up ℕ) (p+1) q (p+q+1)
          (by change p+1+q=p+q+1; omega) := by
  rw [cochainNatBicomplexTotal_d, Preadditive.comp_add]
  simp only [Linear.comp_units_smul, HomologicalComplex.iCycles_d_assoc,
    zero_comp, smul_zero, add_zero]

end Sharpness
