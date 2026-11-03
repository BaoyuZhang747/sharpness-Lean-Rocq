import Sharpness.ChainDualAdditive
import Sharpness.CochainNatTotalSigns
import Mathlib.Algebra.Homology.TotalComplex

/-! The actual Hom_R(-,A) dual of a first-quadrant chain bicomplex.
The horizontal direction reverses; vertical duality is the native
linear Yoneda cochain complex. Square-zero is proved from the original
bicomplex, including the zero boundary terms. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness
open CategoryTheory
variable {R : Type u} [CommRing R]
    (K : HomologicalComplex₂ (ModuleCat.{u} R) (ComplexShape.down ℕ) (ComplexShape.down ℕ))
    (A : ModuleCat.{u} R)

def dualNatBicomplex :
    HomologicalComplex₂ (ModuleCat.{u} R) (ComplexShape.up ℕ) (ComplexShape.up ℕ) :=
  CochainComplex.of (fun p => ChainComplex.linearYonedaObj (K.X p) R A)
    (fun p => SingularCohomology.chainDualMap R (K.d (p+1) p) A) (by
      intro p
      rw [← SingularCohomology.chainDualMap_comp, K.d_comp_d,
        SingularCohomology.chainDualMap_zero])

theorem dualNatBicomplex_horizontal (p : ℕ) :
    (dualNatBicomplex K A).d p (p+1) = SingularCohomology.chainDualMap R (K.d (p+1) p) A := by
  dsimp only [dualNatBicomplex]
  rw [CochainComplex.of_d]

end Sharpness
