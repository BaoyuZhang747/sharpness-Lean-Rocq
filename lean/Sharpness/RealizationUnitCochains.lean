import Sharpness.RealizationUnitInput
import Sharpness.ChainDualProjectiveQuasiIso
import Sharpness.SingularChainsProjective

/-! Arbitrary-module cochain invariance of the actual realization
unit. Only the uniform ring-valued chain comparison is referenced;
the Hom_R(-,A) conclusion follows from proved degreewise projectivity
and chain homotopy equivalence. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness
open CategoryTheory
variable (R : Type u) [CommRing R] (X : SSet.{u}) (A : ModuleCat.{u} R)

def realizationUnitChainMap : X.chainComplex (ModuleCat.of R R) ⟶
    (SingularCohomology.chainsFunctor R).obj (SSet.toTop.obj X) :=
  (simplicialChainsFunctor R).map (realizationSingularUnit X)

def realizationUnitCochainMap : SingularCohomology.cochains R (SSet.toTop.obj X) A ⟶
    ChainComplex.linearYonedaObj (X.chainComplex (ModuleCat.of R R)) R A :=
  SingularCohomology.chainDualMap R (realizationUnitChainMap R X) A

theorem realizationUnitChainMap_quasiIso (real : RealizationUnitInput.{u} R) :
    QuasiIso (realizationUnitChainMap R X) := real.May_16_2_Weibel_3_6_1 X

theorem realizationUnitCochainMap_quasiIso (real : RealizationUnitInput.{u} R) :
    QuasiIso (realizationUnitCochainMap R X A) := by
  letI (n : ℕ) : Projective ((X.chainComplex (ModuleCat.of R R)).X n) :=
    SingularCohomology.simplicialChains_projective R X n
  letI (n : ℕ) : Projective (((SingularCohomology.chainsFunctor R).obj (SSet.toTop.obj X)).X n) :=
    SingularCohomology.chainsFunctor_projective R (SSet.toTop.obj X) n
  letI := realizationUnitChainMap_quasiIso R X real
  exact SingularCohomology.chainDualMap_quasiIso_of_projective R A (realizationUnitChainMap R X)

end Sharpness
