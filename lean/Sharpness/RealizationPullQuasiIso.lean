import Sharpness.RealizationUnitCochainNaturality

/-! An actual simplicial free-chain quasi-isomorphism induces an
actual realized singular-cochain quasi-isomorphism for every constant
module. The proof uses the actual unit square and projective duality. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness
open CategoryTheory
variable (R : Type u) [CommRing R] {X Y : SSet.{u}}
    (f : X ⟶ Y) (A : ModuleCat.{u} R) (real : RealizationUnitInput.{u} R)

include real in
theorem realizationCochainPull_quasiIso [QuasiIso ((simplicialChainsFunctor R).map f)] :
    QuasiIso (SingularCohomology.cochainPull R (SSet.toTop.map f) A) := by
  letI (n : ℕ) : Projective ((X.chainComplex (ModuleCat.of R R)).X n) :=
    SingularCohomology.simplicialChains_projective R X n
  letI (n : ℕ) : Projective ((Y.chainComplex (ModuleCat.of R R)).X n) :=
    SingularCohomology.simplicialChains_projective R Y n
  letI := SingularCohomology.chainDualMap_quasiIso_of_projective R A
    ((simplicialChainsFunctor R).map f)
  letI := realizationUnitCochainMap_quasiIso R X A real
  letI := realizationUnitCochainMap_quasiIso R Y A real
  have h : QuasiIso (SingularCohomology.cochainPull R (SSet.toTop.map f) A ≫
      realizationUnitCochainMap R X A) := by
    rw [realizationUnitCochainMap_naturality]
    infer_instance
  exact (quasiIso_iff_comp_right (SingularCohomology.cochainPull R (SSet.toTop.map f) A)
    (realizationUnitCochainMap R X A)).mp h

end Sharpness
