import Sharpness.CoproductChains
import Sharpness.ModuleDirectSumDual
import Sharpness.ProductCochainLifts

/-! The dual of the actual infinite direct-sum chain complex is the
actual product cochain complex. The cochain comparison uses actual
summand inclusions, so compatibility with all differentials is proved
by their cochain-map structure, not added as an assumption. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness
open CategoryTheory
variable {R : Type u} [CommRing R] {ι : Type u}
    (K : ι → ChainComplex (ModuleCat.{u} R) ℕ) (A : ModuleCat.{u} R)

def coproductChainsDualComparison :
    (coproductChains K).linearYonedaObj R A ⟶ productCochains (fun i => (K i).linearYonedaObj R A) :=
  productCochainsLift _ (fun i => SingularCohomology.chainDualMap R (coproductChainsInclusion K i) A)

set_option backward.isDefEq.respectTransparency false in
theorem coproductChainsDualComparison_component_isIso (n : ℕ) :
    IsIso ((coproductChainsDualComparison K A).f n) := by
  let e := (moduleDirectSumHomEquiv (fun i => (K i).X n) A).toModuleIso
  have he : e.hom = (coproductChainsDualComparison K A).f n := rfl
  rw [← he]
  infer_instance

theorem coproductChainsDualComparison_isIso : IsIso (coproductChainsDualComparison K A) := by
  letI : ∀ n, IsIso ((coproductChainsDualComparison K A).f n) :=
    coproductChainsDualComparison_component_isIso K A
  exact HomologicalComplex.Hom.isIso_of_components _

def coproductChainsDualIso :
    (coproductChains K).linearYonedaObj R A ≅ productCochains (fun i => (K i).linearYonedaObj R A) := by
  letI := coproductChainsDualComparison_isIso K A
  exact asIso (coproductChainsDualComparison K A)

theorem coproductChainsDualIso_projection (i : ι) :
    (coproductChainsDualIso K A).hom ≫ productCochainsProjection _ i =
      SingularCohomology.chainDualMap R (coproductChainsInclusion K i) A :=
  productCochainsLift_projection _ _ _

end Sharpness
