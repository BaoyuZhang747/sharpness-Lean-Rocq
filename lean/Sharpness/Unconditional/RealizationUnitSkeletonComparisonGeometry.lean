import Sharpness.Unconditional.RealizationUnitSkeletonComparison
import Sharpness.Unconditional.RealizationSeparation

/-! The algebraic skeletal passage with the actual realization separation
and skeletal embedding theorems supplied. Only the finite-stage unit remains. -/
set_option autoImplicit false
noncomputable section
universe u

namespace Sharpness.RealizationUnitHomology
open CategoryTheory Simplicial

variable (R : Type u) [CommRing R] (X : SSet.{u})

/-- Realization-unit comparison reduces to its finite-dimensional skeleta;
the geometric separation and embedding facts are proved, not hypotheses. -/
theorem realizationUnitChainMap_quasiIso_of_finite_skeleta
    (hstage : ∀ n, QuasiIso (realizationUnitChainMap R (X.skeleton n).toSSet)) :
    QuasiIso (realizationUnitChainMap R X) :=
  realizationUnitChainMap_quasiIso_of_skeleta R X
    (fun n => (RealizationSeparation.skeleton_realization_isClosedEmbedding X n).isEmbedding)
    hstage

end Sharpness.RealizationUnitHomology
