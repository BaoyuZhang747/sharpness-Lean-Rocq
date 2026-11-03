import Sharpness.Unconditional.SingularAttachmentComparisonCells
import Sharpness.Unconditional.RealizationUnitSkeletonInduction
import Sharpness.RealizationUnitInput

/-! The uniform realization-unit theorem, constructed from actual singular
subdivision, excision, simplex collars and exhaustive skeletal induction. -/
set_option autoImplicit false
noncomputable section
universe u

namespace Sharpness
open CategoryTheory

variable (R : Type u) [CommRing R]

/-- The actual simplicial-to-singular unit induces a quasi-isomorphism for
every simplicial set and every commutative coefficient ring. -/
theorem realizationUnitChainMap_quasiIso_unconditional (X : SSet.{u}) :
    QuasiIso (realizationUnitChainMap R X) :=
  RealizationUnitHomology.realizationUnitChainMap_quasiIso_of_cell_attachments R
    (fun X n => SingularAttachmentComparison.realizedRelativeSkeleton_relative_quasiIso
      R (⊥ : X.Subcomplex).ι n) X

/-- The former published-input boundary is now inhabited by an unconditional
proof of the actual realization adjunction unit. -/
def canonicalRealizationUnitInput : RealizationUnitInput R where
  May_16_2_Weibel_3_6_1 X := realizationUnitChainMap_quasiIso_unconditional R X

end Sharpness

