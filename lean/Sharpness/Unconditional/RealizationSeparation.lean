import Sharpness.Unconditional.RealizationSeparationRelative
import Sharpness.Unconditional.RealizationBoundaryGluing

/-! Unconditional separation and closed embeddings for geometric realization.
The actual finite-face boundary construction discharges the only geometric
premise of the relative skeletal assembly. -/
set_option autoImplicit false
noncomputable section
universe u

namespace Sharpness.RealizationSeparation
open CategoryTheory Topology Simplicial

theorem realization_map_isClosedEmbedding {X Y : SSet.{u}} (i : X ⟶ Y) [Mono i] :
    IsClosedEmbedding (SSet.toTop.map i) :=
  realization_mono_isClosedEmbedding
    RealizationBoundary.boundaryRealizationInclusion_isClosedEmbedding i

instance realizationT1Space (X : SSet.{u}) : T1Space |X| :=
  realization_t1Space_of_boundary
    RealizationBoundary.boundaryRealizationInclusion_isClosedEmbedding X

theorem subcomplex_realization_isClosedEmbedding (X : SSet.{u}) (A : X.Subcomplex) :
    IsClosedEmbedding (SSet.toTop.map A.ι) :=
  realization_map_isClosedEmbedding A.ι

theorem skeleton_realization_isClosedEmbedding (X : SSet.{u}) (n : ℕ) :
    IsClosedEmbedding (SSet.toTop.map (X.skeleton n).ι) :=
  realization_map_isClosedEmbedding (X.skeleton n).ι

end Sharpness.RealizationSeparation
