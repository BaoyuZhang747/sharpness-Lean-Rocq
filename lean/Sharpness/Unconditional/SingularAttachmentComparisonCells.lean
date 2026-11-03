import Sharpness.Unconditional.SingularAttachmentComparisonCellRealization
import Sharpness.Unconditional.SingularAttachmentComparisonTopological
import Sharpness.Unconditional.SingularAttachmentComparisonUnitPushout

/-! The actual relative singular comparison for arbitrary families of
simplex attachments. No collar, homotopy, or comparison premise remains. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
noncomputable section
universe u

namespace Sharpness.SingularAttachmentComparison
open CategoryTheory CategoryTheory.Limits Simplicial

variable (R : Type u) [CommRing R] {ι : Type u} (n : ι → ℕ)
  {X Y : SSet.{u}} {p : (∐ cellBoundaryFamily n) ⟶ X}
  {q : (∐ cellSimplexFamily n) ⟶ Y} {j : X ⟶ Y}

theorem realizedCellAttachment_relative_quasiIso
    (h : IsPushout (Limits.Sigma.map (fun i => (SSet.boundary.{u} (n i)).ι)) p q j) :
    QuasiIso (realizedPushoutRelativeMap R h) :=
  collaredPushout_relative_quasiIso R (h.map SSet.toTop)
    (realizedCellBoundary_isClosedEmbedding n)
    (realizedCellCollarBoundary n) (realizedCellCollarEmbedding n)
    (realizedCellCollarBoundary_embedding n)
    (realizedCellCollarEmbedding_isOpenEmbedding n)
    (realizedCellCollarRetraction n) (realizedCellCollarBoundary_retraction n)
    (realizedCellCollarHomotopy n) (realizedCellCollarHomotopy_fixed n)

theorem realizedRelativeSkeleton_relative_quasiIso {A X : SSet.{u}}
    (i : A ⟶ X) [Mono i] (n : ℕ) :
    QuasiIso (realizedPushoutRelativeMap R
      (SSet.relativeCellComplexOfMono.isPushout i n).flip) :=
  realizedCellAttachment_relative_quasiIso R
    (fun _ : SSet.relativeCellComplexOfMono.Cell i n => n)
    (SSet.relativeCellComplexOfMono.isPushout i n).flip

end Sharpness.SingularAttachmentComparison
