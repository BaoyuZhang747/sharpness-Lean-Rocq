import Sharpness.Unconditional.RealizationUnitSkeletonInductionSupport
import Sharpness.Unconditional.SingularAttachmentComparisonUnitPushout
import Sharpness.Unconditional.RealizationUnitSkeletonComparisonGeometry

/-! Induction over actual skeletal attachments. The single remaining input
here is the literal relative singular-chain map for each cell attachment;
the geometric collar/excision construction supplies that input separately. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
noncomputable section
universe u
namespace Sharpness.RealizationUnitHomology
open CategoryTheory CategoryTheory.Limits Simplicial Opposite
open SSet.relativeCellComplexOfMono
open Sharpness.SingularAttachmentComparison
variable (R : Type u) [CommRing R]

theorem realizationUnitChainMap_quasiIso_of_cell_attachments
    (hrel : ∀ (X : SSet.{u}) (n : ℕ), QuasiIso (realizedPushoutRelativeMap R
      (SSet.relativeCellComplexOfMono.isPushout (⊥ : X.Subcomplex).ι n).flip))
    (X : SSet.{u}) : QuasiIso (realizationUnitChainMap R X) := by
  have hs (n : ℕ) (Y : SSet.{u}) : QuasiIso (realizationUnitChainMap R (Y.skeleton n).toSSet) := by
    induction n generalizing Y with
    | zero => exact skeletonZero_unit_quasiIso R Y
    | succ n ih =>
      let i := (⊥ : Y.Subcomplex).ι
      letI : QuasiIso (realizationUnitChainMap R
          (((SSet.boundary.{u} n).toSSet).skeleton n).toSSet) := ih _
      letI : QuasiIso (realizationUnitChainMap R (SSet.boundary.{u} n).toSSet) :=
        realizationUnitChainMap_quasiIso_of_iso R (boundarySkeletonIso n)
      letI : QuasiIso (realizationUnitChainMap R (sigmaBoundary i n)) :=
        realizationUnitChainMap_coproduct_quasiIso R _ (fun _ => inferInstance)
      letI : QuasiIso (realizationUnitChainMap R (sigmaStdSimplex i n)) :=
        standardSimplexCoproduct_unit_quasiIso R (fun _ : Cell i n => n)
      letI : QuasiIso (realizationUnitChainMap R (Y.skeleton n).toSSet) := ih Y
      letI : QuasiIso (realizationUnitChainMap R (SSet.skeletonOfMono i n).toSSet) :=
        realizationUnitChainMap_quasiIso_of_iso R (relativeEmptySkeletonIso Y n).symm
      letI : Mono (SSet.toTop.map (l i n)) :=
        (TopCat.mono_iff_injective _).mpr
          (RealizationSeparation.realization_map_isClosedEmbedding (l i n)).injective
      letI : Mono (SSet.toTop.map (r i n)) :=
        (TopCat.mono_iff_injective _).mpr
          (RealizationSeparation.realization_map_isClosedEmbedding (r i n)).injective
      letI : QuasiIso (realizationUnitChainMap R (SSet.skeletonOfMono i (n + 1)).toSSet) :=
        realizationUnitChainMap_pushout_quasiIso R
          (SSet.relativeCellComplexOfMono.isPushout i n).flip (hrel Y n)
      exact realizationUnitChainMap_quasiIso_of_iso R (relativeEmptySkeletonIso Y (n + 1))
  exact realizationUnitChainMap_quasiIso_of_finite_skeleta R X (fun n => hs n X)

end Sharpness.RealizationUnitHomology
