import Sharpness.Unconditional.RealizationSeparationCoproduct
import Sharpness.Unconditional.RealizationUnitSkeleton
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal
import Mathlib.Topology.Separation.Hausdorff

/-! The native relative skeletal filtration transports the closedness of
simplex-boundary inclusions to every realized simplicial monomorphism. The
single geometric boundary premise is explicit until its independent finite
face-cover construction is supplied. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
noncomputable section
universe u

namespace Sharpness.RealizationSeparation
open CategoryTheory CategoryTheory.Limits Topology Simplicial

theorem standardSimplex_t1Space (n : ℕ) : T1Space |(Δ[n] : SSet.{u})| := by
  exact (SimplexCategory.toTopHomeo ⦋n⦌).isEmbedding.t1Space

theorem emptyRealization_t1Space (X : SSet.{u}) : T1Space |(⊥ : X.Subcomplex).toSSet| := by
  let e := (SSet.Subcomplex.isInitialBot (X := X)).isInitialObj SSet.toTop _
  exact (TopCat.homeoOfIso (e.uniqueUpToIso TopCat.isInitialPEmpty)).isEmbedding.t1Space

variable (hboundary : ∀ n : ℕ,
  IsClosedEmbedding (SSet.toTop.map (∂Δ[n].ι : (∂Δ[n] : SSet.{u}) ⟶ Δ[n])))
include hboundary

theorem relativeBoundaryCoproduct_isClosedEmbedding {X Y : SSet.{u}} (i : X ⟶ Y) (n : ℕ) :
    IsClosedEmbedding (SSet.toTop.map (SSet.relativeCellComplexOfMono.l i n)) :=
  mapped_coproduct_isClosedEmbedding SSet.toTop _ (fun _ => hboundary n)

theorem relativeSkeletonStep_isClosedEmbedding {X Y : SSet.{u}} (i : X ⟶ Y) (n : ℕ) :
    IsClosedEmbedding (SSet.toTop.map (SSet.relativeCellComplexOfMono.r i n)) :=
  isClosedEmbedding_of_isPushout (RealizationUnitHomology.realizationRelativeSkeleton_isPushout i n)
    (relativeBoundaryCoproduct_isClosedEmbedding hboundary i n)

theorem realization_mono_isClosedEmbedding {X Y : SSet.{u}} (i : X ⟶ Y) [Mono i] :
    IsClosedEmbedding (SSet.toTop.map i) := by
  let c := SSet.relativeCellComplexOfMono i
  let d : Cocone (c.F ⋙ SSet.toTop) := SSet.toTop.mapCocone (Cocone.mk Y c.incl)
  have hd : IsColimit d := isColimitOfPreserves SSet.toTop c.isColimit
  have hs (n : ℕ) : IsClosedEmbedding ((c.F ⋙ SSet.toTop).map (homOfLE (Nat.le_succ n))) :=
    relativeSkeletonStep_isClosedEmbedding hboundary i n
  have hzero := sequential_inclusion_isClosedEmbedding (c.F ⋙ SSet.toTop) hs d hd 0
  rw [← c.fac, SSet.toTop.map_comp]
  exact hzero.comp (TopCat.homeoOfIso (SSet.toTop.mapIso c.isoBot)).symm.isClosedEmbedding

theorem realization_mono_t1Space {X Y : SSet.{u}} (i : X ⟶ Y) [Mono i]
    [T1Space |X|] : T1Space |Y| := by
  let c := SSet.relativeCellComplexOfMono i
  let d : Cocone (c.F ⋙ SSet.toTop) := SSet.toTop.mapCocone (Cocone.mk Y c.incl)
  have hd : IsColimit d := isColimitOfPreserves SSet.toTop c.isColimit
  have hs (n : ℕ) : IsClosedEmbedding ((c.F ⋙ SSet.toTop).map (homOfLE (Nat.le_succ n))) :=
    relativeSkeletonStep_isClosedEmbedding hboundary i n
  have ht (n : ℕ) : T1Space ((c.F ⋙ SSet.toTop).obj n) := by
    induction n with
    | zero => exact (TopCat.homeoOfIso (SSet.toTop.mapIso c.isoBot)).isEmbedding.t1Space
    | succ n ih =>
      letI : T1Space |(SSet.skeletonOfMono i n).toSSet| := ih
      letI : T1Space |SSet.relativeCellComplexOfMono.sigmaStdSimplex i n| :=
        mapped_coproduct_t1Space (fun _ : SSet.relativeCellComplexOfMono.Cell i n =>
          (Δ[n] : SSet.{u})) SSet.toTop (fun _ => standardSimplex_t1Space n)
      exact t1Space_of_isPushout (RealizationUnitHomology.realizationRelativeSkeleton_isPushout i n)
        (relativeBoundaryCoproduct_isClosedEmbedding hboundary i n)
  exact sequential_colimit_t1Space (c.F ⋙ SSet.toTop) hs d hd ht

theorem realization_t1Space_of_boundary (X : SSet.{u}) : T1Space |X| := by
  letI := emptyRealization_t1Space X
  exact realization_mono_t1Space hboundary (SSet.Subcomplex.ι (⊥ : X.Subcomplex))

theorem realization_subcomplex_isClosedEmbedding (X : SSet.{u}) (A : X.Subcomplex) :
    IsClosedEmbedding (SSet.toTop.map A.ι) :=
  realization_mono_isClosedEmbedding hboundary A.ι

theorem realization_skeleton_isClosedEmbedding (X : SSet.{u}) (n : ℕ) :
    IsClosedEmbedding (SSet.toTop.map (X.skeleton n).ι) :=
  realization_subcomplex_isClosedEmbedding hboundary X (X.skeleton n)

end Sharpness.RealizationSeparation
