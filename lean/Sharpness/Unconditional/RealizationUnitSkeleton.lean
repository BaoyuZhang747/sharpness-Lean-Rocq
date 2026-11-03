import Mathlib.AlgebraicTopology.SimplicialSet.Skeleton
import Mathlib.AlgebraicTopology.SimplicialSet.TopAdj
import Mathlib.AlgebraicTopology.SimplicialSet.Homology.Basic
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import Mathlib.CategoryTheory.Adjunction.Limits

/-! Actual skeletal colimits and realization attachment squares.  These
statements transport colimits through geometric realization only; they do not
assert that singular chains preserve arbitrary colimits. The native skeleton
`X.skeleton n` contains simplices generated in dimensions strictly below `n`. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
noncomputable section
universe u

namespace Sharpness.RealizationUnitHomology
open CategoryTheory CategoryTheory.Limits Simplicial Opposite

def skeletonDiagram (X : SSet.{u}) : ℕ ⥤ SSet.{u} :=
  X.skeleton.monotone.functor ⋙ SSet.Subcomplex.toSSetFunctor

def skeletonCocone (X : SSet.{u}) : Cocone (skeletonDiagram X) where
  pt := X
  ι.app n := (X.skeleton n).ι

/-- The actual increasing skeletal diagram exhausts every simplicial set. -/
def skeletonIsColimit (X : SSet.{u}) : IsColimit (skeletonCocone X) :=
  IsColimit.ofIsoColimit
    (isColimitOfPreserves SSet.Subcomplex.toSSetFunctor
      ((CompleteLattice.colimitCocone X.skeleton.monotone.functor).isColimit))
    (Cocone.ext (SSet.Subcomplex.eqToIso X.iSup_skeleton ≪≫ SSet.Subcomplex.topIso X))

def realizationSkeletonDiagram (X : SSet.{u}) : ℕ ⥤ TopCat.{u} :=
  skeletonDiagram X ⋙ SSet.toTop

def realizationSkeletonCocone (X : SSet.{u}) : Cocone (realizationSkeletonDiagram X) :=
  SSet.toTop.mapCocone (skeletonCocone X)

/-- Realization of the actual skeletal diagram has colimit the realization
of `X`, by the proved realization/singular-set adjunction. -/
def realizationSkeletonIsColimit (X : SSet.{u}) :
    IsColimit (realizationSkeletonCocone X) :=
  isColimitOfPreserves SSet.toTop (skeletonIsColimit X)

section RelativeAttachment
variable {X Y : SSet.{u}} (i : X ⟶ Y) (n : ℕ)
open SSet.relativeCellComplexOfMono

/-- The native nondegenerate-simplex attachment is an actual topological
pushout after geometric realization. -/
theorem realizationRelativeSkeleton_isPushout :
    IsPushout (SSet.toTop.map (t i n)) (SSet.toTop.map (l i n))
      (SSet.toTop.map (r i n)) (SSet.toTop.map (b i n)) :=
  (isPushout i n).map SSet.toTop

def realizationRelativeSkeletonCellsIso :
    |sigmaStdSimplex i n| ≅ ∐ (fun _ : Cell i n => |(Δ[n] : SSet.{u})|) :=
  PreservesCoproduct.iso SSet.toTop (fun _ : Cell i n => (Δ[n] : SSet.{u}))

def realizationRelativeSkeletonBoundariesIso :
    |sigmaBoundary i n| ≅ ∐ (fun _ : Cell i n => |(∂Δ[n] : SSet.{u})|) :=
  PreservesCoproduct.iso SSet.toTop (fun _ : Cell i n => (∂Δ[n] : SSet.{u}))

end RelativeAttachment

/-- The skeleton inclusion is bijective on every simplex degree below its
cutoff; this is stronger than eventual finite support on the simplicial side. -/
theorem skeletonInclusion_app_isIso (X : SSet.{u}) (d n : ℕ) (h : d < n) :
    IsIso ((X.skeleton n).ι.app (op ⦋d⦌)) := by
  apply (CategoryTheory.isIso_iff_bijective _).mpr
  exact ⟨Subtype.val_injective, fun x => ⟨⟨x, X.mem_skeleton x h⟩, rfl⟩⟩

/-- Actual simplicial chains stabilize degreewise on the skeletal filtration. -/
theorem skeletonChainInclusion_degree_isIso (R : Type u) [CommRing R]
    (X : SSet.{u}) (d n : ℕ) (h : d < n) :
    IsIso ((SSet.chainComplexMap (X.skeleton n).ι (ModuleCat.of R R)).f d) := by
  letI := skeletonInclusion_app_isIso X d n h
  change IsIso ((sigmaConst.obj (ModuleCat.of R R)).map ((X.skeleton n).ι.app (op ⦋d⦌)))
  infer_instance

end Sharpness.RealizationUnitHomology
