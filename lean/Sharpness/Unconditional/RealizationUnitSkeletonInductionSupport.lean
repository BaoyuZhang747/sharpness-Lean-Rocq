import Sharpness.Unconditional.SingularAttachmentComparisonUnitCoproducts
import Sharpness.Unconditional.RealizationUnitSkeleton
import Mathlib.AlgebraicTopology.SimplicialSet.Dimension

/-! Base and dimension facts for induction over the actual native skeletal
filtration. Skeleton n contains generators of dimension strictly below n. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
noncomputable section
universe u
namespace Sharpness.RealizationUnitHomology
open CategoryTheory CategoryTheory.Limits Simplicial Opposite

variable (R : Type u) [CommRing R]

theorem realizationUnitChainMap_quasiIso_of_iso {X Y : SSet.{u}} (e : X ≅ Y)
    [QuasiIso (realizationUnitChainMap R X)] :
    QuasiIso (realizationUnitChainMap R Y) := by
  haveI : QuasiIso ((simplicialChainsFunctor R).map e.hom ≫
      realizationUnitChainMap R Y) := by
    rw [realizationUnitChainMap_naturality]
    infer_instance
  exact quasiIso_of_comp_left ((simplicialChainsFunctor R).map e.hom)
    (realizationUnitChainMap R Y)

theorem realizationUnitChainMap_quasiIso_of_isInitial (X : SSet.{u}) (hX : IsInitial X) :
    QuasiIso (realizationUnitChainMap R X) := by
  let family : PEmpty.{u+1} → SSet.{u} := fun _ => (Δ[0] : SSet.{u})
  letI : QuasiIso (realizationUnitChainMap R (∐ family)) :=
    SingularAttachmentComparison.realizationUnitChainMap_coproduct_quasiIso R family
      (fun i => PEmpty.elim i)
  let hE : IsInitial (∐ family) :=
    (isColimitEquivIsInitialOfIsEmpty _ _) (colimit.isColimit (Discrete.functor family))
  exact realizationUnitChainMap_quasiIso_of_iso R (hE.uniqueUpToIso hX)

theorem skeletonZero_unit_quasiIso (X : SSet.{u}) :
    QuasiIso (realizationUnitChainMap R (X.skeleton 0).toSSet) := by
  rw [X.skeleton_zero]
  exact realizationUnitChainMap_quasiIso_of_isInitial R _ (SSet.Subcomplex.isInitialBot (X := X))

theorem skeleton_hasDimensionLT (X : SSet.{u}) (n : ℕ) :
    SSet.HasDimensionLT (X.skeleton n).toSSet n where
  degenerate_eq_top d hd := by
    ext x
    simp only [Set.top_eq_univ, Set.mem_univ, iff_true]
    rw [SSet.Subcomplex.mem_degenerate_iff]
    by_contra hx
    have hnd : x.val ∈ X.nonDegenerate d := hx
    have hlt := (X.mem_skeleton_obj_iff_of_nonDegenerate ⟨x.val, hnd⟩ n).mp x.property
    omega

theorem skeleton_eq_top_of_hasDimensionLT (X : SSet.{u}) (n : ℕ)
    [SSet.HasDimensionLT X n] : X.skeleton n = ⊤ := by
  apply (SSet.Subcomplex.eq_top_iff_of_hasDimensionLT _ n).mpr
  intro d hd x hx
  exact X.mem_skeleton x hd

def skeletonIsoOfHasDimensionLT (X : SSet.{u}) (n : ℕ)
    [SSet.HasDimensionLT X n] : (X.skeleton n).toSSet ≅ X :=
  SSet.Subcomplex.eqToIso (skeleton_eq_top_of_hasDimensionLT X n) ≪≫
    SSet.Subcomplex.topIso X

def boundarySkeletonIso (n : ℕ) :
    (((SSet.boundary.{u} n).toSSet).skeleton n).toSSet ≅ (SSet.boundary n).toSSet :=
  skeletonIsoOfHasDimensionLT _ n

theorem skeletonOfEmptyInclusion (X : SSet.{u}) (n : ℕ) :
    SSet.skeletonOfMono (⊥ : X.Subcomplex).ι n = X.skeleton n := by
  change SSet.Subcomplex.range (⊥ : X.Subcomplex).ι ⊔ X.skeleton n = X.skeleton n
  have h : SSet.Subcomplex.range (⊥ : X.Subcomplex).ι = ⊥ := by
    ext k x
    simp [SSet.Subcomplex.range]
  rw [h, bot_sup_eq]

def relativeEmptySkeletonIso (X : SSet.{u}) (n : ℕ) :
    (SSet.skeletonOfMono (⊥ : X.Subcomplex).ι n).toSSet ≅ (X.skeleton n).toSSet :=
  SSet.Subcomplex.eqToIso (skeletonOfEmptyInclusion X n)

end Sharpness.RealizationUnitHomology
