import Sharpness.Unconditional.RealizationBoundaryAllFaces
import Sharpness.Unconditional.FiniteClosedCoverColimit
import Mathlib.AlgebraicTopology.SimplicialSet.Boundary

/-! The actual realization of the simplicial boundary is the closed coordinate
boundary. The comparison is glued from all faces, including empty intersections. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
noncomputable section
universe u
namespace Sharpness.RealizationBoundary
open CategoryTheory CategoryTheory.Limits Simplicial Opposite

def liftedBoundary (n : ℕ) : Set (SimplexCategory.toTop.{u}.obj ⦋n⦌) :=
  {t | ∃ i : Fin (n + 1), (t.down : Simplex n).val i = 0}

def boundaryFaceVertices {n : ℕ} (i : Fin (n + 1)) : Finset (Fin (n + 1)) := {i}ᶜ

theorem finiteCoordinateFace_mono {n : ℕ} {S T : Finset (Fin (n + 1))}
    (h : S ⊆ T) : finiteCoordinateFace.{u} S ⊆ finiteCoordinateFace T := by
  intro x hx j hj
  exact hx j (fun hs => hj (h hs))

theorem finiteCoordinateFace_inter {n : ℕ} (S T : Finset (Fin (n + 1))) :
    finiteCoordinateFace.{u} (S ∩ T) = finiteCoordinateFace S ∩ finiteCoordinateFace T := by
  classical
  ext t
  constructor
  · intro h
    exact ⟨fun j hj => h j (by simp [hj]), fun j hj => h j (by simp [hj])⟩
  · rintro ⟨hS, hT⟩ j hj
    by_cases hs : j ∈ S
    · exact hT j (fun ht => hj (Finset.mem_inter.mpr ⟨hs, ht⟩))
    · exact hS j hs

theorem face_mono {n : ℕ} {S T : Finset (Fin (n + 1))} (h : S ⊆ T) :
    SSet.stdSimplex.face.{u} S ≤ SSet.stdSimplex.face T := by
  intro m x hx
  exact fun j hj => h (hx hj)

theorem faceHomeo_natural {n : ℕ} {S T : Finset (Fin (n + 1))} (h : S ⊆ T) :
    SSet.toTop.map (SSet.Subcomplex.homOfLE (face_mono h)) ≫
        (TopCat.isoOfHomeo (faceHomeo T)).hom =
      (TopCat.isoOfHomeo (faceHomeo S)).hom ≫
        TopCat.ofHom (ContinuousMap.inclusion (finiteCoordinateFace_mono h)) := by
  ext x
  change (faceHomeo T (SSet.toTop.map _ x)).val = (faceHomeo S x).val
  rw [faceHomeo_inclusion, faceHomeo_inclusion]
  congr 1
  change (SSet.toTop.map _ ≫ SSet.toTop.map _) x = (SSet.toTop.map _) x
  rw [← SSet.toTop.map_comp, SSet.Subcomplex.homOfLE_ι]

def boundaryFaceCover (n : ℕ) : SSet.Subcomplex.MulticoequalizerDiagram
    (SSet.boundary.{u} n)
    (fun i : Fin (n + 1) => SSet.stdSimplex.face (boundaryFaceVertices i))
    (fun i j => SSet.stdSimplex.face (boundaryFaceVertices i ∩ boundaryFaceVertices j)) where
  iSup_eq := (SSet.boundary_eq_iSup n).symm
  eq_inf _ _ := (SSet.stdSimplex.face_inter_face _ _).symm

def boundaryCoordinateCover (n : ℕ) : CompleteLattice.MulticoequalizerDiagram
    (liftedBoundary.{u} n)
    (fun i : Fin (n + 1) => finiteCoordinateFace (boundaryFaceVertices i))
    (fun i j => finiteCoordinateFace (boundaryFaceVertices i ∩ boundaryFaceVertices j)) where
  iSup_eq := by
    ext t
    simp only [Set.iSup_eq_iUnion, Set.mem_iUnion, liftedBoundary, Set.mem_setOf_eq]
    simp [finiteCoordinateFace, boundaryFaceVertices]
  eq_inf i j := finiteCoordinateFace_inter _ _

def boundaryRealizedMulticofork (n : ℕ) :=
  ((boundaryFaceCover.{u} n).multicofork.map SSet.Subcomplex.toSSetFunctor).map SSet.toTop

def boundaryRealizedIsColimit (n : ℕ) : IsColimit (boundaryRealizedMulticofork.{u} n) :=
  Multicofork.isColimitMapOfPreserves _ _ (boundaryFaceCover n).isColimit

def boundaryCoordinateMulticofork (n : ℕ) :=
  (boundaryCoordinateCover.{u} n).multicofork.map FiniteClosedCover.subsetFunctor

def boundaryCoordinateIsColimit (n : ℕ) : IsColimit (boundaryCoordinateMulticofork.{u} n) :=
  FiniteClosedCover.isColimit_of_isClosed _ (fun _ => isClosed_finiteCoordinateFace _)

def boundaryFaceDiagramIso (n : ℕ) :
    (((boundaryFaceCover.{u} n).multispanIndex.map SSet.Subcomplex.toSSetFunctor).map
      SSet.toTop).multispan ≅
    ((boundaryCoordinateCover.{u} n).multispanIndex.map
      FiniteClosedCover.subsetFunctor).multispan :=
  NatIso.ofComponents
    (fun i => match i with
      | .left ij => TopCat.isoOfHomeo (faceHomeo (boundaryFaceVertices ij.1 ∩
          boundaryFaceVertices ij.2))
      | .right i => TopCat.isoOfHomeo (faceHomeo (boundaryFaceVertices i)))
    (by
      rintro (_ | _) (_ | _) (_ | _ | _) <;> dsimp
      · simp
      · exact faceHomeo_natural Finset.inter_subset_left
      · exact faceHomeo_natural Finset.inter_subset_right
      · simp)

def boundaryRealizationIso (n : ℕ) :
    SSet.toTop.obj (SSet.boundary.{u} n).toSSet ≅ TopCat.of (liftedBoundary.{u} n) :=
  (boundaryRealizedIsColimit n).coconePointsIsoOfNatIso
    (boundaryCoordinateIsColimit n) (boundaryFaceDiagramIso n)

def boundaryRealizationHomeo (n : ℕ) :
    |(SSet.boundary.{u} n).toSSet| ≃ₜ liftedBoundary.{u} n :=
  TopCat.homeoOfIso (boundaryRealizationIso n)

theorem boundaryRealizationIso_fac (n : ℕ) (i : Fin (n + 1)) :
    (boundaryRealizedMulticofork.{u} n).π i ≫ (boundaryRealizationIso n).hom =
      (TopCat.isoOfHomeo (faceHomeo (boundaryFaceVertices i))).hom ≫
        (boundaryCoordinateMulticofork n).π i :=
  IsColimit.comp_coconePointsIsoOfNatIso_hom (boundaryRealizedIsColimit n)
    (boundaryCoordinateIsColimit n) (boundaryFaceDiagramIso n) (WalkingMultispan.right i)

def liftedBoundaryInclusion (n : ℕ) :
    TopCat.of (liftedBoundary.{u} n) ⟶ SimplexCategory.toTop.obj ⦋n⦌ :=
  TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

theorem boundaryRealizationIso_hom_inclusion (n : ℕ) :
    (boundaryRealizationIso.{u} n).hom ≫ liftedBoundaryInclusion n =
      SSet.toTop.map (SSet.boundary n).ι ≫ (SSet.toTopSimplex.app ⦋n⦌).hom := by
  apply Multicofork.IsColimit.hom_ext (boundaryRealizedIsColimit n)
  intro i
  rw [← Category.assoc, boundaryRealizationIso_fac, Category.assoc]
  change _ = SSet.toTop.map (SSet.Subcomplex.homOfLE
    (SSet.face_singleton_compl_le_boundary i)) ≫
    SSet.toTop.map (SSet.boundary n).ι ≫ (SSet.toTopSimplex.app ⦋n⦌).hom
  conv_rhs => rw [← Category.assoc, ← SSet.toTop.map_comp, SSet.Subcomplex.homOfLE_ι]
  ext x
  exact faceHomeo_inclusion _ x

theorem boundaryRealizationHomeo_inclusion (n : ℕ)
    (x : |(SSet.boundary.{u} n).toSSet|) :
    (boundaryRealizationHomeo n x).val =
      (SSet.toTopSimplex.app ⦋n⦌).hom (SSet.toTop.map (SSet.boundary n).ι x) :=
  congrArg (fun f => f x) (boundaryRealizationIso_hom_inclusion n)

theorem isClosed_liftedBoundary (n : ℕ) : IsClosed (liftedBoundary.{u} n) :=
  (isClosed_boundary n).preimage continuous_uliftDown

theorem boundaryRealizationInclusion_isClosedEmbedding (n : ℕ) :
    Topology.IsClosedEmbedding (SSet.toTop.map (SSet.boundary.{u} n).ι) := by
  have h := (isClosed_liftedBoundary.{u} n).isClosedEmbedding_subtypeVal.comp
    (boundaryRealizationHomeo.{u} n).isClosedEmbedding
  have he : (fun x => (boundaryRealizationHomeo.{u} n x).val) =
      (fun x => (SSet.toTopSimplex.app ⦋n⦌).hom
        (SSet.toTop.map (SSet.boundary n).ι x)) := by
    funext x
    exact boundaryRealizationHomeo_inclusion n x
  change Topology.IsClosedEmbedding (fun x => (boundaryRealizationHomeo n x).val) at h
  rw [he] at h
  exact Topology.IsClosedEmbedding.of_comp
    (TopCat.homeoOfIso (SSet.toTopSimplex.app ⦋n⦌)).isEmbedding h

def liftedBoundaryHomeo (n : ℕ) : liftedBoundary.{u} n ≃ₜ boundary n where
  toFun x := ⟨x.val.down, x.property⟩
  invFun x := ⟨ULift.up x.val, x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_uliftDown.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_uliftUp.comp continuous_subtype_val).subtype_mk _

/-- Literal coordinate-boundary form of the actual realization comparison. -/
def boundaryCoordinateHomeo (n : ℕ) :
    |(SSet.boundary.{u} n).toSSet| ≃ₜ boundary n :=
  (boundaryRealizationHomeo n).trans (liftedBoundaryHomeo n)

theorem boundaryCoordinateHomeo_inclusion (n : ℕ)
    (x : |(SSet.boundary.{u} n).toSSet|) :
    (boundaryCoordinateHomeo n x).val =
      ((SSet.toTopSimplex.app ⦋n⦌).hom (SSet.toTop.map (SSet.boundary n).ι x)).down :=
  congrArg ULift.down (boundaryRealizationHomeo_inclusion n x)

end Sharpness.RealizationBoundary
