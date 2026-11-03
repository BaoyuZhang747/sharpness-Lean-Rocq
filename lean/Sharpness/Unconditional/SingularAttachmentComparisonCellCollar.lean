import Sharpness.Unconditional.RealizationBoundaryGluing
import Sharpness.Unconditional.RealizationBoundaryRadialHomotopy
import Mathlib.Topology.Homotopy.TopCat.Basic

/-! An actual boundary-fixed open collar of each realized standard simplex.
The boundary domain and inclusion are the native simplicial realization. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace Sharpness.SingularAttachmentComparison
open CategoryTheory CategoryTheory.Limits Simplicial
open Sharpness.RealizationBoundary

def simplexCoordinateHomeo (n : ℕ) : |(Δ[n] : SSet.{u})| ≃ₜ Simplex n :=
  (TopCat.homeoOfIso (SSet.toTopSimplex.app ⦋n⦌)).trans Homeomorph.ulift

def simplexCollar (n : ℕ) : TopCat.{u} := TopCat.of (ULift.{u} (radialNeighborhood n))

def simplexCollarBoundary (n : ℕ) : |(SSet.boundary.{u} n).toSSet| ⟶ simplexCollar n :=
  TopCat.ofHom ⟨fun x => ULift.up (boundaryInclusion n (boundaryCoordinateHomeo n x)),
    continuous_uliftUp.comp ((boundaryInclusion n).continuous.comp
      (boundaryCoordinateHomeo n).continuous)⟩

def simplexCollarEmbedding (n : ℕ) : simplexCollar.{u} n ⟶ |(Δ[n] : SSet.{u})| :=
  TopCat.ofHom ⟨fun x => (simplexCoordinateHomeo n).symm x.down.val,
    (simplexCoordinateHomeo n).symm.continuous.comp
      (continuous_subtype_val.comp continuous_uliftDown)⟩

theorem simplexCollarEmbedding_isOpenEmbedding (n : ℕ) :
    Topology.IsOpenEmbedding (simplexCollarEmbedding.{u} n) :=
  (simplexCoordinateHomeo n).symm.isOpenEmbedding.comp
    ((isOpen_radialNeighborhood n).isOpenEmbedding_subtypeVal.comp
      Homeomorph.ulift.isOpenEmbedding)

theorem simplexCollarBoundary_embedding (n : ℕ) :
    simplexCollarBoundary.{u} n ≫ simplexCollarEmbedding n =
      SSet.toTop.map (SSet.boundary n).ι := by
  ext x
  apply (simplexCoordinateHomeo n).injective
  change simplexCoordinateHomeo n ((simplexCoordinateHomeo n).symm
      (boundaryCoordinateHomeo n x).val) = _
  rw [Homeomorph.apply_symm_apply]
  exact boundaryCoordinateHomeo_inclusion n x

def simplexCollarRetraction (n : ℕ) : simplexCollar.{u} n ⟶ |(SSet.boundary.{u} n).toSSet| :=
  TopCat.ofHom ⟨fun x => (boundaryCoordinateHomeo n).symm (radialRetraction n x.down),
    (boundaryCoordinateHomeo n).symm.continuous.comp
      ((radialRetraction n).continuous.comp continuous_uliftDown)⟩

theorem simplexCollarBoundary_retraction (n : ℕ) :
    simplexCollarBoundary.{u} n ≫ simplexCollarRetraction n = 𝟙 _ := by
  ext x
  change (boundaryCoordinateHomeo n).symm
    ((radialRetraction n).comp (boundaryInclusion n) (boundaryCoordinateHomeo n x)) = x
  rw [radialRetraction_boundaryInclusion]
  exact (boundaryCoordinateHomeo n).symm_apply_apply x

def simplexCollarHomotopy (n : ℕ) :
    TopCat.Homotopy (𝟙 (simplexCollar.{u} n))
      (simplexCollarRetraction n ≫ simplexCollarBoundary n) where
  toFun p := ULift.up (radialHomotopy n (p.1, p.2.down))
  continuous_toFun := continuous_uliftUp.comp
    ((radialHomotopy n).continuous.comp
      (continuous_fst.prodMk (continuous_uliftDown.comp continuous_snd)))
  map_zero_left x := by
    change ULift.{u} (radialNeighborhood n) at x
    change ULift.up (radialHomotopy n (0, x.down)) = x
    exact congrArg ULift.up ((radialHomotopy n).map_zero_left x.down)
  map_one_left x := by
    change ULift.{u} (radialNeighborhood n) at x
    change ULift.up (radialHomotopy n (1, x.down)) =
      ULift.up (boundaryInclusion n (boundaryCoordinateHomeo n
        ((boundaryCoordinateHomeo n).symm (radialRetraction n x.down))))
    rw [Homeomorph.apply_symm_apply]
    exact congrArg ULift.up ((radialHomotopy n).map_one_left x.down)

theorem simplexCollarHomotopy_fixed (n : ℕ) (s : unitInterval)
    (x : |(SSet.boundary.{u} n).toSSet|) :
    simplexCollarHomotopy n (s, simplexCollarBoundary n x) = simplexCollarBoundary n x := by
  change ULift.up (radialHomotopy n (s, boundaryInclusion n (boundaryCoordinateHomeo n x))) = _
  rw [radialHomotopy_fixed]
  rfl

end Sharpness.SingularAttachmentComparison
