import Sharpness.Unconditional.RealizationBoundaryCoordinates
import Mathlib.Topology.Homotopy.Basic

/-! A boundary-fixed deformation of the actual open radial neighborhood onto
the literal coordinate boundary of a topological standard simplex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Sharpness.RealizationBoundary
open scoped BigOperators

def boundaryInclusion (n : ℕ) : C(boundary n, radialNeighborhood n) where
  toFun t := ⟨t.val, boundary_subset_radialNeighborhood n t.property⟩
  continuous_toFun := continuous_subtype_val.subtype_mk _

def radialRetraction (n : ℕ) : C(radialNeighborhood n, boundary n) where
  toFun t := ⟨radialProjection t, radialProjection_mem_boundary t⟩
  continuous_toFun := (continuous_radialProjection n).subtype_mk _

theorem radialRetraction_boundaryInclusion (n : ℕ) :
    (radialRetraction n).comp (boundaryInclusion n) = ContinuousMap.id (boundary n) := by
  ext t i
  exact congrArg (fun s : Simplex n => s i) (radialProjection_fixed t)

def radialStage {n : ℕ} (s : unitInterval) (t : radialNeighborhood n) : Simplex n :=
  ⟨fun i => (1 - s.val) * t.val i + s.val * radialProjection t i,
    ⟨fun i => add_nonneg
      (mul_nonneg (sub_nonneg.mpr s.property.2) (_root_.stdSimplex.zero_le t.val i))
      (mul_nonneg s.property.1 (_root_.stdSimplex.zero_le (radialProjection t) i)), by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      simp only [_root_.stdSimplex.sum_eq_one, mul_one]
      ring⟩⟩

theorem radialStage_minimum_le {n : ℕ} (s : unitInterval) (t : radialNeighborhood n) :
    minimumCoordinate (radialStage s t) ≤ minimumCoordinate t.val := by
  obtain ⟨i, hi⟩ := exists_minimumCoordinate t.val
  apply (minimumCoordinate_le (radialStage s t) i).trans
  change (1 - s.val) * t.val i + s.val *
    ((t.val i - minimumCoordinate t.val) / _) ≤ minimumCoordinate t.val
  rw [← hi, sub_self, zero_div, mul_zero, add_zero]
  have hs := mul_nonneg s.property.1 (minimumCoordinate_nonneg t.val)
  nlinarith

theorem radialStage_mem {n : ℕ} (s : unitInterval) (t : radialNeighborhood n) :
    radialStage s t ∈ radialNeighborhood n := by
  change (n + 1 : ℝ) * minimumCoordinate (radialStage s t) < 1
  exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left (radialStage_minimum_le s t)
    (by positivity)) t.property

theorem continuous_radialStage (n : ℕ) :
    Continuous (fun p : unitInterval × radialNeighborhood n => radialStage p.1 p.2) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro i
  have hs : Continuous (fun p : unitInterval × radialNeighborhood n => p.1.val) :=
    continuous_subtype_val.comp continuous_fst
  have ht : Continuous (fun p : unitInterval × radialNeighborhood n => p.2.val i) :=
    (((continuous_apply i).comp continuous_subtype_val).comp continuous_subtype_val).comp
      continuous_snd
  have hr : Continuous (fun p : unitInterval × radialNeighborhood n => radialProjection p.2 i) :=
    ((continuous_apply i).comp continuous_subtype_val).comp
      ((continuous_radialProjection n).comp continuous_snd)
  exact ((continuous_const.sub hs).mul ht).add (hs.mul hr)

def radialHomotopy (n : ℕ) :
    ContinuousMap.Homotopy (ContinuousMap.id (radialNeighborhood n))
      ((boundaryInclusion n).comp (radialRetraction n)) where
  toFun p := ⟨radialStage p.1 p.2, radialStage_mem p.1 p.2⟩
  continuous_toFun := (continuous_radialStage n).subtype_mk _
  map_zero_left t := by
    apply Subtype.ext
    apply Subtype.ext
    funext i
    change (1 - (0 : ℝ)) * t.val i + 0 * radialProjection t i = t.val i
    ring
  map_one_left t := by
    apply Subtype.ext
    apply Subtype.ext
    funext i
    change (1 - (1 : ℝ)) * t.val i + 1 * radialProjection t i = radialProjection t i
    ring

theorem radialHomotopy_fixed (n : ℕ) (s : unitInterval) (t : boundary n) :
    radialHomotopy n (s, boundaryInclusion n t) = boundaryInclusion n t := by
  apply Subtype.ext
  apply Subtype.ext
  funext i
  change (1 - s.val) * t.val i + s.val *
    radialProjection (⟨t.val, boundary_subset_radialNeighborhood n t.property⟩) i = t.val i
  rw [radialProjection_fixed]
  ring

end Sharpness.RealizationBoundary
