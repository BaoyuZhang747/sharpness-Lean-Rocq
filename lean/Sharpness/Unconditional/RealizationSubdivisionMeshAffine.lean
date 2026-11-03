import Sharpness.Unconditional.RealizationUnitHomologyAffineNaturality
import Sharpness.Unconditional.RealizationSubdivisionMeshAverages

/-! Actual affine-simplex images lie in the convex hull of their vertices.
Consequently their diameter is controlled by the pairwise vertex distances. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace Sharpness.RealizationUnitHomology
open scoped BigOperators

theorem affineSimplexMap_mem_convexHull {n m : ℕ}
    (v : Fin (n + 1) → _root_.stdSimplex ℝ (Fin (m + 1)))
    (x : _root_.stdSimplex ℝ (Fin (n + 1))) :
    (affineSimplexMap v x).val ∈ convexHull ℝ (Set.range (fun j => (v j).val)) := by
  have h := (convex_convexHull ℝ (Set.range (fun j => (v j).val))).sum_mem
    (t := Finset.univ) (w := fun j => x j) (z := fun j => (v j).val)
    (fun j _ => _root_.stdSimplex.zero_le x j) (_root_.stdSimplex.sum_eq_one x)
    (fun j _ => subset_convexHull ℝ _ (Set.mem_range_self j))
  convert h using 1
  ext i
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rfl

theorem affineSimplexMap_dist_le {n m : ℕ}
    (v : Fin (n + 1) → _root_.stdSimplex ℝ (Fin (m + 1)))
    {D : ℝ} (hD : ∀ i j, dist (v i) (v j) ≤ D)
    (x y : _root_.stdSimplex ℝ (Fin (n + 1))) :
    dist (affineSimplexMap v x) (affineSimplexMap v y) ≤ D := by
  obtain ⟨_, ⟨i, rfl⟩, _, ⟨j, rfl⟩, h⟩ := convexHull_exists_dist_ge2
    (affineSimplexMap_mem_convexHull v x) (affineSimplexMap_mem_convexHull v y)
  exact h.trans (hD i j)

theorem affineSimplexMap_diam_le {n m : ℕ}
    (v : Fin (n + 1) → _root_.stdSimplex ℝ (Fin (m + 1)))
    {D : ℝ} (hD0 : 0 ≤ D) (hD : ∀ i j, dist (v i) (v j) ≤ D) :
    Metric.diam (Set.range (affineSimplexMap v)) ≤ D := by
  apply Metric.diam_le_of_forall_dist_le hD0
  rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
  exact affineSimplexMap_dist_le v hD x y

theorem affineSimplexMap_vertex_dist_le_diam {n m : ℕ}
    (v : Fin (n + 1) → _root_.stdSimplex ℝ (Fin (m + 1))) (i j : Fin (n + 1)) :
    dist (v i) (v j) ≤ Metric.diam (Set.range (affineSimplexMap v)) := by
  apply Metric.dist_le_diam_of_mem (isCompact_range (affineSimplexMap v).continuous).isBounded
  · exact ⟨_root_.stdSimplex.vertex i, affineSimplexMap_vertex v i⟩
  · exact ⟨_root_.stdSimplex.vertex j, affineSimplexMap_vertex v j⟩

theorem affineSimplexMap_diam_le_one {n m : ℕ}
    (v : Fin (n + 1) → _root_.stdSimplex ℝ (Fin (m + 1))) :
    Metric.diam (Set.range (affineSimplexMap v)) ≤ 1 := by
  apply affineSimplexMap_diam_le v zero_le_one
  intro i j
  exact (Metric.dist_le_diam_of_mem (bounded_stdSimplex _) (v i).property (v j).property).trans
    diam_stdSimplex_le

end Sharpness.RealizationUnitHomology
