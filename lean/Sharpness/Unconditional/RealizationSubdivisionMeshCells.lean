import Sharpness.Unconditional.RealizationSubdivisionMeshAffine
import Sharpness.Unconditional.RealizationUnitHomologySubdivisionFaces
import Mathlib.Order.Interval.Finset.Fin

/-! The sharp n/(n+1) diameter estimate for actual barycentric cell images
in the native sup metric on standard simplices, including n=0. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace Sharpness.RealizationUnitHomology
open scoped BigOperators

theorem affineSimplexMap_prefixBarycenter_average {n m : ℕ}
    (v : Fin (n + 1) → _root_.stdSimplex ℝ (Fin (m + 1)))
    (p : Equiv.Perm (Fin (n + 1))) (k : Fin (n + 1)) (i : Fin (m + 1)) :
    affineSimplexMap v (prefixBarycenter p k) i =
      meshAverage (Finset.Iic k) (fun j => v (p j) i) := by
  classical
  rw [affineSimplexMap_apply]
  rw [← Equiv.sum_comp p (fun j => prefixBarycenter p k j * v j i)]
  have hset : Finset.Iic k = Finset.univ.filter (fun j : Fin (n + 1) => j.val ≤ k.val) := by
    ext j
    simp only [Finset.mem_Iic, Finset.mem_filter, Finset.mem_univ, true_and, Fin.le_def]
  rw [meshAverage, Fin.card_Iic, hset, Finset.sum_filter, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp only [prefixBarycenter_apply, Equiv.symm_apply_apply, Nat.cast_add, Nat.cast_one]
  split_ifs <;> simp

theorem affineBarycentric_vertices_dist_le {n m : ℕ}
    (v : Fin (n + 1) → _root_.stdSimplex ℝ (Fin (m + 1)))
    (p : Equiv.Perm (Fin (n + 1))) {D : ℝ} (hD0 : 0 ≤ D)
    (hD : ∀ i j, dist (v i) (v j) ≤ D) (a b : Fin (n + 1)) :
    dist (affineSimplexMap v (prefixBarycenter p a))
      (affineSimplexMap v (prefixBarycenter p b)) ≤ ((n : ℝ) / (n + 1)) * D := by
  have hq : 0 ≤ ((n : ℝ) / (n + 1)) * D := by positivity
  have hordered (a b : Fin (n + 1)) (hab : a ≤ b) :
      dist (affineSimplexMap v (prefixBarycenter p a))
        (affineSimplexMap v (prefixBarycenter p b)) ≤ ((n : ℝ) / (n + 1)) * D := by
    apply (dist_pi_le_iff hq).mpr
    intro i
    rw [Real.dist_eq]
    change |affineSimplexMap v (prefixBarycenter p a) i -
      affineSimplexMap v (prefixBarycenter p b) i| ≤ _
    rw [affineSimplexMap_prefixBarycenter_average,
      affineSimplexMap_prefixBarycenter_average]
    apply meshAverage_nested_dimension_le (Finset.Iic a) (Finset.Iic b)
      ⟨0, Finset.mem_Iic.mpr (Fin.zero_le a)⟩
      (Finset.Iic_subset_Iic.mpr hab) (fun j => v (p j) i) n
    · rw [Fin.card_Iic]
      exact Nat.succ_le_of_lt b.isLt
    · exact hD0
    · intro j _ k _
      exact (dist_le_pi_dist (v (p j)).val (v (p k)).val i).trans (hD (p j) (p k))
  rcases le_total a b with hab | hba
  · exact hordered a b hab
  · rw [dist_comm]
    exact hordered b a hba

/-- Subdivision decreases the diameter of every actual affine simplex image
by n/(n+1). This is the mesh statement needed for iteration. -/
theorem affineBarycentricCell_diam_le {n m : ℕ}
    (v : Fin (n + 1) → _root_.stdSimplex ℝ (Fin (m + 1)))
    (p : Equiv.Perm (Fin (n + 1))) :
    Metric.diam (Set.range ((affineSimplexMap v).comp (barycentricCell p))) ≤
      ((n : ℝ) / (n + 1)) * Metric.diam (Set.range (affineSimplexMap v)) := by
  rw [barycentricCell, affineSimplexMap_comp]
  apply affineSimplexMap_diam_le _ (by positivity)
  exact affineBarycentric_vertices_dist_le v p Metric.diam_nonneg
    (affineSimplexMap_vertex_dist_le_diam v)

theorem affineBarycentricCell_zero_diam {m : ℕ}
    (v : Fin 1 → _root_.stdSimplex ℝ (Fin (m + 1))) (p : Equiv.Perm (Fin 1)) :
    Metric.diam (Set.range ((affineSimplexMap v).comp (barycentricCell p))) = 0 := by
  apply le_antisymm _ Metric.diam_nonneg
  simpa using affineBarycentricCell_diam_le v p

end Sharpness.RealizationUnitHomology
