import Sharpness.Unconditional.RealizationUnitHomologySubdivisionGeometry

/-! Actual affine simplex composition and compatibility with every simplicial
index map. These identities support boundary cancellation in subdivision. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
noncomputable section
universe u
namespace Sharpness.RealizationUnitHomology
open scoped BigOperators

theorem affineSimplexMap_comp {k n m : ℕ}
    (v : Fin (n + 1) → _root_.stdSimplex ℝ (Fin (m + 1)))
    (w : Fin (k + 1) → _root_.stdSimplex ℝ (Fin (n + 1))) :
    (affineSimplexMap v).comp (affineSimplexMap w) =
      affineSimplexMap (fun j => affineSimplexMap v (w j)) := by
  apply ContinuousMap.ext
  intro t
  apply Subtype.ext
  funext i
  change (∑ j, (∑ l, t l * w l j) * v j i) =
    ∑ l, t l * (∑ j, w l j * v j i)
  simp_rw [Finset.sum_mul, Finset.mul_sum, mul_assoc]
  rw [Finset.sum_comm]

@[simp] theorem affineSimplexMap_vertices (n : ℕ) :
    affineSimplexMap (fun j : Fin (n + 1) => _root_.stdSimplex.vertex j) =
      ContinuousMap.id (_root_.stdSimplex ℝ (Fin (n + 1))) := by
  apply ContinuousMap.ext
  intro t
  apply Subtype.ext
  funext i
  change (∑ j, t j * (Pi.single j (1 : ℝ) : Fin (n + 1) → ℝ) i) = t i
  simp [Pi.single_apply, mul_ite, eq_comm]

/-- Every index map gives the corresponding affine vertex map. -/
theorem stdSimplex_map_eq_affine {n m : ℕ} (f : Fin (n + 1) → Fin (m + 1)) :
    (⟨_root_.stdSimplex.map f, _root_.stdSimplex.continuous_map f⟩ :
      C(_root_.stdSimplex ℝ (Fin (n + 1)), _root_.stdSimplex ℝ (Fin (m + 1)))) =
        affineSimplexMap (fun j => _root_.stdSimplex.vertex (f j)) := by
  apply ContinuousMap.ext
  intro t
  apply Subtype.ext
  funext i
  change FunOnFinite.linearMap ℝ ℝ f t i =
    ∑ j, t j * (Pi.single (f j) (1 : ℝ) : Fin (m + 1) → ℝ) i
  simp [FunOnFinite.linearMap_apply_apply, Finset.sum_filter, Pi.single_apply, mul_ite, eq_comm]

/-- Restricting an affine simplex along any simplex map restricts its vertices.
This includes every face and every degeneracy. -/
theorem affineSimplexMap_index {k n m : ℕ}
    (v : Fin (n + 1) → _root_.stdSimplex ℝ (Fin (m + 1)))
    (f : Fin (k + 1) → Fin (n + 1)) :
    (affineSimplexMap v).comp ⟨_root_.stdSimplex.map f, _root_.stdSimplex.continuous_map f⟩ =
      affineSimplexMap (fun j => v (f j)) := by
  rw [stdSimplex_map_eq_affine, affineSimplexMap_comp]
  simp only [affineSimplexMap_vertex]

end Sharpness.RealizationUnitHomology
