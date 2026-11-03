import Sharpness.Unconditional.RealizationSubdivisionMeshCells
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

/-! Iterated actual barycentric cells have vanishing mesh. Compactness and
the metric Lebesgue lemma give uniform eventual containment in open covers. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u v

namespace Sharpness.RealizationUnitHomology
open Filter

def barycentricMeshFactor (n : ℕ) : ℝ := (n : ℝ) / (n + 1)

theorem barycentricMeshFactor_nonneg (n : ℕ) : 0 ≤ barycentricMeshFactor n := by
  unfold barycentricMeshFactor
  positivity

theorem barycentricMeshFactor_lt_one (n : ℕ) : barycentricMeshFactor n < 1 := by
  unfold barycentricMeshFactor
  exact (div_lt_one (by positivity : (0 : ℝ) < n + 1)).mpr (by linarith)

def iteratedAffineVertices {n m : ℕ}
    (v : Fin (n + 1) → _root_.stdSimplex ℝ (Fin (m + 1))) :
    List (Equiv.Perm (Fin (n + 1))) → Fin (n + 1) → _root_.stdSimplex ℝ (Fin (m + 1))
  | [] => v
  | p :: ps => fun j => affineSimplexMap (iteratedAffineVertices v ps) (prefixBarycenter p j)

def iteratedAffineCell {n m : ℕ}
    (v : Fin (n + 1) → _root_.stdSimplex ℝ (Fin (m + 1)))
    (ps : List (Equiv.Perm (Fin (n + 1)))) :=
  affineSimplexMap (iteratedAffineVertices v ps)

theorem iteratedAffineCell_cons {n m : ℕ}
    (v : Fin (n + 1) → _root_.stdSimplex ℝ (Fin (m + 1)))
    (p : Equiv.Perm (Fin (n + 1))) (ps : List (Equiv.Perm (Fin (n + 1)))) :
    iteratedAffineCell v (p :: ps) = (iteratedAffineCell v ps).comp (barycentricCell p) :=
  (affineSimplexMap_comp _ _).symm

theorem iteratedAffineCell_diam_le {n m : ℕ}
    (v : Fin (n + 1) → _root_.stdSimplex ℝ (Fin (m + 1)))
    (ps : List (Equiv.Perm (Fin (n + 1)))) :
    Metric.diam (Set.range (iteratedAffineCell v ps)) ≤
      barycentricMeshFactor n ^ ps.length * Metric.diam (Set.range (affineSimplexMap v)) := by
  induction ps with
  | nil => simp [iteratedAffineCell, iteratedAffineVertices]
  | cons p ps ih =>
    rw [iteratedAffineCell_cons]
    calc
      _ ≤ barycentricMeshFactor n * Metric.diam (Set.range (iteratedAffineCell v ps)) :=
        affineBarycentricCell_diam_le (iteratedAffineVertices v ps) p
      _ ≤ barycentricMeshFactor n *
          (barycentricMeshFactor n ^ ps.length * Metric.diam (Set.range (affineSimplexMap v))) :=
        mul_le_mul_of_nonneg_left ih (barycentricMeshFactor_nonneg n)
      _ = _ := by simp only [List.length_cons, pow_succ]; ring

def iteratedBarycentricCell {n : ℕ} (ps : List (Equiv.Perm (Fin (n + 1)))) :=
  iteratedAffineCell (fun j => _root_.stdSimplex.vertex j) ps

@[simp] theorem iteratedBarycentricCell_nil (n : ℕ) :
    iteratedBarycentricCell ([] : List (Equiv.Perm (Fin (n + 1)))) =
      ContinuousMap.id (_root_.stdSimplex ℝ (Fin (n + 1))) :=
  affineSimplexMap_vertices n

theorem iteratedBarycentricCell_cons {n : ℕ} (p : Equiv.Perm (Fin (n + 1)))
    (ps : List (Equiv.Perm (Fin (n + 1)))) :
    iteratedBarycentricCell (p :: ps) = (iteratedBarycentricCell ps).comp (barycentricCell p) :=
  iteratedAffineCell_cons _ _ _

theorem iteratedBarycentricCell_diam_le {n : ℕ}
    (ps : List (Equiv.Perm (Fin (n + 1)))) :
    Metric.diam (Set.range (iteratedBarycentricCell ps)) ≤ barycentricMeshFactor n ^ ps.length := by
  have h := iteratedAffineCell_diam_le (fun j : Fin (n + 1) => _root_.stdSimplex.vertex j) ps
  refine h.trans ?_
  simpa only [mul_one] using mul_le_mul_of_nonneg_left
    (affineSimplexMap_diam_le_one (fun j : Fin (n + 1) => _root_.stdSimplex.vertex j))
    (pow_nonneg (barycentricMeshFactor_nonneg n) ps.length)

/-- One depth works for every cell at every subsequent subdivision depth. -/
theorem iteratedBarycentricCell_eventually_small {n : ℕ} {ι : Type v}
    (U : ι → Set (_root_.stdSimplex ℝ (Fin (n + 1))))
    (hU : ∀ i, IsOpen (U i)) (hcover : ∀ x, ∃ i, x ∈ U i) :
    ∃ N : ℕ, ∀ ps : List (Equiv.Perm (Fin (n + 1))), N ≤ ps.length →
      ∃ i, Set.range (iteratedBarycentricCell ps) ⊆ U i := by
  obtain ⟨δ, hδ, hball⟩ := lebesgue_number_lemma_of_metric
    (s := Set.univ) isCompact_univ hU (by
      intro x _
      obtain ⟨i, hi⟩ := hcover x
      exact Set.mem_iUnion.mpr ⟨i, hi⟩)
  have ht := tendsto_pow_atTop_nhds_zero_of_lt_one
    (barycentricMeshFactor_nonneg n) (barycentricMeshFactor_lt_one n)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (ht.eventually (gt_mem_nhds hδ))
  refine ⟨N, fun ps hps => ?_⟩
  let z := iteratedBarycentricCell ps (_root_.stdSimplex.vertex 0)
  obtain ⟨i, hi⟩ := hball z (Set.mem_univ z)
  refine ⟨i, ?_⟩
  rintro y ⟨t, rfl⟩
  apply hi
  apply lt_of_le_of_lt _ (hN ps.length hps)
  exact (Metric.dist_le_diam_of_mem
    (isCompact_range (iteratedBarycentricCell ps).continuous).isBounded
    (Set.mem_range_self t) (Set.mem_range_self (_root_.stdSimplex.vertex 0))).trans
      (iteratedBarycentricCell_diam_le ps)

/-- Eventual smallness after any continuous singular simplex; no metric on
the target space is required. -/
theorem iteratedBarycentricCell_eventually_small_comp {X : Type u} [TopologicalSpace X]
    {n : ℕ} (σ : C(_root_.stdSimplex ℝ (Fin (n + 1)), X)) {ι : Type v}
    (U : ι → Set X) (hU : ∀ i, IsOpen (U i))
    (hcover : ∀ t, ∃ i, σ t ∈ U i) :
    ∃ N : ℕ, ∀ ps : List (Equiv.Perm (Fin (n + 1))), N ≤ ps.length →
      ∃ i, Set.range (σ.comp (iteratedBarycentricCell ps)) ⊆ U i := by
  obtain ⟨N, hN⟩ := iteratedBarycentricCell_eventually_small
    (fun i => σ ⁻¹' U i) (fun i => (hU i).preimage σ.continuous) hcover
  refine ⟨N, fun ps hps => ?_⟩
  obtain ⟨i, hi⟩ := hN ps hps
  refine ⟨i, ?_⟩
  rintro _ ⟨t, rfl⟩
  exact hi (Set.mem_range_self t)

end Sharpness.RealizationUnitHomology
