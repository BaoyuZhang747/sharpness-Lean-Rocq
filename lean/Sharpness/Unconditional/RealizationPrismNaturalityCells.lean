import Sharpness.Unconditional.RealizationPrismNaturality
import Sharpness.Unconditional.RealizationNerveHomotopyGluing

/-! Closed prism-cell transport and its exact barycentric-coordinate
identity under every simplex order map. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace Sharpness.RealizationPrism
open scoped BigOperators

theorem predAbove_lt_pivot_iff {n : ℕ} (i : Fin (n + 1)) (k : Fin (n + 2)) :
    i.predAbove k < i ↔ k < i.castSucc := by
  refine Fin.succAboveCases i.castSucc ?_ (fun j => ?_) k
  · simp
  · simp [Fin.succAbove_lt_iff_castSucc_lt]

theorem partialWeight_predAbove {n : ℕ} (i : Fin (n + 1))
    (y : stdSimplex ℝ (Fin (n + 2))) :
    partialWeight (fun j => stdSimplex.map i.predAbove y j) i =
      partialWeight (fun j => y j) i.castSucc := by
  rw [partialWeight_map]
  unfold partialWeight
  apply Finset.sum_congr rfl
  intro k hk
  simp only [predAbove_lt_pivot_iff]

theorem upperWeight_eq_sum {n : ℕ} (x : Fin n → ℝ) (i : Fin n) :
    partialWeight x i + x i = ∑ j, if j ≤ i then x j else 0 := by
  have hi : x i = ∑ j : Fin n, if j = i then x j else 0 := by simp
  unfold partialWeight
  rw [hi, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  rcases lt_trichotomy j i with hlt | he | hgt
  · simp [hlt, le_of_lt hlt, ne_of_lt hlt]
  · subst j
    simp
  · simp [not_lt.mpr (le_of_lt hgt), not_le.mpr hgt, ne_of_gt hgt]

theorem partialWeight_map_le {n m : ℕ} (a : Fin (n + 1) →o Fin (m + 1))
    (x : stdSimplex ℝ (Fin (n + 1))) (i : Fin (n + 1)) :
    partialWeight (fun j => stdSimplex.map a x j) (a i) ≤ partialWeight (fun j => x j) i := by
  rw [partialWeight_map]
  unfold partialWeight
  apply Finset.sum_le_sum
  intro k hk
  by_cases hki : k < i
  · rw [if_pos hki]
    split_ifs
    · rfl
    · exact stdSimplex.zero_le x k
  · have ha : ¬ a k < a i := not_lt.mpr (a.monotone (le_of_not_gt hki))
    simp [hki, ha]

theorem upperWeight_le_map {n m : ℕ} (a : Fin (n + 1) →o Fin (m + 1))
    (x : stdSimplex ℝ (Fin (n + 1))) (i : Fin (n + 1)) :
    partialWeight (fun j => x j) i + x i ≤
      partialWeight (fun j => stdSimplex.map a x j) (a i) + stdSimplex.map a x (a i) := by
  rw [upperWeight_eq_sum, upperWeight_eq_sum, sum_map_indicator]
  apply Finset.sum_le_sum
  intro k hk
  by_cases hki : k ≤ i
  · simp [hki, a.monotone hki]
  · rw [if_neg hki]
    split_ifs
    · exact stdSimplex.zero_le x k
    · rfl

/-- Every source prism cell maps into its corresponding target cell.
The inequalities are non-strict, so all faces and zero coordinates remain covered. -/
theorem map_mem_cell {n m : ℕ} (a : Fin (n + 1) →o Fin (m + 1))
    (i : Fin (n + 1)) (p : unitInterval × stdSimplex ℝ (Fin (n + 1)))
    (hp : p ∈ cell i) : (p.1, stdSimplex.map a p.2) ∈ cell (a i) :=
  ⟨(partialWeight_map_le a p.2 i).trans hp.1,
    hp.2.trans (upperWeight_le_map a p.2 i)⟩

theorem partialWeight_staircaseLift {n m : ℕ} (a : Fin (n + 1) →o Fin (m + 1))
    (i : Fin (n + 1)) (y : stdSimplex ℝ (Fin (n + 2))) :
    partialWeight (fun j => stdSimplex.map (staircaseLift a i) y j) (a i).succ =
      partialWeight (fun j => y j) i.succ := by
  rw [partialWeight_map]
  unfold partialWeight
  apply Finset.sum_congr rfl
  intro k hk
  simp only [staircaseLift_lt_succ, Fin.le_castSucc_iff]

theorem partialWeight_split_succ {n : ℕ} (i : Fin (n + 1))
    (x : stdSimplex ℝ (Fin (n + 1))) (a : ℝ) (ha₀ : 0 ≤ a) (ha₁ : a ≤ x i) :
    partialWeight (fun j => split i x a ha₀ ha₁ j) i.succ =
      partialWeight (fun j => x j) i + a := by
  have h := partialWeight_predAbove i (split i x a ha₀ ha₁)
  rw [map_split] at h
  rw [partialWeight_succ_eq, ← h, split_at]

theorem partialWeight_cellSimplex_succ {n : ℕ} (i : Fin (n + 1)) (p : cell i) :
    partialWeight (fun j => cellSimplex i p j) i.succ = 1 - (p.1.1 : ℝ) := by
  dsimp only [cellSimplex, ContinuousMap.coe_mk]
  rw [partialWeight_split_succ]
  ring

/-- Exact simplex-prism naturality on each closed cell, including all
degeneracies and boundary cells. -/
theorem map_cellSimplex_staircaseLift {n m : ℕ} (a : Fin (n + 1) →o Fin (m + 1))
    (i : Fin (n + 1)) (p : cell i) :
    stdSimplex.map (staircaseLift a i) (cellSimplex i p) =
      cellSimplex (a i) ⟨(p.1.1, stdSimplex.map a p.1.2), map_mem_cell a i p.1 p.2⟩ := by
  let y := stdSimplex.map (staircaseLift a i) (cellSimplex i p)
  have hy : stdSimplex.map (a i).predAbove y = stdSimplex.map a p.1.2 := by
    rw [map_staircaseLift_coalesce, map_cellSimplex]
  have hw : partialWeight (fun j => y j) (a i).succ = 1 - (p.1.1 : ℝ) := by
    rw [partialWeight_staircaseLift, partialWeight_cellSimplex_succ]
  have hp := partialWeight_predAbove (a i) y
  rw [hy] at hp
  have hya : y (a i).castSucc =
      1 - (p.1.1 : ℝ) - partialWeight (fun j => stdSimplex.map a p.1.2 j) (a i) := by
    rw [partialWeight_succ_eq] at hw
    linarith
  have hc := map_mem_cell a i p.1 p.2
  exact split_unique (a i) (stdSimplex.map a p.1.2) _
    (by linarith [hc.1]) (by linarith [hc.2]) y hy hya

end Sharpness.RealizationPrism
