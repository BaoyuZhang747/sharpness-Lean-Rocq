import Sharpness.Unconditional.RealizationPrismNaturalityCoordinates

/-! The staircase lift of an arbitrary simplex order map, with its
coalescence and interval-coordinate identities. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace Sharpness.RealizationPrism
open scoped BigOperators

/-- Lift an order map to the staircase simplex at a chosen split vertex. -/
def staircaseLift {n m : ℕ} (a : Fin (n + 1) →o Fin (m + 1)) (i : Fin (n + 1)) :
    Fin (n + 2) →o Fin (m + 2) where
  toFun k := if k ≤ i.castSucc then (a (i.predAbove k)).castSucc else (a (i.predAbove k)).succ
  monotone' := by
    intro k l hkl
    have hp := a.monotone (Fin.predAbove_right_monotone i hkl)
    dsimp only
    split_ifs with hk hl hl
    · exact hp
    · exact (Fin.castSucc_le_castSucc_iff.mpr hp).trans (Fin.castSucc_le_succ _)
    · exact (hk (hkl.trans hl)).elim
    · exact Fin.succ_le_succ_iff.mpr hp

theorem staircaseLift_predAbove {n m : ℕ} (a : Fin (n + 1) →o Fin (m + 1))
    (i : Fin (n + 1)) (k : Fin (n + 2)) :
    (a i).predAbove (staircaseLift a i k) = a (i.predAbove k) := by
  by_cases hk : k ≤ i.castSucc
  · have hp : i.predAbove k ≤ i := by
      simpa using Fin.predAbove_right_monotone i hk
    change (a i).predAbove (if k ≤ i.castSucc then _ else _) = _
    rw [if_pos hk]
    exact Fin.predAbove_castSucc_of_le _ _ (a.monotone hp)
  · have hk' : i.succ ≤ k := Fin.castSucc_lt_iff_succ_le.mp (lt_of_not_ge hk)
    have hp : i ≤ i.predAbove k := by
      simpa using Fin.predAbove_right_monotone i hk'
    change (a i).predAbove (if k ≤ i.castSucc then _ else _) = _
    rw [if_neg hk]
    exact Fin.predAbove_succ_of_le _ _ (a.monotone hp)

theorem staircaseLift_lt_succ {n m : ℕ} (a : Fin (n + 1) →o Fin (m + 1))
    (i : Fin (n + 1)) (k : Fin (n + 2)) :
    staircaseLift a i k < (a i).succ ↔ k ≤ i.castSucc := by
  by_cases hk : k ≤ i.castSucc
  · have hp : i.predAbove k ≤ i := by
      simpa using Fin.predAbove_right_monotone i hk
    change (if k ≤ i.castSucc then _ else _) < (a i).succ ↔ _
    rw [if_pos hk]
    exact iff_of_true
      ((Fin.castSucc_le_castSucc_iff.mpr (a.monotone hp)).trans_lt Fin.castSucc_lt_succ) hk
  · have hk' : i.succ ≤ k := Fin.castSucc_lt_iff_succ_le.mp (lt_of_not_ge hk)
    have hp : i ≤ i.predAbove k := by
      simpa using Fin.predAbove_right_monotone i hk'
    change (if k ≤ i.castSucc then _ else _) < (a i).succ ↔ _
    rw [if_neg hk]
    exact iff_of_false (not_lt.mpr (Fin.succ_le_succ_iff.mpr (a.monotone hp))) hk

@[simp] theorem staircaseLift_castSucc {n m : ℕ} (a : Fin (n + 1) →o Fin (m + 1))
    (i : Fin (n + 1)) : staircaseLift a i i.castSucc = (a i).castSucc := by
  simp [staircaseLift]

@[simp] theorem staircaseLift_succ {n m : ℕ} (a : Fin (n + 1) →o Fin (m + 1))
    (i : Fin (n + 1)) : staircaseLift a i i.succ = (a i).succ := by
  simp [staircaseLift, not_le.mpr Fin.castSucc_lt_succ]

theorem map_staircaseLift_coalesce {n m : ℕ} (a : Fin (n + 1) →o Fin (m + 1))
    (i : Fin (n + 1)) (y : stdSimplex ℝ (Fin (n + 2))) :
    stdSimplex.map (a i).predAbove (stdSimplex.map (staircaseLift a i) y) =
      stdSimplex.map a (stdSimplex.map i.predAbove y) := by
  rw [stdSimplex.map_comp_apply, stdSimplex.map_comp_apply]
  congr 1
  funext k
  exact staircaseLift_predAbove a i k

end Sharpness.RealizationPrism
