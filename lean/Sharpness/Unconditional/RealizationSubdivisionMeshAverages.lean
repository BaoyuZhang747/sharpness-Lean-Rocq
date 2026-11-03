import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.Normed.Module.Convex

/-! Finite-average estimates for the actual barycentric mesh. These are
diameter estimates, not claims that a barycentric cell is a contraction map. -/
set_option autoImplicit false
noncomputable section

namespace Sharpness.RealizationUnitHomology
open scoped BigOperators

def meshAverage {ι : Type*} (s : Finset ι) (f : ι → ℝ) : ℝ :=
  (s.card : ℝ)⁻¹ * ∑ i ∈ s, f i

theorem meshAverage_sub_const {ι : Type*} (s : Finset ι) (hs : s.Nonempty)
    (f : ι → ℝ) (c : ℝ) :
    meshAverage s f - c = (s.card : ℝ)⁻¹ * ∑ i ∈ s, (f i - c) := by
  have hc : (s.card : ℝ) ≠ 0 := by exact_mod_cast hs.card_pos.ne'
  simp only [meshAverage, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
  field_simp

theorem meshAverage_sub_vertex_le {ι : Type*} (s : Finset ι) (hs : s.Nonempty)
    (f : ι → ℝ) (j : ι) {D : ℝ} (hD : ∀ i ∈ s, |f i - f j| ≤ D) :
    |meshAverage s f - f j| ≤ D := by
  have hc : (s.card : ℝ) ≠ 0 := by exact_mod_cast hs.card_pos.ne'
  rw [meshAverage_sub_const s hs, abs_mul,
    abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg s.card))]
  calc
    (s.card : ℝ)⁻¹ * |∑ i ∈ s, (f i - f j)| ≤
        (s.card : ℝ)⁻¹ * ∑ i ∈ s, |f i - f j| :=
      mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _)
        (inv_nonneg.mpr (Nat.cast_nonneg s.card))
    _ ≤ (s.card : ℝ)⁻¹ * ∑ _i ∈ s, D :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum hD)
        (inv_nonneg.mpr (Nat.cast_nonneg s.card))
    _ = D := by simp [hc]

theorem meshAverage_sub_average {ι : Type*} [DecidableEq ι]
    (s t : Finset ι) (hs : s.Nonempty) (hst : s ⊆ t) (f : ι → ℝ) :
    meshAverage s f - meshAverage t f =
      (t.card : ℝ)⁻¹ * ∑ j ∈ t \ s, (meshAverage s f - f j) := by
  have hsc : (s.card : ℝ) ≠ 0 := by exact_mod_cast hs.card_pos.ne'
  have htc : (t.card : ℝ) ≠ 0 := by exact_mod_cast (hs.mono hst).card_pos.ne'
  have hsum : (∑ j ∈ t \ s, (meshAverage s f - f j)) +
      (∑ j ∈ s, (meshAverage s f - f j)) =
      ∑ j ∈ t, (meshAverage s f - f j) := Finset.sum_sdiff hst
  rw [eq_sub_of_add_eq hsum]
  simp only [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, meshAverage]
  field_simp
  ring

/-- Averages of nested nonempty sets get closer by the proportion of new vertices. -/
theorem meshAverage_nested_le {ι : Type*} [DecidableEq ι]
    (s t : Finset ι) (hs : s.Nonempty) (hst : s ⊆ t) (f : ι → ℝ)
    {D : ℝ} (hD : ∀ i ∈ s, ∀ j ∈ t, |f i - f j| ≤ D) :
    |meshAverage s f - meshAverage t f| ≤
      (t.card : ℝ)⁻¹ * ((t \ s).card : ℝ) * D := by
  rw [meshAverage_sub_average s t hs hst, abs_mul,
    abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg t.card))]
  calc
    (t.card : ℝ)⁻¹ * |∑ j ∈ t \ s, (meshAverage s f - f j)| ≤
        (t.card : ℝ)⁻¹ * ∑ j ∈ t \ s, |meshAverage s f - f j| :=
      mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _)
        (inv_nonneg.mpr (Nat.cast_nonneg t.card))
    _ ≤ (t.card : ℝ)⁻¹ * ∑ _j ∈ t \ s, D := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Nat.cast_nonneg t.card))
      apply Finset.sum_le_sum
      intro j hj
      exact meshAverage_sub_vertex_le s hs f j (fun i hi => hD i hi j (Finset.mem_sdiff.mp hj).1)
    _ = _ := by simp [mul_assoc]

/-- Dimension-uniform shrink factor; this includes dimension zero. -/
theorem meshAverage_nested_dimension_le {ι : Type*} [DecidableEq ι]
    (s t : Finset ι) (hs : s.Nonempty) (hst : s ⊆ t) (f : ι → ℝ)
    (n : ℕ) (ht : t.card ≤ n + 1) {D : ℝ} (hD0 : 0 ≤ D)
    (hD : ∀ i ∈ s, ∀ j ∈ t, |f i - f j| ≤ D) :
    |meshAverage s f - meshAverage t f| ≤ ((n : ℝ) / (n + 1)) * D := by
  refine (meshAverage_nested_le s t hs hst f hD).trans ?_
  apply mul_le_mul_of_nonneg_right _ hD0
  have htpos : (0 : ℝ) < t.card := by exact_mod_cast (hs.mono hst).card_pos
  have hspos : (1 : ℝ) ≤ s.card := by exact_mod_cast hs.card_pos
  have htbound : (t.card : ℝ) ≤ n + 1 := by exact_mod_cast ht
  rw [Finset.card_sdiff_of_subset hst, Nat.cast_sub (Finset.card_le_card hst)]
  rw [← div_eq_inv_mul]
  apply (div_le_div_iff₀ htpos (by positivity : (0 : ℝ) < n + 1)).mpr
  nlinarith [show (0 : ℝ) ≤ n by positivity]

end Sharpness.RealizationUnitHomology
