import Sharpness.Unconditional.RealizationNerveHomotopyPrism
import Mathlib.Order.Fin.Basic

/-! Finite pushforward identities used by simplex-prism naturality.
They allow arbitrary order maps and hence include degenerate simplices. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace Sharpness.RealizationPrism
open scoped BigOperators

theorem sum_map_indicator {n m : ℕ} (f : Fin n → Fin m)
    (x : stdSimplex ℝ (Fin n)) (p : Fin m → Prop) [DecidablePred p] :
    (∑ j, if p j then stdSimplex.map f x j else 0) =
      ∑ k, if p (f k) then x k else 0 := by
  simp only [stdSimplex.map_coe, FunOnFinite.linearMap_apply_apply, Finset.sum_filter]
  trans ∑ j : Fin m, ∑ k : Fin n, if p j then (if f k = j then x k else 0) else 0
  · apply Finset.sum_congr rfl
    intro j hj
    by_cases hp : p j <;> simp [hp]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  trans ∑ j : Fin m, if f k = j then (if p (f k) then x k else 0) else 0
  · apply Finset.sum_congr rfl
    intro j hj
    by_cases he : f k = j
    · subst j
      simp
    · simp [he]
  simp

theorem partialWeight_map {n m : ℕ} (f : Fin n → Fin m)
    (x : stdSimplex ℝ (Fin n)) (i : Fin m) :
    partialWeight (fun j => stdSimplex.map f x j) i =
      ∑ k, if f k < i then x k else 0 :=
  sum_map_indicator f x (fun j => j < i)

theorem map_predAbove_apply {n : ℕ} (i : Fin (n + 1))
    (y : stdSimplex ℝ (Fin (n + 2))) (j : Fin (n + 1)) :
    stdSimplex.map i.predAbove y j =
      (if i = j then y i.castSucc else 0) + y (i.castSucc.succAbove j) := by
  change (FunOnFinite.linearMap ℝ ℝ i.predAbove y) j = _
  rw [FunOnFinite.linearMap_apply_apply, Finset.sum_filter,
    Fin.sum_univ_succAbove _ i.castSucc]
  simp only [Fin.predAbove_castSucc_self, Fin.predAbove_succAbove]
  simp

/-- Coalescence and the first split coordinate uniquely determine a split.
No strict positivity assumption on any coordinate is needed. -/
theorem split_unique {n : ℕ} (i : Fin (n + 1))
    (x : stdSimplex ℝ (Fin (n + 1))) (a : ℝ) (ha₀ : 0 ≤ a) (ha₁ : a ≤ x i)
    (y : stdSimplex ℝ (Fin (n + 2)))
    (hy : stdSimplex.map i.predAbove y = x) (hya : y i.castSucc = a) :
    y = split i x a ha₀ ha₁ := by
  apply stdSimplex.ext
  funext k
  refine Fin.succAboveCases i.castSucc ?_ (fun j => ?_) k
  · exact hya.trans (split_at i x a ha₀ ha₁).symm
  · rw [split_away]
    have h := congrArg (fun z : stdSimplex ℝ (Fin (n + 1)) => z j) hy
    rw [map_predAbove_apply] at h
    by_cases hj : j = i
    · subst j
      simp only [ite_true, hya, Function.update_self] at h ⊢
      linarith
    · simp only [Ne.symm hj, if_false, zero_add] at h
      simpa only [Function.update_of_ne hj] using h

end Sharpness.RealizationPrism
