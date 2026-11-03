import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Topology.Piecewise
import Sharpness.Unconditional.RealizationNerveHomotopyDescent
import Mathlib.AlgebraicTopology.SimplicialSet.Homotopy

/-! Barycentric coordinates for the finite closed cells of the simplex prism.
These are geometric preparation for realization of a simplicial homotopy. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace Sharpness.RealizationPrism
open scoped BigOperators

/-- Sum of the coordinates strictly preceding a vertex. -/
def partialWeight {n : ℕ} (x : Fin n → ℝ) (i : Fin n) : ℝ :=
  ∑ j, if j < i then x j else 0

@[simp] theorem prefix_zero {n : ℕ} (x : Fin (n + 1) → ℝ) : partialWeight x 0 = 0 := by
  simp [partialWeight]

theorem prefix_succ {n : ℕ} (x : Fin (n + 2) → ℝ) (i : Fin (n + 1)) :
    partialWeight x i.succ = x 0 + partialWeight (fun j => x j.succ) i := by
  simp [partialWeight, Fin.sum_univ_succ]

theorem continuous_partialWeight {n : ℕ} (i : Fin n) :
    Continuous (fun x : Fin n → ℝ => partialWeight x i) := by
  unfold partialWeight
  apply continuous_finsetSum
  intro j hj
  split_ifs <;> fun_prop

/-- Consecutive partial-sum intervals cover the whole range of a nonnegative
finite sequence, including all boundary cases and zero coordinates. -/
theorem exists_prefix_interval {n : ℕ} (x : Fin (n + 1) → ℝ)
    (hx : ∀ i, 0 ≤ x i) (s : ℝ) (hs₀ : 0 ≤ s) (hs₁ : s ≤ ∑ i, x i) :
    ∃ i, partialWeight x i ≤ s ∧ s ≤ partialWeight x i + x i := by
  induction n generalizing s with
  | zero =>
    refine ⟨0, ?_, ?_⟩
    · simpa using hs₀
    · simpa using hs₁
  | succ n ih =>
    by_cases h : s ≤ x 0
    · exact ⟨0, by simpa using hs₀, by simpa using h⟩
    · obtain ⟨i, hi₀, hi₁⟩ := ih (fun j => x j.succ) (fun j => hx j.succ)
        (s - x 0) (by linarith) (by rw [Fin.sum_univ_succ] at hs₁; linarith)
      refine ⟨i.succ, ?_, ?_⟩ <;> rw [prefix_succ] <;> linarith

/-- Splitting the weight of vertex `i` into two adjacent weights. -/
def split {n : ℕ} (i : Fin (n + 1)) (x : stdSimplex ℝ (Fin (n + 1)))
    (a : ℝ) (ha₀ : 0 ≤ a) (ha₁ : a ≤ x i) : stdSimplex ℝ (Fin (n + 2)) :=
  ⟨i.castSucc.insertNth a (Function.update (fun j => x j) i (x i - a)), by
    constructor
    · rw [Fin.forall_iff_succAbove i.castSucc]
      constructor
      · simpa using ha₀
      · intro j
        simp only [Fin.insertNth_apply_succAbove]
        by_cases h : j = i
        · subst j
          simp only [Function.update_self]
          exact sub_nonneg.mpr ha₁
        · simpa [Function.update_of_ne h] using x.zero_le j
    · rw [Fin.sum_univ_succAbove _ i.castSucc]
      simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]
      rw [Finset.sum_update_of_mem (Finset.mem_univ i)]
      have hs := stdSimplex.sum_eq_one x
      rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)] at hs
      simpa only [Finset.sdiff_singleton_eq_erase] using (by linarith :
        a + (x i - a + ∑ j ∈ Finset.univ.erase i, x j) = 1)⟩

@[simp] theorem split_at {n : ℕ} (i : Fin (n + 1))
    (x : stdSimplex ℝ (Fin (n + 1))) (a : ℝ) (ha₀ : 0 ≤ a) (ha₁ : a ≤ x i) :
    split i x a ha₀ ha₁ i.castSucc = a := by
  exact Fin.insertNth_apply_same (α := fun _ => ℝ) i.castSucc a
    (Function.update (fun j => x j) i (x i - a))

@[simp] theorem split_away {n : ℕ} (i : Fin (n + 1))
    (x : stdSimplex ℝ (Fin (n + 1))) (a : ℝ) (ha₀ : 0 ≤ a) (ha₁ : a ≤ x i)
    (j : Fin (n + 1)) :
    split i x a ha₀ ha₁ (i.castSucc.succAbove j) =
      Function.update (fun k => x k) i (x i - a) j := by
  exact Fin.insertNth_apply_succAbove (α := fun _ => ℝ) i.castSucc a
    (Function.update (fun k => x k) i (x i - a)) j

/-- Coalescing the two split vertices recovers the original simplex exactly. -/
theorem map_split {n : ℕ} (i : Fin (n + 1))
    (x : stdSimplex ℝ (Fin (n + 1))) (a : ℝ) (ha₀ : 0 ≤ a) (ha₁ : a ≤ x i) :
    stdSimplex.map i.predAbove (split i x a ha₀ ha₁) = x := by
  ext j
  change (FunOnFinite.linearMap ℝ ℝ i.predAbove (split i x a ha₀ ha₁)) j = x j
  rw [FunOnFinite.linearMap_apply_apply, Finset.sum_filter]
  rw [Fin.sum_univ_succAbove _ i.castSucc]
  simp only [Fin.predAbove_castSucc_self, split_at, Fin.predAbove_succAbove, split_away]
  by_cases h : i = j
  · subst j
    simp
  · simp [h, Ne.symm h]

/-- The closed prism cell in which the split occurs at vertex `i`. -/
def cell {n : ℕ} (i : Fin (n + 1)) : Set (unitInterval × stdSimplex ℝ (Fin (n + 1))) :=
  {p | partialWeight (fun j => p.2 j) i ≤ 1 - (p.1 : ℝ) ∧
    1 - (p.1 : ℝ) ≤ partialWeight (fun j => p.2 j) i + p.2 i}

theorem mem_some_cell {n : ℕ} (p : unitInterval × stdSimplex ℝ (Fin (n + 1))) :
    ∃ i, p ∈ cell i := by
  obtain ⟨i, hi⟩ := exists_prefix_interval (fun j => p.2 j) (stdSimplex.zero_le p.2)
    (1 - (p.1 : ℝ)) (sub_nonneg.mpr p.1.property.2)
    (by rw [stdSimplex.sum_eq_one p.2]; linarith [p.1.property.1])
  exact ⟨i, hi⟩

/-- Splitting weights varies continuously on its domain. -/
theorem continuous_split {n : ℕ} (i : Fin (n + 1)) {Z : Type*} [TopologicalSpace Z]
    (x : Z → stdSimplex ℝ (Fin (n + 1))) (a : Z → ℝ)
    (hx : Continuous x) (ha : Continuous a)
    (ha₀ : ∀ z, 0 ≤ a z) (ha₁ : ∀ z, a z ≤ x z i) :
    Continuous (fun z => split i (x z) (a z) (ha₀ z) (ha₁ z)) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  rw [Fin.forall_iff_succAbove i.castSucc]
  constructor
  · simpa only [Fin.insertNth_apply_same] using ha
  · intro j
    simp only [Fin.insertNth_apply_succAbove]
    by_cases h : j = i
    · subst j
      simp only [Function.update_self]
      exact (continuous_apply i |>.comp hx.subtype_val).sub ha
    · simp only [Function.update_of_ne h]
      exact continuous_apply j |>.comp hx.subtype_val

theorem isClosed_cell {n : ℕ} (i : Fin (n + 1)) : IsClosed (cell i) := by
  have hw : Continuous (fun p : unitInterval × stdSimplex ℝ (Fin (n + 1)) =>
      partialWeight (fun j => p.2 j) i) :=
    (continuous_partialWeight i).comp continuous_snd.subtype_val
  have ht : Continuous (fun p : unitInterval × stdSimplex ℝ (Fin (n + 1)) =>
      1 - (p.1 : ℝ)) := by fun_prop
  exact (isClosed_le hw ht).inter
    (isClosed_le ht (hw.add ((continuous_apply i).comp continuous_snd.subtype_val)))

/-- Barycentric coordinates in the simplex above a closed prism cell. -/
def cellSimplex {n : ℕ} (i : Fin (n + 1)) : C(cell i, stdSimplex ℝ (Fin (n + 2))) where
  toFun p := split i p.1.2 (1 - (p.1.1 : ℝ) - partialWeight (fun j => p.1.2 j) i)
    (by linarith [p.property.1]) (by linarith [p.property.2])
  continuous_toFun := continuous_split i _ _ (by fun_prop)
    ((continuous_const.sub (by fun_prop)).sub
      ((continuous_partialWeight i).comp (by fun_prop))) _ _

@[simp] theorem map_cellSimplex {n : ℕ} (i : Fin (n + 1)) (p : cell i) :
    stdSimplex.map i.predAbove (cellSimplex i p) = p.1.2 :=
  map_split i _ _ (by linarith [p.property.1]) (by linarith [p.property.2])

open CategoryTheory Simplicial Opposite MonoidalCategory

/-- The continuous map on one closed prism cell, obtained from the actual
characteristic map of its staircase simplex in the simplicial cylinder. -/
def cellRealizationMap {X Y : SSet.{u}} {f g : X ⟶ Y}
    (H : SSet.Homotopy f g) {n : ℕ} (x : X.obj (op ⦋n⦌)) (i : Fin (n + 1)) :
    C(cell i, |Y|) :=
  (realizationSimplex
    (H.h.app (op ⦋n + 1⦌)
      ((X.σ i x), SSet.stdSimplex.objMk₁ i.succ.castSucc))).comp (cellSimplex i)

end Sharpness.RealizationPrism
