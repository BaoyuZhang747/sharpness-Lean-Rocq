import Sharpness.Unconditional.RealizationBoundaryCoordinates

/-! Actual coordinate faces of standard topological simplices. Every injective
vertex map identifies a smaller simplex homeomorphically with its coordinate
face. No realization-embedding assertion is assumed. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Sharpness.RealizationBoundary
open scoped BigOperators

theorem simplex_map_injective_apply {n m : ℕ}
    (f : Fin (n + 1) → Fin (m + 1)) (hf : Function.Injective f)
    (t : Simplex n) (i : Fin (n + 1)) :
    _root_.stdSimplex.map f t (f i) = t i := by
  classical
  change FunOnFinite.linearMap ℝ ℝ f t (f i) = _
  rw [FunOnFinite.linearMap_apply_apply]
  have h : Finset.univ.filter (fun j => f j = f i) = {i} := by
    ext j
    simp [hf.eq_iff]
  rw [h]
  simp

theorem simplex_map_zero_of_not_range {n m : ℕ}
    (f : Fin (n + 1) → Fin (m + 1)) (t : Simplex n)
    (j : Fin (m + 1)) (hj : j ∉ Set.range f) :
    _root_.stdSimplex.map f t j = 0 := by
  classical
  change FunOnFinite.linearMap ℝ ℝ f t j = _
  rw [FunOnFinite.linearMap_apply_apply]
  have h : Finset.univ.filter (fun i => f i = j) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro i hi
    exact hj ⟨i, (Finset.mem_filter.mp hi).2⟩
  rw [h, Finset.sum_empty]

def coordinateFace {n m : ℕ} (f : Fin (n + 1) → Fin (m + 1)) : Set (Simplex m) :=
  {t | ∀ j, j ∉ Set.range f → t j = 0}

theorem isClosed_coordinateFace {n m : ℕ} (f : Fin (n + 1) → Fin (m + 1)) :
    IsClosed (coordinateFace f) := by
  have h : coordinateFace f = ⋂ j, ⋂ (_ : j ∉ Set.range f), {t | t j = 0} := by
    ext t
    simp [coordinateFace]
  rw [h]
  apply isClosed_iInter
  intro j
  apply isClosed_iInter
  intro _
  exact isClosed_eq ((continuous_apply j).comp continuous_subtype_val) continuous_const

def coordinateFacePull {n m : ℕ} (f : Fin (n + 1) → Fin (m + 1))
    (hf : Function.Injective f) (t : coordinateFace f) : Simplex n :=
  ⟨fun i => t.val (f i), ⟨fun i => _root_.stdSimplex.zero_le t.val (f i), by
    classical
    rw [← Finset.sum_image (fun a _ b _ hab => hf hab)]
    calc
      _ = ∑ j : Fin (m + 1), t.val j := by
        apply Finset.sum_subset (Finset.subset_univ _)
        intro j _ hj
        exact t.property j (by simpa using hj)
      _ = 1 := _root_.stdSimplex.sum_eq_one t.val⟩⟩

def coordinateFaceHomeo {n m : ℕ} (f : Fin (n + 1) → Fin (m + 1))
    (hf : Function.Injective f) : Simplex n ≃ₜ coordinateFace f where
  toFun t := ⟨_root_.stdSimplex.map f t, simplex_map_zero_of_not_range f t⟩
  invFun := coordinateFacePull f hf
  left_inv t := by
    apply Subtype.ext
    funext i
    exact simplex_map_injective_apply f hf t i
  right_inv t := by
    apply Subtype.ext
    apply Subtype.ext
    funext j
    change _root_.stdSimplex.map f (coordinateFacePull f hf t) j = t.val j
    by_cases hj : j ∈ Set.range f
    · obtain ⟨i, rfl⟩ := hj
      rw [simplex_map_injective_apply f hf]
      rfl
    · rw [simplex_map_zero_of_not_range f _ j hj, t.property j hj]
  continuous_toFun := (_root_.stdSimplex.continuous_map f).subtype_mk _
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro i
    exact ((continuous_apply (f i)).comp continuous_subtype_val).comp continuous_subtype_val

end Sharpness.RealizationBoundary
