import Sharpness.Unconditional.RealizationNerveHomotopyPrism
import Mathlib.Topology.LocallyFinite

/-! Compatibility of the geometric simplex-prism cells. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 300000
noncomputable section
universe u

namespace Sharpness.RealizationPrism
open CategoryTheory Simplicial Opposite MonoidalCategory
open scoped BigOperators

theorem map_succAbove_coe {n : ℕ} (i : Fin (n + 1))
    (x : stdSimplex ℝ (Fin n)) :
    (⇑(stdSimplex.map i.succAbove x)) =
      Fin.insertNth (α := fun _ => ℝ) i 0 (fun j => x j) := by
  symm
  apply (Fin.insertNth_eq_iff).mpr
  constructor
  · change 0 = (FunOnFinite.linearMap ℝ ℝ i.succAbove x) i
    simp [FunOnFinite.linearMap_apply_apply, Fin.succAbove_ne]
  · funext j
    change x j = (FunOnFinite.linearMap ℝ ℝ i.succAbove x) (i.succAbove j)
    simp [FunOnFinite.linearMap_apply_apply, Finset.sum_filter]

theorem split_zero {n : ℕ} (i : Fin (n + 1))
    (x : stdSimplex ℝ (Fin (n + 1))) :
    split i x 0 (by rfl) (stdSimplex.zero_le x i) = stdSimplex.map i.castSucc.succAbove x := by
  apply stdSimplex.ext
  rw [map_succAbove_coe]
  change Fin.insertNth (α := fun _ => ℝ) i.castSucc 0
    (Function.update (fun j => x j) i (x i - 0)) = _
  simp

theorem split_congr {n : ℕ} (i : Fin (n + 1)) (x : stdSimplex ℝ (Fin (n + 1)))
    {a b : ℝ} {ha₀ : 0 ≤ a} {ha₁ : a ≤ x i} {hb₀ : 0 ≤ b} {hb₁ : b ≤ x i}
    (h : a = b) : split i x a ha₀ ha₁ = split i x b hb₀ hb₁ := by
  subst b
  rfl

theorem adjacent_succAbove_eq {n : ℕ} (i j : Fin (n + 1)) (h : j ≠ i) :
    i.castSucc.succAbove j = i.succ.succAbove j := by
  rcases lt_or_gt_of_ne h with hj | hj
  · rw [Fin.succAbove_castSucc_of_lt _ _ hj, Fin.succAbove_succ_of_le _ _ (le_of_lt hj)]
  · rw [Fin.succAbove_castSucc_of_le _ _ (le_of_lt hj), Fin.succAbove_succ_of_lt _ _ hj]

theorem split_full {n : ℕ} (i : Fin (n + 1))
    (x : stdSimplex ℝ (Fin (n + 1))) :
    split i x (x i) (stdSimplex.zero_le x i) (by rfl) = stdSimplex.map i.succ.succAbove x := by
  apply stdSimplex.ext
  rw [map_succAbove_coe]
  funext j
  refine Fin.succAboveCases i.castSucc ?_ (fun k => ?_) j
  · change split i x (x i) _ _ i.castSucc =
      Fin.insertNth (α := fun _ => ℝ) i.succ 0 (fun j => x j) i.castSucc
    rw [split_at, ← Fin.succAbove_succ_self i, Fin.insertNth_apply_succAbove]
  · change split i x (x i) _ _ (i.castSucc.succAbove k) =
      Fin.insertNth (α := fun _ => ℝ) i.succ 0 (fun j => x j) (i.castSucc.succAbove k)
    rw [split_away]
    by_cases h : k = i
    · subst k
      simp
    · rw [Function.update_of_ne h, adjacent_succAbove_eq i k h, Fin.insertNth_apply_succAbove]

/-- At the common face, consecutive staircase simplices have exactly the same
realized value. This is the geometric content of the middle prism identity. -/
theorem staircase_face_agreement {X Y : SSet.{u}} {f g : X ⟶ Y}
    (H : SimplicialObject.Homotopy f g) {n : ℕ}
    (x : X.obj (op ⦋n + 1⦌)) (i : Fin (n + 1))
    (z : stdSimplex ℝ (Fin (n + 2))) :
    realizationSimplex (H.h i.castSucc x)
        (stdSimplex.map i.castSucc.succ.succAbove z) =
      realizationSimplex (H.h i.succ x)
        (stdSimplex.map i.castSucc.succ.succAbove z) := by
  have h := ConcreteCategory.congr_hom (H.h_succ_comp_δ_castSucc_succ i) x
  have h' := congrArg (fun y => realizationSimplex y z) h
  simp only [types_comp_apply, SimplicialObject.δ, realizationSimplex_naturality] at h'
  exact h'.symm

theorem partialWeight_succ_eq {n : ℕ} (x : Fin (n + 2) → ℝ) (i : Fin (n + 1)) :
    partialWeight x i.succ = partialWeight x i.castSucc + x i.castSucc := by
  have h : x i.castSucc = ∑ j : Fin (n + 2), if j = i.castSucc then x j else 0 := by simp
  unfold partialWeight
  rw [h, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  by_cases hlt : j < i.castSucc
  · have hlt' : j < i.succ := hlt.trans Fin.castSucc_lt_succ
    have hne : j ≠ i.castSucc := ne_of_lt hlt
    simp [hlt, hlt', hne]
  · by_cases he : j = i.castSucc
    · subst j
      simp
    · have hge : ¬j < i.succ := not_lt.mpr
        (Fin.castSucc_lt_iff_succ_le.mp (lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm he)))
      simp [hlt, he, hge]

theorem partialWeight_mono {n : ℕ} (x : stdSimplex ℝ (Fin n)) :
    Monotone (partialWeight (fun j => x j)) := by
  intro i j hij
  apply Finset.sum_le_sum
  intro k hk
  by_cases hki : k < i
  · simp [hki, lt_of_lt_of_le hki hij]
  · by_cases hkj : k < j
    · simp [hki, hkj, stdSimplex.zero_le]
    · simp [hki, hkj]

theorem upperWeight_mono {n : ℕ} (x : stdSimplex ℝ (Fin n)) :
    Monotone (fun i => partialWeight (fun j => x j) i + x i) := by
  have hu (i : Fin n) : partialWeight (fun j => x j) i + x i =
      ∑ j, if j ≤ i then x j else 0 := by
    have h : x i = ∑ j : Fin n, if j = i then x j else 0 := by simp
    unfold partialWeight
    rw [h, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    rcases lt_trichotomy j i with hlt | he | hgt
    · simp [hlt, le_of_lt hlt, ne_of_lt hlt]
    · subst j
      simp
    · simp [not_lt.mpr (le_of_lt hgt), not_le.mpr hgt, ne_of_gt hgt]
  intro i j hij
  change partialWeight (fun k => x k) i + x i ≤ partialWeight (fun k => x k) j + x j
  rw [hu, hu]
  apply Finset.sum_le_sum
  intro k hk
  by_cases hki : k ≤ i
  · simp [hki, hki.trans hij]
  · by_cases hkj : k ≤ j
    · simp [hki, hkj, stdSimplex.zero_le]
    · simp [hki, hkj]

theorem mem_cell_between {n : ℕ} (p : unitInterval × stdSimplex ℝ (Fin (n + 1)))
    {i j k : Fin (n + 1)} (hi : p ∈ cell i) (hj : p ∈ cell j)
    (hik : i ≤ k) (hkj : k ≤ j) : p ∈ cell k :=
  ⟨(partialWeight_mono p.2 hkj).trans hj.1,
    hi.2.trans (upperWeight_mono p.2 hik)⟩

theorem cellRealizationMap_adjacent {X Y : SSet.{u}} {f g : X ⟶ Y}
    (H : SSet.Homotopy f g) {n : ℕ} (x : X.obj (op ⦋n + 1⦌)) (i : Fin (n + 1))
    (p : unitInterval × stdSimplex ℝ (Fin (n + 2)))
    (hi : p ∈ cell i.castSucc) (hj : p ∈ cell i.succ) :
    cellRealizationMap H x i.castSucc ⟨p, hi⟩ =
      cellRealizationMap H x i.succ ⟨p, hj⟩ := by
  have hsum := partialWeight_succ_eq (fun j => p.2 j) i
  have ha : 1 - (p.1 : ℝ) - partialWeight (fun j => p.2 j) i.castSucc = p.2 i.castSucc := by
    have hi' := hi.2
    have hj' := hj.1
    linarith
  have hb : 1 - (p.1 : ℝ) - partialWeight (fun j => p.2 j) i.succ = 0 := by
    have hi' := hi.2
    have hj' := hj.1
    linarith
  have hl : cellSimplex i.castSucc ⟨p, hi⟩ =
      stdSimplex.map i.castSucc.succ.succAbove p.2 := by
    dsimp only [cellSimplex, ContinuousMap.coe_mk]
    exact (split_congr i.castSucc p.2 ha).trans (split_full i.castSucc p.2)
  have hr : cellSimplex i.succ ⟨p, hj⟩ =
      stdSimplex.map i.succ.castSucc.succAbove p.2 := by
    dsimp only [cellSimplex, ContinuousMap.coe_mk]
    exact (split_congr i.succ p.2 hb).trans (split_zero i.succ p.2)
  change realizationSimplex _ (cellSimplex i.castSucc ⟨p, hi⟩) =
    realizationSimplex _ (cellSimplex i.succ ⟨p, hj⟩)
  rw [hl, hr]
  exact staircase_face_agreement H.toSimplicialObjectHomotopy x i p.2

/-- All of the closed prism-cell maps agree wherever their domains overlap. -/
theorem cellRealizationMap_agree {X Y : SSet.{u}} {f g : X ⟶ Y}
    (H : SSet.Homotopy f g) {n : ℕ} (x : X.obj (op ⦋n⦌))
    (i j : Fin (n + 1)) (p : unitInterval × stdSimplex ℝ (Fin (n + 1)))
    (hi : p ∈ cell i) (hj : p ∈ cell j) :
    cellRealizationMap H x i ⟨p, hi⟩ = cellRealizationMap H x j ⟨p, hj⟩ := by
  cases n with
  | zero =>
    have h : i = j := by apply Fin.ext; omega
    subst j
    rfl
  | succ n =>
    have hle : ∀ j : Fin (n + 2), ∀ i : Fin (n + 2), i ≤ j →
        ∀ (hi : p ∈ cell i) (hj : p ∈ cell j),
        cellRealizationMap H x i ⟨p, hi⟩ = cellRealizationMap H x j ⟨p, hj⟩ := by
      intro j
      induction j using Fin.induction with
      | zero =>
        intro i hi hci hcj
        have he : i = 0 := Fin.le_zero_iff.mp hi
        subst i
        rfl
      | succ k ih =>
        intro i hik hci hcj
        by_cases he : i = k.succ
        · subst i
          rfl
        · have hik' : i ≤ k.castSucc :=
            Fin.le_castSucc_iff.mpr (lt_of_le_of_ne hik he)
          have hck := mem_cell_between p hci hcj hik' (le_of_lt Fin.castSucc_lt_succ)
          exact (ih i hik' hci hck).trans (cellRealizationMap_adjacent H x k p hck hcj)
    rcases le_total i j with hij | hji
    · exact hle j i hij hi hj
    · exact (hle i j hji hj hi).symm

theorem iUnion_cell (n : ℕ) : (⋃ i : Fin (n + 1), cell i) = Set.univ := by
  ext p
  simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
  exact mem_some_cell p

/-- The finite closed-cell prism maps glue to a continuous map on the whole
topological simplex times the compact unit interval. -/
def simplexRealizationPrism {X Y : SSet.{u}} {f g : X ⟶ Y}
    (H : SSet.Homotopy f g) {n : ℕ} (x : X.obj (op ⦋n⦌)) :
    C(unitInterval × stdSimplex ℝ (Fin (n + 1)), |Y|) where
  toFun := Set.liftCover cell (fun i => cellRealizationMap H x i)
    (cellRealizationMap_agree H x) (iUnion_cell n)
  continuous_toFun := by
    apply (locallyFinite_of_finite cell).continuous (iUnion_cell n) isClosed_cell
    intro i
    apply continuousOn_iff_continuous_restrict.mpr
    convert (cellRealizationMap H x i).continuous using 1
    funext p
    exact Set.liftCover_coe p

theorem simplexRealizationPrism_on_cell {X Y : SSet.{u}} {f g : X ⟶ Y}
    (H : SSet.Homotopy f g) {n : ℕ} (x : X.obj (op ⦋n⦌))
    (i : Fin (n + 1)) (p : cell i) :
    simplexRealizationPrism H x p = cellRealizationMap H x i p :=
  Set.liftCover_coe (f := fun i => cellRealizationMap H x i)
    (hf := cellRealizationMap_agree H x) (hS := iUnion_cell n) p

theorem partialWeight_last_add {n : ℕ} (x : stdSimplex ℝ (Fin (n + 1))) :
    partialWeight (fun j => x j) (Fin.last n) + x (Fin.last n) = 1 := by
  calc
    _ = (∑ j : Fin n, x j.castSucc) + x (Fin.last n) := by
      congr 1
      unfold partialWeight
      rw [Fin.sum_univ_castSucc]
      simp
    _ = 1 := by rw [← Fin.sum_univ_castSucc]; exact stdSimplex.sum_eq_one x

theorem staircase_last_face {X Y : SSet.{u}} {f g : X ⟶ Y}
    (H : SimplicialObject.Homotopy f g) {n : ℕ} (x : X.obj (op ⦋n⦌))
    (z : stdSimplex ℝ (Fin (n + 1))) :
    realizationSimplex (H.h (Fin.last n) x)
        (stdSimplex.map (Fin.last (n + 1)).succAbove z) = realizationSimplex (f.app _ x) z := by
  have h := ConcreteCategory.congr_hom (H.h_last_comp_δ_last n) x
  have h' := congrArg (fun y => realizationSimplex y z) h
  simp only [types_comp_apply, SimplicialObject.δ, realizationSimplex_naturality] at h'
  exact h'

theorem staircase_zero_face {X Y : SSet.{u}} {f g : X ⟶ Y}
    (H : SimplicialObject.Homotopy f g) {n : ℕ} (x : X.obj (op ⦋n⦌))
    (z : stdSimplex ℝ (Fin (n + 1))) :
    realizationSimplex (H.h 0 x) (stdSimplex.map (0 : Fin (n + 2)).succAbove z) =
      realizationSimplex (g.app _ x) z := by
  have h := ConcreteCategory.congr_hom (H.h_zero_comp_δ_zero n) x
  have h' := congrArg (fun y => realizationSimplex y z) h
  simp only [types_comp_apply, SimplicialObject.δ, realizationSimplex_naturality] at h'
  exact h'

theorem simplexRealizationPrism_zero {X Y : SSet.{u}} {f g : X ⟶ Y}
    (H : SSet.Homotopy f g) {n : ℕ} (x : X.obj (op ⦋n⦌))
    (z : stdSimplex ℝ (Fin (n + 1))) :
    simplexRealizationPrism H x (0, z) = realizationSimplex (f.app _ x) z := by
  have hs := partialWeight_last_add z
  have hp : (0, z) ∈ cell (Fin.last n) := by
    constructor
    · change partialWeight (fun j => z j) (Fin.last n) ≤ 1 - 0
      linarith [stdSimplex.zero_le z (Fin.last n)]
    · change 1 - 0 ≤ partialWeight (fun j => z j) (Fin.last n) + z (Fin.last n)
      linarith
  have ha : 1 - ((0 : unitInterval) : ℝ) - partialWeight (fun j => z j) (Fin.last n) =
      z (Fin.last n) := by change 1 - 0 - _ = _; linarith
  have hc : cellSimplex (Fin.last n) ⟨(0, z), hp⟩ =
      stdSimplex.map (Fin.last (n + 1)).succAbove z := by
    dsimp only [cellSimplex, ContinuousMap.coe_mk]
    exact (split_congr (Fin.last n) z ha).trans (split_full (Fin.last n) z)
  have he := simplexRealizationPrism_on_cell H x (Fin.last n) ⟨(0, z), hp⟩
  rw [he]
  change realizationSimplex _ (cellSimplex (Fin.last n) ⟨(0, z), hp⟩) = _
  rw [hc]
  exact staircase_last_face H.toSimplicialObjectHomotopy x z

theorem simplexRealizationPrism_one {X Y : SSet.{u}} {f g : X ⟶ Y}
    (H : SSet.Homotopy f g) {n : ℕ} (x : X.obj (op ⦋n⦌))
    (z : stdSimplex ℝ (Fin (n + 1))) :
    simplexRealizationPrism H x (1, z) = realizationSimplex (g.app _ x) z := by
  have hp : (1, z) ∈ cell (0 : Fin (n + 1)) := by
    constructor <;> simp [stdSimplex.zero_le]
  have ha : 1 - ((1 : unitInterval) : ℝ) - partialWeight (fun j => z j) 0 = 0 := by simp
  have hc : cellSimplex (0 : Fin (n + 1)) ⟨(1, z), hp⟩ =
      stdSimplex.map (0 : Fin (n + 2)).succAbove z := by
    dsimp only [cellSimplex, ContinuousMap.coe_mk]
    exact (split_congr 0 z ha).trans (split_zero 0 z)
  have he := simplexRealizationPrism_on_cell H x 0 ⟨(1, z), hp⟩
  rw [he]
  change realizationSimplex _ (cellSimplex (0 : Fin (n + 1)) ⟨(1, z), hp⟩) = _
  rw [hc]
  exact staircase_zero_face H.toSimplicialObjectHomotopy x z

/-- An actual continuous homotopy on each characteristic simplex. -/
def simplexRealizationHomotopy {X Y : SSet.{u}} {f g : X ⟶ Y}
    (H : SSet.Homotopy f g) {n : ℕ} (x : X.obj (op ⦋n⦌)) :
    ContinuousMap.Homotopy ((SSet.toTop.map f).hom.comp (realizationSimplex x))
      ((SSet.toTop.map g).hom.comp (realizationSimplex x)) where
  toContinuousMap := simplexRealizationPrism H x
  map_zero_left z := (simplexRealizationPrism_zero H x z).trans (realizationSimplex_map f x z)
  map_one_left z := (simplexRealizationPrism_one H x z).trans (realizationSimplex_map g x z)

end Sharpness.RealizationPrism
