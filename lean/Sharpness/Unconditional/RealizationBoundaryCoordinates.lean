import Mathlib.AlgebraicTopology.SimplicialSet.TopAdj
import Mathlib.Topology.Order.Lattice
import Mathlib.Tactic

/-! Literal coordinate boundaries and radial neighborhoods of topological
standard simplices. The realization of the simplicial boundary is a separate
comparison, not assumed in these geometric lemmas. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Sharpness.RealizationBoundary
open scoped BigOperators

abbrev Simplex (n : ℕ) := _root_.stdSimplex ℝ (Fin (n + 1))

def boundary (n : ℕ) : Set (Simplex n) := {t | ∃ i, t i = 0}

def minimumCoordinate {n : ℕ} (t : Simplex n) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty (fun i => t i)

theorem minimumCoordinate_nonneg {n : ℕ} (t : Simplex n) : 0 ≤ minimumCoordinate t :=
  Finset.le_inf' _ _ (fun i _ => _root_.stdSimplex.zero_le t i)

theorem minimumCoordinate_le {n : ℕ} (t : Simplex n) (i : Fin (n + 1)) :
    minimumCoordinate t ≤ t i := Finset.inf'_le _ (Finset.mem_univ i)

theorem exists_minimumCoordinate {n : ℕ} (t : Simplex n) :
    ∃ i, minimumCoordinate t = t i := by
  obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty (fun i => t i)
  exact ⟨i, hi⟩

theorem continuous_minimumCoordinate (n : ℕ) :
    Continuous (minimumCoordinate (n := n)) :=
  Continuous.finset_inf'_apply Finset.univ_nonempty
    (fun i _ => (continuous_apply i).comp continuous_subtype_val)

theorem cardinal_mul_minimumCoordinate_le_one {n : ℕ} (t : Simplex n) :
    (n + 1 : ℝ) * minimumCoordinate t ≤ 1 := by
  have h := Finset.sum_le_sum (s := Finset.univ)
    (fun (i : Fin (n + 1)) _ => minimumCoordinate_le t i)
  simpa [Finset.sum_const, nsmul_eq_mul, _root_.stdSimplex.sum_eq_one] using h

theorem mem_boundary_iff_minimumCoordinate_eq_zero {n : ℕ} (t : Simplex n) :
    t ∈ boundary n ↔ minimumCoordinate t = 0 := by
  constructor
  · rintro ⟨i, hi⟩
    exact le_antisymm (hi ▸ minimumCoordinate_le t i) (minimumCoordinate_nonneg t)
  · intro h
    obtain ⟨i, hi⟩ := exists_minimumCoordinate t
    exact ⟨i, hi.symm.trans h⟩

theorem isClosed_boundary (n : ℕ) : IsClosed (boundary n) := by
  have h : boundary n = {t | minimumCoordinate t = 0} :=
    Set.ext (mem_boundary_iff_minimumCoordinate_eq_zero)
  rw [h]
  exact isClosed_eq (continuous_minimumCoordinate n) continuous_const

/-- The open punctured-simplex neighborhood of the coordinate boundary. -/
def radialNeighborhood (n : ℕ) : Set (Simplex n) :=
  {t | (n + 1 : ℝ) * minimumCoordinate t < 1}

theorem isOpen_radialNeighborhood (n : ℕ) : IsOpen (radialNeighborhood n) :=
  isOpen_lt (continuous_const.mul (continuous_minimumCoordinate n)) continuous_const

theorem boundary_subset_radialNeighborhood (n : ℕ) : boundary n ⊆ radialNeighborhood n := by
  intro t ht
  have h := (mem_boundary_iff_minimumCoordinate_eq_zero t).mp ht
  change (n + 1 : ℝ) * minimumCoordinate t < 1
  simp [h]

theorem radial_denominator_pos {n : ℕ} (t : radialNeighborhood n) :
    0 < 1 - (n + 1 : ℝ) * minimumCoordinate t.val := sub_pos.mpr t.property

/-- The actual radial projection from the center to the coordinate boundary. -/
def radialProjection {n : ℕ} (t : radialNeighborhood n) : Simplex n :=
  ⟨fun i => (t.val i - minimumCoordinate t.val) /
      (1 - (n + 1 : ℝ) * minimumCoordinate t.val),
    ⟨fun i => div_nonneg (sub_nonneg.mpr (minimumCoordinate_le t.val i))
        (radial_denominator_pos t).le, by
      rw [← Finset.sum_div, Finset.sum_sub_distrib]
      simp only [_root_.stdSimplex.sum_eq_one, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
      exact div_self (ne_of_gt (radial_denominator_pos t))⟩⟩

theorem radialProjection_mem_boundary {n : ℕ} (t : radialNeighborhood n) :
    radialProjection t ∈ boundary n := by
  obtain ⟨i, hi⟩ := exists_minimumCoordinate t.val
  refine ⟨i, ?_⟩
  change (t.val i - minimumCoordinate t.val) / _ = 0
  rw [hi, sub_self, zero_div]

theorem continuous_radialProjection (n : ℕ) :
    Continuous (radialProjection (n := n)) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro i
  exact ((((continuous_apply i).comp continuous_subtype_val).comp continuous_subtype_val).sub
    ((continuous_minimumCoordinate n).comp continuous_subtype_val)).div
    (continuous_const.sub (continuous_const.mul
      ((continuous_minimumCoordinate n).comp continuous_subtype_val)))
    (fun t => ne_of_gt (radial_denominator_pos t))

theorem radialProjection_fixed {n : ℕ} (t : boundary n) :
    radialProjection (⟨t.val, boundary_subset_radialNeighborhood n t.property⟩) = t.val := by
  apply Subtype.ext
  funext i
  have h := (mem_boundary_iff_minimumCoordinate_eq_zero t.val).mp t.property
  change (t.val i - minimumCoordinate t.val) / _ = t.val i
  simp [h]

end Sharpness.RealizationBoundary
