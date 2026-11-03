import Sharpness.Unconditional.ElementaryCochainEdgeElimination
import Sharpness.Unconditional.ElementaryCochainEdgeCycleCriterionMap

/-! A total cocycle whose zero-column class vanishes is a coboundary. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
noncomputable section
universe u
namespace Sharpness.ElementaryCochainEdge
open CategoryTheory CategoryTheory.Limits HomologicalComplex
variable {R : Type u} [CommRing R]
    (K : HomologicalComplex₂ (ModuleCat.{u} R) (ComplexShape.up ℕ) (ComplexShape.up ℕ))

theorem zero_edge_cycle_boundary (hK : PositiveHorizontalExact K) (n : ℕ)
    (x : (K.total (ComplexShape.up ℕ)).X n) (hx : Cycle (K.total (ComplexShape.up ℕ)) n x)
    (hz : cycleClass (K.X 0) n (totalSummandProjectionAt K 0 n n (by omega) x)
      (leading_cycle K 0 n n (by omega) x hx (by intro i j hij hi; omega)) = 0) :
    ∃ y : (K.total (ComplexShape.up ℕ)).X (n-1),
      (K.total (ComplexShape.up ℕ)).d (n-1) n y = x := by
  cases n with
  | zero =>
    have hzero := (cycleClass_eq_zero_iff_zero (K.X 0) _ _).mp hz
    have hs : SupportedFrom K x 1 :=
      supportedFrom_step K (p := 0) (q := 0) rfl (by intro i j hij hi; omega) hzero
    have hx0 : x=0 := supportedFrom_eq_zero K hs
    exact ⟨0, by rw [map_zero, hx0]⟩
  | succ n =>
    obtain ⟨b, hb⟩ := (cycleClass_eq_zero_iff (K.X 0) (n+1) _ _).mp hz
    change (K.X 0).d n (n+1) b = totalSummandProjectionAt K 0 (n+1) (n+1) (by omega) x at hb
    let y₀ := K.ιTotal (ComplexShape.up ℕ) 0 n n (by simp) b
    let z := x - (K.total (ComplexShape.up ℕ)).d n (n+1) y₀
    have hzc : Cycle (K.total (ComplexShape.up ℕ)) (n+1) z :=
      cycle_sub _ _ _ _ hx (cycle_boundary _ _ _ y₀)
    have hzs : SupportedFrom K z 1 := by
      apply supportedFrom_step K (p := 0) (q := n+1) (by omega)
        (by intro i j hij hi; omega)
      dsimp only [z, y₀]
      rw [map_sub, differential_component_zero_column, inclusion_projection, hb, sub_self]
    obtain ⟨y, hy, _⟩ := tail_cycle_boundary K hK n 0 z hzc hzs
    refine ⟨y+y₀, ?_⟩
    change (K.total (ComplexShape.up ℕ)).d n (n+1) (y+y₀)=x
    rw [map_add, hy]
    exact sub_add_cancel _ _

theorem edgeMap_injective (hK : PositiveHorizontalExact K) (n : ℕ) :
    Function.Injective (edgeMap K n) := by
  rw [injective_iff_map_eq_zero (edgeMap K n).hom]
  intro z hz
  obtain ⟨x, hx, rfl⟩ := cycleClass_surjective (K.total (ComplexShape.up ℕ)) n z
  have hh := congrArg Subtype.val hz
  rw [edgeMap_cycleClass_val] at hh
  apply (cycleClass_eq_zero_iff _ _ _ _).mpr
  exact zero_edge_cycle_boundary K hK n x hx hh

end Sharpness.ElementaryCochainEdge
