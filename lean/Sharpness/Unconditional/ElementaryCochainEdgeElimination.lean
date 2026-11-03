import Sharpness.Unconditional.ElementaryCochainEdgeCorrection

/-! Finite leading-column elimination. A total cocycle supported strictly
after column p is a coboundary with primitive supported from column p. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
noncomputable section
universe u
namespace Sharpness.ElementaryCochainEdge
open CategoryTheory CategoryTheory.Limits HomologicalComplex
variable {R : Type u} [CommRing R]
    (K : HomologicalComplex₂ (ModuleCat.{u} R) (ComplexShape.up ℕ) (ComplexShape.up ℕ))

theorem tail_cycle_boundary_bounded (hK : PositiveHorizontalExact K) (n m p : ℕ)
    (hpm : p+m=n+1) (x : (K.total (ComplexShape.up ℕ)).X (n+1))
    (hx : Cycle (K.total (ComplexShape.up ℕ)) (n+1) x) (hs : SupportedFrom K x (p+1)) :
    ∃ y : (K.total (ComplexShape.up ℕ)).X n,
      (K.total (ComplexShape.up ℕ)).d n (n+1) y=x ∧ SupportedFrom K y p := by
  induction m generalizing p x with
  | zero =>
    have hp : n+2 ≤ p+1 := by omega
    have hz : x=0 := supportedFrom_eq_zero K (supportedFrom_mono K hs hp)
    exact ⟨0, by rw [map_zero, hz], supportedFrom_zero K n p⟩
  | succ m ih =>
    obtain ⟨y₀, hy₀, hd₀, hlead⟩ := leading_correction K hK p m n (by omega) x hx hs
    let z := x - (K.total (ComplexShape.up ℕ)).d n (n+1) y₀
    have hzc : Cycle (K.total (ComplexShape.up ℕ)) (n+1) z :=
      cycle_sub _ _ _ _ hx (cycle_boundary _ _ _ y₀)
    have hzs : SupportedFrom K z (p+2) := by
      apply supportedFrom_step K (p := p+1) (q := m) (by omega)
        (supportedFrom_sub K hs hd₀)
      change totalSummandProjectionAt K (p+1) m (n+1) (by omega)
        (x - (K.total (ComplexShape.up ℕ)).d n (n+1) y₀) = 0
      rw [map_sub, hlead, sub_self]
    obtain ⟨y, hy, hys⟩ := ih (p+1) (by omega) z hzc hzs
    refine ⟨y+y₀, ?_, supportedFrom_add K (supportedFrom_mono K hys (by omega)) hy₀⟩
    rw [map_add, hy]
    exact sub_add_cancel _ _

theorem tail_cycle_boundary (hK : PositiveHorizontalExact K) (n p : ℕ)
    (x : (K.total (ComplexShape.up ℕ)).X (n+1))
    (hx : Cycle (K.total (ComplexShape.up ℕ)) (n+1) x) (hs : SupportedFrom K x (p+1)) :
    ∃ y : (K.total (ComplexShape.up ℕ)).X n,
      (K.total (ComplexShape.up ℕ)).d n (n+1) y=x ∧ SupportedFrom K y p := by
  by_cases hp : p ≤ n+1
  · exact tail_cycle_boundary_bounded K hK n (n+1-p) p (by omega) x hx hs
  · have hz : x=0 := supportedFrom_eq_zero K (supportedFrom_mono K hs (by omega))
    exact ⟨0, by rw [map_zero, hz], supportedFrom_zero K n p⟩

end Sharpness.ElementaryCochainEdge
