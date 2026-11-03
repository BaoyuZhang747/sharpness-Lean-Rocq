import Sharpness.Unconditional.ElementaryCochainEdgeInjective

/-! Lift a zero-column horizontal cohomology cycle to a native total cocycle.
The remaining obstruction is removed without changing column zero. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
noncomputable section
universe u
namespace Sharpness.ElementaryCochainEdge
open CategoryTheory CategoryTheory.Limits HomologicalComplex
variable {R : Type u} [CommRing R]
    (K : HomologicalComplex₂ (ModuleCat.{u} R) (ComplexShape.up ℕ) (ComplexShape.up ℕ))

theorem kernel_cycle_seed (n : ℕ) (x : (K.X 0).X n) (hx : Cycle (K.X 0) n x)
    (hh : homologyMap (K.d 0 1) n (cycleClass (K.X 0) n x hx)=0) :
    ∃ z : (K.total (ComplexShape.up ℕ)).X n,
      totalSummandProjectionAt K 0 n n (by omega) z=x ∧
      SupportedFrom K ((K.total (ComplexShape.up ℕ)).d n (n+1) z) 2 := by
  rw [cycleClass_map] at hh
  cases n with
  | zero =>
    have hd := (cycleClass_eq_zero_iff_zero (K.X 1) _ _).mp hh
    refine ⟨K.ιTotal (ComplexShape.up ℕ) 0 0 0 rfl x, inclusion_projection K 0 0 0 rfl x, ?_⟩
    rw [inclusion_differential_of_cycle K 0 0 0 rfl x (hx 1), hd, map_zero]
    exact supportedFrom_zero K 1 2
  | succ n =>
    obtain ⟨b, hb⟩ := (cycleClass_eq_zero_iff (K.X 1) (n+1) _ _).mp hh
    change (K.X 1).d n (n+1) b = (K.d 0 1).f (n+1) x at hb
    let z := K.ιTotal (ComplexShape.up ℕ) 0 (n+1) (n+1) (by simp) x +
      K.ιTotal (ComplexShape.up ℕ) 1 n (n+1) (by change 1+n=n+1; omega) b
    have hz₀ : totalSummandProjectionAt K 0 (n+1) (n+1) (by omega) z=x := by
      dsimp only [z]
      rw [map_add, inclusion_projection,
        inclusion_projection_other K 1 n (n+1) (by omega) b 0 (n+1) (by omega) (by decide), add_zero]
    have hz₁ : totalSummandProjectionAt K 1 n (n+1) (by omega) z=b := by
      dsimp only [z]
      rw [map_add,
        inclusion_projection_other K 0 (n+1) (n+1) (by omega) x 1 n (by omega) (by decide),
        inclusion_projection, zero_add]
    refine ⟨z, hz₀, ?_⟩
    intro p q hpq hp
    have hp' : p=0 ∨ p=1 := by omega
    rcases hp' with rfl | rfl
    · have hq : q=n+2 := by omega
      subst q
      rw [differential_component_zero_column, hz₀, hx (n+2)]
    · have hq : q=n+1 := by omega
      subst q
      rw [differential_component K 0 n (n+1) (by omega), hz₀, hz₁, hb]
      simp

theorem kernel_cycle_lift (hK : PositiveHorizontalExact K) (n : ℕ)
    (x : (K.X 0).X n) (hx : Cycle (K.X 0) n x)
    (hh : homologyMap (K.d 0 1) n (cycleClass (K.X 0) n x hx)=0) :
    ∃ z : (K.total (ComplexShape.up ℕ)).X n,
      Cycle (K.total (ComplexShape.up ℕ)) n z ∧
      totalSummandProjectionAt K 0 n n (by omega) z=x := by
  obtain ⟨z, hz₀, hzs⟩ := kernel_cycle_seed K n x hx hh
  obtain ⟨y, hy, hys⟩ := tail_cycle_boundary K hK n 1
    ((K.total (ComplexShape.up ℕ)).d n (n+1) z) (cycle_boundary _ _ _ z) hzs
  refine ⟨z-y, ?_, ?_⟩
  · apply (cycle_iff _ _ _).mpr
    rw [map_sub, hy, sub_self]
  · rw [map_sub, hz₀, hys 0 n (by omega) (by decide), sub_zero]

theorem edgeMap_surjective (hK : PositiveHorizontalExact K) (n : ℕ) :
    Function.Surjective (edgeMap K n) := by
  intro a
  obtain ⟨x, hx, hclass⟩ := cycleClass_surjective (K.X 0) n a.val
  have hh : homologyMap (K.d 0 1) n (cycleClass (K.X 0) n x hx)=0 := by
    rw [hclass]
    exact a.property
  obtain ⟨z, hz, hz₀⟩ := kernel_cycle_lift K hK n x hx hh
  refine ⟨cycleClass (K.total (ComplexShape.up ℕ)) n z hz, ?_⟩
  apply Subtype.ext
  rw [edgeMap_cycleClass_val]
  simpa only [hz₀] using hclass

end Sharpness.ElementaryCochainEdge
