import Sharpness.Unconditional.AtomicHigherLimits
import Sharpness.Unconditional.AtomicSylowOrbit
import Sharpness.HigherLimitsEquivalence

/-! The normal-p-subgroup atomic vanishing theorem transported to the
full p-orbit subcategory of a chosen Sylow subgroup. -/
set_option autoImplicit false
noncomputable section
universe u

namespace Sharpness.AtomicGroupOrbit
open CategoryTheory CategoryTheory.Limits Opposite
variable {p : ℕ} {G : Type u} [Group G]

theorem subgroup_eq_bot_of_hom_to_bot {P Q : Orbit (p := p) (G := G)}
    (f : P ⟶ Q) (hQ : Q.as.subgroup = ⊥) : P.as.subgroup = ⊥ := by
  obtain ⟨g, rfl⟩ := toOrbit.map_surjective f
  apply bot_unique
  intro x hx
  have hg := g.property x hx
  simp only [hQ, Subgroup.mem_bot] at hg
  rw [Subgroup.mem_bot]
  have he := congrArg (fun y => g.val * y * g.val⁻¹) hg
  simpa [mul_assoc] using he

variable (R : Type u) [CommRing R] [Fact p.Prime] [Finite (Sylow p G)]
    (T : Sylow p G) (N : Subgroup G) [N.Normal] (hN : IsPGroup p N)

include hN in
theorem atomic_higherLimits_zero_sylow (hne : N ≠ ⊥)
    (M : CoefficientCategory R (Below (p := p) (T : Subgroup G)))
    (supported : ∀ P : Below (p := p) (T : Subgroup G),
      P.obj.as.subgroup ≠ ⊥ → IsZero (M.obj (op P)))
    (n : ℕ) : IsZero (higherLimit M n) := by
  let e := sylowEquivalence T
  have hs : ∀ P : Orbit (p := p) (G := G), P.as.subgroup ≠ ⊥ →
      IsZero ((e.inverse.op ⋙ M).obj (op P)) := by
    intro P hP
    apply supported
    intro h
    exact hP (subgroup_eq_bot_of_hom_to_bot (e.counitIso.app P).inv h)
  exact IsZero.of_iso (atomic_higherLimits_zero R N hN hne (e.inverse.op ⋙ M) hs n)
    (higherLimitEquivalenceIso R e.symm M n)

end Sharpness.AtomicGroupOrbit
