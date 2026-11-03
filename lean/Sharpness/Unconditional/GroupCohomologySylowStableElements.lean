import Sharpness.Unconditional.GroupCohomologyStableElementsConjugation
import Mathlib.GroupTheory.Sylow
import Mathlib.Algebra.CharP.Defs

/-! The native stable-elements isomorphism at any Sylow subgroup, with arbitrary
trivial module over any field of the specified prime characteristic. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness.OrdinaryCohomology
variable {G : Type u} [Group G] [Finite G]
  (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p]

theorem sylow_index_isUnit (S : Sylow p G) : IsUnit ((S : Subgroup G).index : k) := by
  apply isUnit_iff_ne_zero.mpr
  intro h
  exact S.not_dvd_index ((CharP.cast_eq_zero_iff k p _).mp h)

def restrictionSylowStableElementsEquiv (S : Sylow p G)
    (A : Type u) [AddCommGroup A] [Module k A] (n : ℕ) :
    value k G A n ≃ₗ[k] stableElements (R := k) (A := A) (S : Subgroup G) n :=
  restrictionStableElementsEquiv (S : Subgroup G) n (sylow_index_isUnit p k S)

@[simp] theorem restrictionSylowStableElementsEquiv_apply (S : Sylow p G)
    (A : Type u) [AddCommGroup A] [Module k A] (n : ℕ) (x : value k G A n) :
    (restrictionSylowStableElementsEquiv p k S A n x).1 =
      pull (S : Subgroup G).subtype n x := rfl

end Sharpness.OrdinaryCohomology
