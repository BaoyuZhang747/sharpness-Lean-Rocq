import Sharpness.ScalarBar

/-! The reverse scalar-restriction implication for general bar cochains.
Together with ScalarBar, acyclicity is equivalent after scalar restriction. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness.ScalarBarComparison
open CategoryTheory
variable {R k C : Type u} [CommRing R] [CommRing k] [Algebra R k] [Category.{u} C]
    {BR : FiniteBarModel R C} {BK : FiniteBarModel k C}
    (cmp : ScalarBarComparison BR BK) (D : CoefficientCategory k C)

include cmp

theorem exactPositive_restrict_of (h : BK.ExactPositive D) :
    BR.ExactPositive (restrictCoefficientScalars (R := R) D) := by
  intro n z hz
  have closed : BK.d D (n+1) (cmp.cochains D (n+1) z) = 0 := by
    rw [← cmp.differential, hz, map_zero]
  obtain ⟨b, hb⟩ := h n _ closed
  refine ⟨(cmp.cochains D n).symm b, ?_⟩
  apply (cmp.cochains D (n+1)).injective
  rw [cmp.differential, AddEquiv.apply_symm_apply, hb]

theorem acyclic_restrict_of
    [EnoughProjectives (CoefficientCategory R C)]
    [EnoughProjectives (CoefficientCategory k C)]
    (barR : BR.Comparison) (barK : BK.Comparison) (h : Acyclic D) :
    Acyclic (restrictCoefficientScalars (R := R) D) :=
  (BR.acyclic_iff barR _).mpr
    (cmp.exactPositive_restrict_of D ((BK.acyclic_iff barK D).mp h))

end Sharpness.ScalarBarComparison
