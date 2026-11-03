import Sharpness.FiniteBar
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-! The scalar comparison deduction in Proposition 2.3.
The general bar construction supplies the same underlying additive
cochains after restriction of scalars, with commuting differentials.
We prove that this data transfers cocycle exactness and actual Ext vanishing.
-/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness
open CategoryTheory
variable {R k C : Type u} [CommRing R] [CommRing k] [Algebra R k] [Category.{u} C]

def restrictCoefficientScalars (D : CoefficientCategory k C) : CoefficientCategory R C :=
  D ⋙ ModuleCat.restrictScalars (algebraMap R k)

/-- Scalar compatibility of the general bar computation (AKO III.5.3).
There is no Mackey or acyclicity assertion in this input. -/
structure ScalarBarComparison (BR : FiniteBarModel R C) (BK : FiniteBarModel k C) where
  cochains : ∀ D n,
    BR.Cochains (restrictCoefficientScalars (R := R) D) n ≃+ BK.Cochains D n
  differential : ∀ D n x,
    cochains D (n+1) (BR.d (restrictCoefficientScalars (R := R) D) n x) =
      BK.d D n (cochains D n x)

namespace ScalarBarComparison
variable {BR : FiniteBarModel R C} {BK : FiniteBarModel k C}
    (cmp : ScalarBarComparison BR BK) (D : CoefficientCategory k C)

include cmp

theorem exactPositive_of_restrict
    (h : BR.ExactPositive (restrictCoefficientScalars (R := R) D)) : BK.ExactPositive D := by
  intro n z hz
  let zR := (cmp.cochains D (n+1)).symm z
  have closed : BR.d (restrictCoefficientScalars (R := R) D) (n+1) zR = 0 := by
    apply (cmp.cochains D (n+2)).injective
    rw [map_zero, cmp.differential]
    change BK.d D (n+1) ((cmp.cochains D (n+1)) ((cmp.cochains D (n+1)).symm z)) = 0
    rw [AddEquiv.apply_symm_apply, hz]
  obtain ⟨b, hb⟩ := h n zR closed
  refine ⟨cmp.cochains D n b, ?_⟩
  rw [← cmp.differential, hb]
  exact (cmp.cochains D (n+1)).apply_symm_apply z

theorem acyclic_of_restrict
    [CategoryTheory.EnoughProjectives (CoefficientCategory R C)]
    [CategoryTheory.EnoughProjectives (CoefficientCategory k C)]
    (barR : BR.Comparison) (barK : BK.Comparison)
    (h : Acyclic (restrictCoefficientScalars (R := R) D)) : Acyclic D :=
  (BK.acyclic_iff barK D).mpr
    (cmp.exactPositive_of_restrict D ((BR.acyclic_iff barR _).mp h))

end ScalarBarComparison
end Sharpness
