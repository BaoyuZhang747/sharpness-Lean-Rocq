import Sharpness.ChainDualAdditive

/-! Actual finite alternating sums of chain maps dualize term by term.
The summation index has its own universe. -/
set_option autoImplicit false
noncomputable section
universe u v
namespace Sharpness.SingularCohomology
open CategoryTheory
variable (R : Type u) [CommRing R] (A : ModuleCat.{u} R)
    {K L : ChainComplex (ModuleCat.{u} R) ℕ}

theorem chainDualMap_zsmul (r : ℤ) (f : K ⟶ L) :
    chainDualMap R (r • f) A = r • chainDualMap R f A := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  change (r • f.f n) ≫ z = r • (f.f n ≫ z)
  simp only [Preadditive.zsmul_comp]

theorem chainDualMap_sum {I : Type v} (s : Finset I) (f : I → (K ⟶ L)) :
    chainDualMap R (∑ i ∈ s, f i) A = ∑ i ∈ s, chainDualMap R (f i) A := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, chainDualMap_zero]
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, chainDualMap_add, ih, Finset.sum_insert hi]

end Sharpness.SingularCohomology
