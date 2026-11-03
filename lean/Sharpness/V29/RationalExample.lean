import Sharpness.V29.RationalDegreeZero
import Sharpness.Unconditional.FiniteGroupFusionSaturation
import Mathlib.Data.ZMod.Basic

/-! A concrete saturated example of Remark 3.3, on a group of order two. -/
noncomputable section
namespace Sharpness.FusionSystem

abbrev rationalExampleAmbient := Multiplicative (ZMod 2)
abbrev rationalExampleGroup := (⊤ : Subgroup rationalExampleAmbient)
def rationalExampleFusion : FusionSystem rationalExampleGroup := finiteGroupFusion ⊤

theorem rationalExample_pgroup : IsPGroup 2 rationalExampleGroup := by
  apply IsPGroup.of_card (n := 1)
  simp [rationalExampleGroup, rationalExampleAmbient, Nat.card_eq_fintype_card]

theorem rationalExample_saturated : rationalExampleFusion.Saturated 2 := by
  let P : Sylow 2 rationalExampleAmbient := rationalExample_pgroup.toSylow (by simp)
  exact finiteGroupFusion_saturated 2 P

theorem rationalExample_counterexample :
    rationalExampleFusion.rationalDegreeZeroMackey.IsSimple ∧
    (∃ x : rationalExampleFusion.rationalDegreeZeroMackey.Value
      (rationalExampleFusion.toOrbit.obj ⟨⊤⟩), x ≠ 0) ∧
    ¬ ∃ L : Subgroup rationalExampleGroup,
      rationalExampleFusion.IsMinimalSupport rationalExampleFusion.rationalDegreeZeroMackey L ∧
        Subgroup.centralizer (L : Set rationalExampleGroup) ≤ L :=
  rationalExampleFusion.rationalDegreeZero_centralizer_counterexample

end Sharpness.FusionSystem
