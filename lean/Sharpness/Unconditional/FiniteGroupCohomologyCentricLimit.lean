import Sharpness.Unconditional.FiniteGroupCohomologyStableComparison
import Sharpness.Unconditional.Alperin

/-! Native inverse-limit stable-elements comparison for a group-induced
fusion system. Saturation is an explicit genuine hypothesis here; the Sylow
constructor discharges it in the final specialization. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness.OrdinaryCohomology
open CategoryTheory CategoryTheory.Limits
variable {R G A : Type u} [CommRing R] [Group G] [Finite G]
  [AddCommGroup A] [Module R A]

def finiteGroupCentricLimitIso (S : Subgroup G) (p : ℕ) [Fact p.Prime]
    (hS : IsPGroup p S) (sat : (finiteGroupFusion S).Saturated p)
    (hindex : IsUnit (S.index : R)) (n : ℕ) :
    limit ((finiteGroupFusion S).cohomologyCoefficient (R := R) (A := A) n) ≅
      value R G A n :=
  HasLimit.isoOfNatIso ((finiteGroupFusion S).nativeCohomologyMackeyCentricIso n).symm ≪≫
    (finiteGroupFusion S).nativeCentricStableIso
      ((finiteGroupFusion S).alperinInput p hS sat)
      ((finiteGroupFusion S).nativeGroupCohomologyMackey n) ≪≫
    (finiteGroupCohomologyFusionStableIso S n hindex).symm

def finiteGroupCentricHigherLimitZeroIso (S : Subgroup G) (p : ℕ) [Fact p.Prime]
    (hS : IsPGroup p S) (sat : (finiteGroupFusion S).Saturated p)
    (hindex : IsUnit (S.index : R)) (n : ℕ) :
    higherLimit ((finiteGroupFusion S).cohomologyCoefficient (R := R) (A := A) n) 0 ≅
      value R G A n :=
  higherLimitIso ((finiteGroupFusion S).nativeCohomologyMackeyCentricIso n).symm 0 ≪≫
    (((finiteGroupFusion S).coefficientData
      ((finiteGroupFusion S).nativeGroupCohomologyMackey (R := R) (A := A) n)).onFull
        (finiteGroupFusion S).centricProperty).higherLimitZeroIso ≪≫
    ((finiteGroupFusion S).compatibleStableLinearEquiv
      ((finiteGroupFusion S).alperinInput p hS sat)
      ((finiteGroupFusion S).nativeGroupCohomologyMackey n)).toModuleIso ≪≫
    (finiteGroupCohomologyFusionStableIso S n hindex).symm

end Sharpness.OrdinaryCohomology
