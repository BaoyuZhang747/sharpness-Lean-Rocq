import Sharpness.Unconditional.CanonicalReplacementInvariance
import Sharpness.Unconditional.BisimplicialAlexanderWhitneyQuasiIso

/-! Unconditional homology invariance for the actual simplicial replacement.
Both the finite-diagonal total comparison and the native Alexander–Whitney
quasi-isomorphism are proved in the imported modules. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness
open CategoryTheory
variable (R : Type u) [CommRing R]

def canonicalReplacementHomologyInvarianceInput : ReplacementHomologyInvarianceInput.{u} R :=
  TotalComparison.replacementHomologyInvarianceInput_of_AW
    (fun X => bisimplicialAlexanderWhitney_quasiIso X R)

theorem simplicialReplacementDiagonalMap_quasiIso
    {C : Type u} [Category.{u} C] {D E : C ⥤ SSet.{u}} (a : D ⟶ E)
    (ha : ∀ c, QuasiIso ((simplicialChainsFunctor R).map (a.app c))) :
    QuasiIso ((simplicialChainsFunctor R).map (simplicialReplacementDiagonalMap a)) :=
  (canonicalReplacementHomologyInvarianceInput R).Weibel_5_2_12_5_6_1_8_5_1 a ha

end Sharpness
