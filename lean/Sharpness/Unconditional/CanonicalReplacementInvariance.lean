import Sharpness.Unconditional.CanonicalReplacementInvarianceTotal
import Sharpness.Unconditional.CostructuredDiagonalChainComparison
import Sharpness.ReplacementHomologyInvarianceInput

/-! The actual replacement diagonal comparison follows from the proved column/total
comparison and the quasi-isomorphism property of the explicitly constructed AW map.
The latter premise is explicit here until the separate AW construction is complete. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace Sharpness.TotalComparison
open CategoryTheory Simplicial
variable {R : Type u} [CommRing R]

theorem replacementDiagonalChainMap_quasiIso_of_AW
    {C : Type u} [Category.{u} C] {D E : C ⥤ SSet.{u}} (a : D ⟶ E)
    (ha : ∀ c, QuasiIso ((simplicialChainsFunctor R).map (a.app c)))
    (hD : QuasiIso (bisimplicialAlexanderWhitney (simplicialSetReplacement D) R))
    (hE : QuasiIso (bisimplicialAlexanderWhitney (simplicialSetReplacement E) R)) :
    QuasiIso ((simplicialChainsFunctor R).map (simplicialReplacementDiagonalMap a)) := by
  exact bisimplicialDiagonalChainsMap_quasiIso_of_AW_total
    (simplicialReplacementNatTrans a) R hD hE (replacementTotalChainMap_quasiIso a ha)

/-- This constructor exposes precisely the remaining AW theorem, with no total-comparison input. -/
def replacementHomologyInvarianceInput_of_AW
    (hAW : ∀ X : SimplicialObject SSet.{u}, QuasiIso (bisimplicialAlexanderWhitney X R)) :
    ReplacementHomologyInvarianceInput.{u} R where
  Weibel_5_2_12_5_6_1_8_5_1 a ha :=
    replacementDiagonalChainMap_quasiIso_of_AW a ha (hAW _) (hAW _)

end Sharpness.TotalComparison
