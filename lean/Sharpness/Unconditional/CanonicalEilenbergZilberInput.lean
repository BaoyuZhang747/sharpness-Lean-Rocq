import Sharpness.EilenbergZilberInput
import Sharpness.Unconditional.BisimplicialAlexanderWhitneyQuasiIso

/-! A proved inhabitant of the former Alexander–Whitney literature boundary. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness
open CategoryTheory Simplicial

def canonicalEilenbergZilberInput (R : Type u) [CommRing R] : EilenbergZilberInput R where
  alexanderWhitney X := bisimplicialAlexanderWhitney X R
  alexanderWhitney_component X := bisimplicialAlexanderWhitney_component X R
  Weibel_8_5_1 X := bisimplicialAlexanderWhitney_quasiIso X R

@[simp] theorem canonicalEilenbergZilberInput_map (R : Type u) [CommRing R]
    (X : SimplicialObject SSet.{u}) :
    (canonicalEilenbergZilberInput R).alexanderWhitney X =
      bisimplicialAlexanderWhitney X R := rfl

end Sharpness
