import Sharpness.Unconditional.RealizationUnitHomologyCarriers
import Sharpness.Unconditional.RealizationUnitHomologySubdivisionHomotopy
import Sharpness.Unconditional.RealizationSmallSubdivisionChainMap
import Sharpness.Unconditional.HomotopyRestriction

/-! The actual subdivision homotopy restricts to every small-chain complex,
using its proved natural carrier property. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u v
namespace Sharpness.RealizationUnitHomology
open CategoryTheory

def smallSubdivisionHomotopy (R : Type u) [CommRing R]
    (X : TopCat.{u}) {ι : Type v} (U : ι → Set X) :
    Homotopy (smallSubdivisionChainMap R X U) (𝟙 _) :=
  Sharpness.restrictHomotopy (smallSingularChainsInclusion X U R)
    (smallSubdivisionChainMap_inclusion R X U) (by simp)
    (subdivisionHomotopy R X)
    (fun n m => smallNaturalDegree U R ((subdivisionNaturalHomotopy R).hom n m))
    (fun n m => smallNaturalDegree_inclusion U R ((subdivisionNaturalHomotopy R).hom n m))

end Sharpness.RealizationUnitHomology
