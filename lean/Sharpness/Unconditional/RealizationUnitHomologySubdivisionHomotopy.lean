import Sharpness.Unconditional.RealizationUnitHomologySubdivisionChainMap
import Sharpness.Unconditional.RealizationUnitHomologyNaturalHomotopy

/-! Actual barycentric subdivision is naturally chain homotopic to the identity. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace Sharpness.RealizationUnitHomology
open CategoryTheory
variable (R : Type u) [CommRing R]

def subdivisionNaturalHomotopy :
    Homotopy (functorChainComplexMap (subdivisionNatTrans R))
      (𝟙 (functorChainComplex (SingularCohomology.chainsFunctor R))) :=
  singularNaturalChainHomotopy R (subdivisionNatTrans R) (𝟙 _)
    (fun X => subdivisionDegree_zero R X)

def subdivisionHomotopy (X : TopCat.{u}) :
    Homotopy (subdivisionChainMap R X) (𝟙 _) :=
  ((evaluation TopCat.{u} (ModuleCat.{u} R)).obj X).mapHomotopy
    (subdivisionNaturalHomotopy R)

@[simp] theorem subdivisionHomotopy_hom (X : TopCat.{u}) (n m : ℕ) :
    (subdivisionHomotopy R X).hom n m = ((subdivisionNaturalHomotopy R).hom n m).app X := rfl

end Sharpness.RealizationUnitHomology
