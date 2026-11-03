import Sharpness.SingularCochains
import Mathlib.AlgebraicTopology.SingularHomology.HomotopyInvariance

/-! Homotopy invariance for the actual singular cochain and cohomology
objects, for every constant R-module A. It follows by dualizing the
native singular-chain homotopy, rather than assuming cohomology invariance. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness.SingularCohomology
open CategoryTheory
variable (R : Type u) [CommRing R]

def cochainHomotopy {X Y : TopCat.{u}} {f g : X ⟶ Y}
    (H : TopCat.Homotopy f g) (A : ModuleCat.{u} R) :
    Homotopy (cochainPull R f A) (cochainPull R g A) :=
  ((((linearYoneda R (ModuleCat.{u} R)).obj A).rightOp).mapHomotopy
    (H.singularChainComplexFunctorObjMap (ModuleCat.of R R))).unop

theorem pull_eq_of_homotopy {X Y : TopCat.{u}} {f g : X ⟶ Y}
    (H : TopCat.Homotopy f g) (A : ModuleCat.{u} R) (n : ℕ) :
    pull R f A n = pull R g A n :=
  (cochainHomotopy R H A).homologyMap_eq n

end Sharpness.SingularCohomology
