import Sharpness.HigherLimits

/-! The projective-coefficient interface, separated from the remaining fusion
reference data so its proved implementation is available to foundations. -/

set_option autoImplicit false
universe u
namespace Sharpness
open CategoryTheory

/-- Small module-valued functor categories have enough projectives. -/
class ProjectiveCoefficientInput where
  contravariant : ∀ (R : Type u) [CommRing R] (J : Type u) [Category.{u} J],
    EnoughProjectives (CoefficientCategory R J)
  covariant : ∀ (R : Type u) [CommRing R] (J : Type u) [Category.{u} J],
    EnoughProjectives (J ⥤ ModuleCat.{u} R)

attribute [instance] ProjectiveCoefficientInput.contravariant ProjectiveCoefficientInput.covariant

end Sharpness
