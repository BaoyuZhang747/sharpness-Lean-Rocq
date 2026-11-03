import Sharpness.Unconditional.CanonicalReplacementInvarianceUnconditional
import Sharpness.Unconditional.CanonicalEilenbergZilberInput

/-! The actual comma-replacement diagonal augmentation is a native chain
quasi-isomorphism. This specialized theorem does not assume or construct a
universal Thomason comparison record. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness
open CategoryTheory
variable (R : Type u) [CommRing R]

theorem costructuredDiagonalAugmentation_quasiIso_native
    {C D : Type u} [Category.{u} C] [Category.{u} D] (T : C ⥤ D) :
    QuasiIso (SSet.chainComplexMap
      (simplicialReplacementDiagonalAugmentation (costructuredNerveDiagram T)
        (costructuredNerveCocone T)) (ModuleCat.of R R)) :=
  costructuredDiagonalAugmentation_quasiIso_of_AW_total R T
    (bisimplicialAlexanderWhitney_quasiIso _ R)
    (bisimplicialAlexanderWhitney_quasiIso _ R)
    (TotalComparison.costructuredFlippedAugmentation_total_quasiIso T)

end Sharpness
