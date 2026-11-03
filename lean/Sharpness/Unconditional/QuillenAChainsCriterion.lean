import Sharpness.Unconditional.QuillenAChainsDiagonal
import Sharpness.Unconditional.CanonicalReplacementInvarianceTotal

/-! The homological comma criterion, with only the separately constructed
Alexander-Whitney map's quasi-isomorphism still exposed as a comparison premise. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace Sharpness
open CategoryTheory Simplicial
variable {C D : Type u} [Category.{u} C] [Category.{u} D]
  (T : C ⥤ D) (R : Type u) [CommRing R]

theorem nerveMap_quasiIso_of_costructured_fibres_of_AW
    (h : ∀ d, QuasiIso (SSet.chainComplexMap
      (nerveMap (Functor.star.{u} (CostructuredArrow T d))) (ModuleCat.of R R)))
    (hAW : ∀ X : SimplicialObject SSet.{u}, QuasiIso (bisimplicialAlexanderWhitney X R)) :
    QuasiIso (SSet.chainComplexMap (nerveMap T) (ModuleCat.of R R)) :=
  nerveMap_quasiIso_of_costructured_AW_totals T R hAW
    (TotalComparison.costructuredFlippedAugmentation_total_quasiIso T)
    (TotalComparison.costructuredBaseProjection_total_quasiIso T h)

theorem nerveMap_quasiIso_of_structured_fibres_of_AW
    (h : ∀ d, QuasiIso (SSet.chainComplexMap
      (nerveMap (Functor.star.{u} (StructuredArrow d T))) (ModuleCat.of R R)))
    (hAW : ∀ X : SimplicialObject SSet.{u}, QuasiIso (bisimplicialAlexanderWhitney X R)) :
    QuasiIso (SSet.chainComplexMap (nerveMap T) (ModuleCat.of R R)) :=
  nerveMap_quasiIso_of_structured_AW_totals T R hAW
    (TotalComparison.costructuredFlippedAugmentation_total_quasiIso T.op)
    (TotalComparison.costructuredBaseProjection_total_quasiIso T.op
      (costructured_op_fibre_quasiIso_of_structured T (ModuleCat.of R R) h))

end Sharpness
