import Sharpness.Unconditional.QuillenAChainsCriterion
import Sharpness.Unconditional.BisimplicialAlexanderWhitneyQuasiIso

/-! The homological comma criterion for the actual native nerve-chain map.
The Alexander-Whitney and total-complex comparisons are proved constructions. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace Sharpness
open CategoryTheory
variable {C D : Type u} [Category.{u} C] [Category.{u} D]
  (T : C ⥤ D) (R : Type u) [CommRing R]

theorem nerveMap_quasiIso_of_costructured_fibres
    (h : ∀ d, QuasiIso (SSet.chainComplexMap
      (nerveMap (Functor.star.{u} (CostructuredArrow T d))) (ModuleCat.of R R))) :
    QuasiIso (SSet.chainComplexMap (nerveMap T) (ModuleCat.of R R)) :=
  nerveMap_quasiIso_of_costructured_fibres_of_AW T R h
    (fun X => bisimplicialAlexanderWhitney_quasiIso X R)

theorem nerveMap_quasiIso_of_structured_fibres
    (h : ∀ d, QuasiIso (SSet.chainComplexMap
      (nerveMap (Functor.star.{u} (StructuredArrow d T))) (ModuleCat.of R R))) :
    QuasiIso (SSet.chainComplexMap (nerveMap T) (ModuleCat.of R R)) :=
  nerveMap_quasiIso_of_structured_fibres_of_AW T R h
    (fun X => bisimplicialAlexanderWhitney_quasiIso X R)

end Sharpness
