import Sharpness.Unconditional.FirstQuadrantTotalComparison
import Sharpness.Unconditional.CanonicalReplacementInvarianceColumns
import Sharpness.Unconditional.CostructuredHorizontalRowsContraction
import Sharpness.Unconditional.QuillenAChainsBaseProjection

/-! Applications of the proved first-quadrant total comparison to actual replacement maps. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace Sharpness.TotalComparison
open CategoryTheory Simplicial Opposite
variable {R : Type u} [CommRing R]

theorem replacementTotalChainMap_quasiIso
    {C : Type u} [Category.{u} C] {D E : C ⥤ SSet.{u}} (a : D ⟶ E)
    (ha : ∀ c, QuasiIso ((simplicialChainsFunctor R).map (a.app c))) :
    QuasiIso (bisimplicialTotalChainsMap (simplicialReplacementNatTrans a) R) := by
  apply bisimplicialTotalChainsMap_quasiIso_of_columns
  intro p
  exact replacementColumnChainMap_quasiIso a ha ⦋p⦌

theorem costructuredFlippedAugmentation_total_quasiIso
    {C D : Type u} [Category.{u} C] [Category.{u} D] (T : C ⥤ D) :
    QuasiIso (bisimplicialTotalChainsMap (costructuredFlippedAugmentation T) R) := by
  apply bisimplicialTotalChainsMap_quasiIso_of_columns
  intro p
  exact costructuredHorizontalRowAugmentation_quasiIso T p (ModuleCat.of R R)

theorem costructuredBaseProjection_total_quasiIso
    {C D : Type u} [Category.{u} C] [Category.{u} D] (T : C ⥤ D)
    (h : ∀ d, QuasiIso (SSet.chainComplexMap
      (nerveMap (Functor.star (CostructuredArrow T d))) (ModuleCat.of R R))) :
    QuasiIso (bisimplicialTotalChainsMap
      (simplicialReplacementBaseProjection (costructuredNerveDiagram T)) R) := by
  apply bisimplicialTotalChainsMap_quasiIso_of_columns
  intro p
  exact costructuredBaseColumn_quasiIso T R h ⦋p⦌

end Sharpness.TotalComparison
