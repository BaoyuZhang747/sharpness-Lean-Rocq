import Sharpness.Unconditional.QuillenAChainsComparison
import Sharpness.Unconditional.QuillenAChainsOppositeFibres

/-! Explicit algebraic comparison implications for the two comma projections.
Only the actual Alexander-Whitney and total maps are left as premises here. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace Sharpness
open CategoryTheory Simplicial Opposite
variable {C D : Type u} [Category.{u} C] [Category.{u} D]
  (T : C ⥤ D) (R : Type u) [CommRing R]

theorem costructuredBaseProjection_diagonal :
    bisimplicialDiagonalMap
        (simplicialReplacementBaseProjection (costructuredNerveDiagram T)) ≫
      (costructuredFlippedDiagonalTargetIso (C := D)).hom =
    simplicialReplacementBaseDiagonal (costructuredNerveDiagram T) := by
  ext n x
  rfl

theorem costructuredBaseDiagonal_quasiIso_of_AW_total
    (hSource : QuasiIso (bisimplicialAlexanderWhitney
      (simplicialSetReplacement (costructuredNerveDiagram T)) R))
    (hTarget : QuasiIso (bisimplicialAlexanderWhitney
      ((Functor.const SimplexCategoryᵒᵖ).obj (nerve D)).flip R))
    (hTotal : QuasiIso (bisimplicialTotalChainsMap
      (simplicialReplacementBaseProjection (costructuredNerveDiagram T)) R)) :
    QuasiIso (SSet.chainComplexMap
      (simplicialReplacementBaseDiagonal (costructuredNerveDiagram T))
      (ModuleCat.of R R)) := by
  let J := (SSet.chainComplexFunctor (ModuleCat.{u} R)).obj (ModuleCat.of R R)
  haveI : QuasiIso (J.map (bisimplicialDiagonalMap
      (simplicialReplacementBaseProjection (costructuredNerveDiagram T)))) :=
    bisimplicialDiagonalChainsMap_quasiIso_of_AW_total
      (simplicialReplacementBaseProjection (costructuredNerveDiagram T)) R
      hSource hTarget hTotal
  change QuasiIso (J.map (simplicialReplacementBaseDiagonal (costructuredNerveDiagram T)))
  rw [← costructuredBaseProjection_diagonal T, J.map_comp]
  infer_instance

/-- This intermediate result exposes the exact pending algebraic comparison
maps. It contains no global Quillen-A premise. -/
theorem nerveMap_quasiIso_of_costructured_AW_totals
    (hAW : ∀ X : SimplicialObject SSet.{u}, QuasiIso (bisimplicialAlexanderWhitney X R))
    (hAugTotal : QuasiIso (bisimplicialTotalChainsMap (costructuredFlippedAugmentation T) R))
    (hBaseTotal : QuasiIso (bisimplicialTotalChainsMap
      (simplicialReplacementBaseProjection (costructuredNerveDiagram T)) R)) :
    QuasiIso (SSet.chainComplexMap (nerveMap T) (ModuleCat.of R R)) :=
  nerveMap_quasiIso_of_costructuredDiagonal T (ModuleCat.of R R)
    (costructuredDiagonalAugmentation_quasiIso_of_AW_total R T
      (hAW _) (hAW _) hAugTotal)
    (costructuredBaseDiagonal_quasiIso_of_AW_total T R
      (hAW _) (hAW _) hBaseTotal)

/-- The same concrete comparison in the structured-arrow orientation uses
the signed opposite-nerve isomorphism already proved without premises. -/
theorem nerveMap_quasiIso_of_structured_AW_totals
    (hAW : ∀ X : SimplicialObject SSet.{u}, QuasiIso (bisimplicialAlexanderWhitney X R))
    (hAugTotal : QuasiIso (bisimplicialTotalChainsMap (costructuredFlippedAugmentation T.op) R))
    (hBaseTotal : QuasiIso (bisimplicialTotalChainsMap
      (simplicialReplacementBaseProjection (costructuredNerveDiagram T.op)) R)) :
    QuasiIso (SSet.chainComplexMap (nerveMap T) (ModuleCat.of R R)) :=
  (nerveOppositeChainMap_quasiIso_iff T (ModuleCat.of R R)).mp
    (nerveMap_quasiIso_of_costructured_AW_totals T.op R hAW hAugTotal hBaseTotal)

end Sharpness
