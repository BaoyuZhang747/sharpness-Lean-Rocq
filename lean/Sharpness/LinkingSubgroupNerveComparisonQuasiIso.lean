import Sharpness.ThomasonComparisonInput
import Sharpness.ReplacementHomologyInvarianceInput
import Sharpness.RealizationUnitCochains
import Sharpness.CostructuredDiagonalGrothendieckComponents
import Sharpness.LinkingSubgroupNerveGrothendieckCochains

/-! The two actual remaining nerve comparisons are quasi-isomorphisms
under uniform standard reference inputs. All actual map formulas,
unit squares and projections were constructed and proved separately.
Their arbitrary-module duals use degreewise projectivity, not an
injectivity condition on the coefficient module. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace Sharpness.FusionSystem.CentricLinkingSystem
open CategoryTheory
variable {S : Type u} [Group S] {F : FusionSystem S}
    (L : F.CentricLinkingSystem) (R : Type u) [CommRing R] (A : ModuleCat.{u} R)

theorem subgroupNerveGrothendieckChainMap_quasiIso (thom : ThomasonComparisonInput.{u} R) :
    QuasiIso (L.subgroupNerveGrothendieckChainMap R) := by
  exact thom.Thomason_Mandell_5_1 L.subgroupCategoryDiagram L.subgroupNerveGrothendieckComparison
    (costructuredDiagonalGrothendieckMap_component L.orbitProjection)

theorem subgroupNerveGrothendieckCochainMap_quasiIso (thom : ThomasonComparisonInput.{u} R) :
    QuasiIso (L.subgroupNerveGrothendieckCochainMap R A) := by
  letI (n : ℕ) : Projective ((L.subgroupNerveDiagonal.chainComplex (ModuleCat.of R R)).X n) :=
    L.subgroupNerveDiagonalChains_projective R n
  letI (n : ℕ) : Projective (((CategoryTheory.nerve L.subgroupGrothendieck).chainComplex
      (ModuleCat.of R R)).X n) :=
    SingularCohomology.simplicialChains_projective R (CategoryTheory.nerve L.subgroupGrothendieck) n
  letI := L.subgroupNerveGrothendieckChainMap_quasiIso R thom
  exact SingularCohomology.chainDualMap_quasiIso_of_projective R A
    (L.subgroupNerveGrothendieckChainMap R)

theorem subgroupNerveUnitChainMap_quasiIso (real : RealizationUnitInput.{u} R)
    (inv : ReplacementHomologyInvarianceInput.{u} R) :
    QuasiIso (L.subgroupNerveUnitChainMap R) := by
  exact inv.Weibel_5_2_12_5_6_1_8_5_1 (realizationDiagramUnit L.subgroupNerveDiagram)
    (fun P => real.May_16_2_Weibel_3_6_1 (L.subgroupNerveDiagram.obj P))

theorem subgroupNerveUnitCochainMap_quasiIso (real : RealizationUnitInput.{u} R)
    (inv : ReplacementHomologyInvarianceInput.{u} R) :
    QuasiIso (L.subgroupNerveUnitCochainMap R A) := by
  letI (n : ℕ) : Projective ((L.subgroupNerveDiagonal.chainComplex (ModuleCat.of R R)).X n) :=
    L.subgroupNerveDiagonalChains_projective R n
  letI (n : ℕ) : Projective ((L.subgroupSingularDiagonal.chainComplex (ModuleCat.of R R)).X n) :=
    L.subgroupSingularDiagonalChains_projective R n
  letI := L.subgroupNerveUnitChainMap_quasiIso R real inv
  exact SingularCohomology.chainDualMap_quasiIso_of_projective R A (L.subgroupNerveUnitChainMap R)

end Sharpness.FusionSystem.CentricLinkingSystem
