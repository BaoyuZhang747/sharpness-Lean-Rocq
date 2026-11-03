import Sharpness.NormalizerNerveCochains
import Sharpness.CostructuredDiagonalGrothendieckComponents
import Sharpness.ThomasonComparisonInput
import Sharpness.ReplacementHomologyInvarianceInput
import Sharpness.RealizationUnitCochains

/-! The actual nerve augmentation is the actual comma diagonal map
followed by the actual Libman Grothendieck-to-linking nerve map.
Thomason's uniform comparison and Libman's stated nerve comparison
therefore prove its chain quasi-isomorphism. Arbitrary-module duality
and the actual realization-unit replacement are proved separately.
No manuscript augmentation conclusion is a reference field. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace Sharpness.FusionSystem.CentricLinkingSystem.LibmanNormalizerInput
open CategoryTheory Simplicial Opposite
variable {S : Type u} [Group S] [Finite S] {F : FusionSystem S}
    {L : F.CentricLinkingSystem} {p : ℕ} [Fact p.Prime]
    {hS : IsPGroup p S} {sat : F.Saturated p}
    (I : L.LibmanNormalizerInput p hS sat)

theorem normalizerNerveDiagonalAugmentation_factor :
    I.normalizerNerveDiagonalAugmentation =
      costructuredDiagonalGrothendieckMap I.projection ≫
        CategoryTheory.nerveMap (CostructuredArrow.grothendieckProj I.projection ⋙ I.evaluation) := by
  have hc : simplicialReplacementDiagonalAugmentation (costructuredNerveDiagram I.projection)
        (costructuredNerveCocone I.projection) ≫ CategoryTheory.nerveMap I.evaluation =
      I.normalizerNerveDiagonalAugmentation := by
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.ext_apply
    rintro ⟨s, x⟩
    rfl
  have he : CategoryTheory.nerveMap
      (CostructuredArrow.grothendieckProj I.projection ⋙ I.evaluation) =
      CategoryTheory.nerveMap (CostructuredArrow.grothendieckProj I.projection) ≫
        CategoryTheory.nerveMap I.evaluation := rfl
  calc
    _ = (costructuredDiagonalGrothendieckMap I.projection ≫
          CategoryTheory.nerveMap (CostructuredArrow.grothendieckProj I.projection)) ≫
        CategoryTheory.nerveMap I.evaluation := by
      rw [costructuredDiagonalGrothendieckMap_projection]
      exact hc.symm
    _ = _ := by rw [he, Category.assoc]

variable (R : Type u) [CommRing R]

theorem normalizerNerveDiagonalChainAugmentation_factor :
    I.normalizerNerveDiagonalChainAugmentation R =
      (simplicialChainsFunctor R).map (costructuredDiagonalGrothendieckMap I.projection) ≫
        (simplicialChainsFunctor R).map (CategoryTheory.nerveMap
          (CostructuredArrow.grothendieckProj I.projection ⋙ I.evaluation)) := by
  calc
    _ = (simplicialChainsFunctor R).map I.normalizerNerveDiagonalAugmentation := rfl
    _ = (simplicialChainsFunctor R).map
        (costructuredDiagonalGrothendieckMap I.projection ≫ CategoryTheory.nerveMap
          (CostructuredArrow.grothendieckProj I.projection ⋙ I.evaluation)) :=
      congrArg (fun f => (simplicialChainsFunctor R).map f) I.normalizerNerveDiagonalAugmentation_factor
    _ = _ := (simplicialChainsFunctor R).map_comp _ _

theorem normalizerNerveDiagonalChainAugmentation_quasiIso (thom : ThomasonComparisonInput.{u} R) :
    QuasiIso (I.normalizerNerveDiagonalChainAugmentation R) := by
  letI : QuasiIso ((simplicialChainsFunctor R).map
      (costructuredDiagonalGrothendieckMap I.projection)) :=
    thom.Thomason_Mandell_5_1 (CostructuredArrow.functor I.projection)
      (costructuredDiagonalGrothendieckMap I.projection)
      (costructuredDiagonalGrothendieckMap_component I.projection)
  letI : QuasiIso ((simplicialChainsFunctor R).map (CategoryTheory.nerveMap
      (CostructuredArrow.grothendieckProj I.projection ⋙ I.evaluation))) :=
    I.Libman_5_1_1_Weibel R
  rw [I.normalizerNerveDiagonalChainAugmentation_factor R]
  infer_instance

theorem normalizerNerveDiagonalCochainAugmentation_quasiIso (A : ModuleCat.{u} R)
    (thom : ThomasonComparisonInput.{u} R) :
    QuasiIso (I.normalizerNerveDiagonalCochainAugmentation R A) := by
  letI (n : ℕ) : Projective ((I.normalizerNerveDiagonal.chainComplex (ModuleCat.of R R)).X n) :=
    I.normalizerNerveDiagonalChains_projective R n
  letI (n : ℕ) : Projective (((CategoryTheory.nerve L.Object).chainComplex (ModuleCat.of R R)).X n) :=
    SingularCohomology.simplicialChains_projective R (CategoryTheory.nerve L.Object) n
  letI := I.normalizerNerveDiagonalChainAugmentation_quasiIso R thom
  exact SingularCohomology.chainDualMap_quasiIso_of_projective R A
    (I.normalizerNerveDiagonalChainAugmentation R)

theorem normalizerNerveUnitChainMap_quasiIso (real : RealizationUnitInput.{u} R)
    (inv : ReplacementHomologyInvarianceInput.{u} R) :
    QuasiIso (I.normalizerNerveUnitChainMap R) :=
  inv.Weibel_5_2_12_5_6_1_8_5_1 (realizationDiagramUnit I.normalizerNerveDiagram)
    (fun d => real.May_16_2_Weibel_3_6_1 (I.normalizerNerveDiagram.obj d))

theorem normalizerNerveUnitCochainMap_quasiIso (A : ModuleCat.{u} R)
    (real : RealizationUnitInput.{u} R) (inv : ReplacementHomologyInvarianceInput.{u} R) :
    QuasiIso (I.normalizerNerveUnitCochainMap R A) := by
  letI (n : ℕ) : Projective ((I.normalizerNerveDiagonal.chainComplex (ModuleCat.of R R)).X n) :=
    I.normalizerNerveDiagonalChains_projective R n
  letI (n : ℕ) : Projective ((I.normalizerSingularDiagonal.chainComplex (ModuleCat.of R R)).X n) :=
    I.normalizerSingularDiagonalChains_projective R n
  letI := I.normalizerNerveUnitChainMap_quasiIso R real inv
  exact SingularCohomology.chainDualMap_quasiIso_of_projective R A (I.normalizerNerveUnitChainMap R)

theorem normalizerRealizationUnitCochainMap_quasiIso (A : ModuleCat.{u} R)
    (real : RealizationUnitInput.{u} R) : QuasiIso (I.normalizerRealizationUnitCochainMap R A) :=
  realizationUnitCochainMap_quasiIso R (CategoryTheory.nerve L.Object) A real

end Sharpness.FusionSystem.CentricLinkingSystem.LibmanNormalizerInput
