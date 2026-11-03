import Sharpness.Unconditional.RealizationUnitHomologyModels
import Sharpness.Unconditional.ModelwisePresentation

/-! The actual native singular degree functors have free presentations on the
actual topological simplex, obtained from Mathlib's evaluation adjunction. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
noncomputable section
universe u
namespace Sharpness.RealizationUnitHomology
open CategoryTheory Simplicial Opposite

variable (R : Type u) [CommRing R]

def singularDegreePresentation (n : ℕ) :
    ModelPresentation
      (SingularCohomology.chainsFunctor R ⋙
        HomologicalComplex.eval (ModuleCat.{u} R) (ComplexShape.down ℕ) n)
      (fun _ : Unit => SimplexCategory.toTop.{u}.obj ⦋n⦌) :=
  ModelPresentation.ofAdjunction _ _
    (AlgebraicTopology.singularChainComplexFunctorAdjunction (ModuleCat.{u} R) n)

/-- The chosen model generator is exactly the singular simplex which is the
identity of the actual standard topological simplex, with coefficient one. -/
theorem singularDegreePresentation_generator (n : ℕ) :
    (singularDegreePresentation R n).generator () =
      (TopCat.toSSet.obj (SimplexCategory.toTop.{u}.obj ⦋n⦌)).ιChainComplex
        (R := ModuleCat.of R R) (ULift.up (𝟙 (SimplexCategory.toTop.{u}.obj ⦋n⦌))) (1 : R) := by
  change (AlgebraicTopology.singularChainComplexFunctorAdjunction (ModuleCat.{u} R) n).unit.app
    (ModuleCat.of R R) (1 : R) = _
  rw [AlgebraicTopology.singularChainComplexFunctorAdjunction_unit_app]
  have hσ : ((SSet.stdSimplexToTop.app ⦋n⦌).app (op ⦋n⦌)
      (SSet.stdSimplex.objEquiv.symm (𝟙 ⦋n⦌))) =
      ULift.up (𝟙 (SimplexCategory.toTop.{u}.obj ⦋n⦌)) := by
    apply ULift.ext
    change (((sSetTopAdj.unit.app (Δ[n] : SSet.{u})).app (op ⦋n⦌)
      (SSet.stdSimplex.objEquiv.symm (𝟙 ⦋n⦌))).down) ≫
        (SSet.toTopSimplex.app ⦋n⦌).hom = 𝟙 _
    rw [sSetTopAdj_unit_app_app_down]
    simp only [SSet.yonedaEquiv_symm_stdSimplex_id, CategoryTheory.Functor.map_id]
    change ((SSet.toTopSimplex.app ⦋n⦌).inv ≫ 𝟙 _) ≫
      (SSet.toTopSimplex.app ⦋n⦌).hom = 𝟙 _
    simp only [Category.comp_id, Iso.inv_hom_id]
  rw [hσ]
  rfl

end Sharpness.RealizationUnitHomology
