import Sharpness.Unconditional.InducedCategoryBarCommaLinearization
import Sharpness.Unconditional.InducedCategoryBarCommaAugmentation
import Mathlib.Algebra.Homology.Functor

/-! Evaluation identifies the actual induced bar with the comma nerve chains,
and identifies their augmentations. Comma acyclicity therefore makes the
projective induced bar into a resolution; no Kan-extension exactness is assumed. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace Sharpness.Unconditional
open CategoryTheory CategoryTheory.Limits Simplicial Opposite AlgebraicTopology
variable (R : Type u) [CommRing R] {C D : Type u} [Category.{u} C] [Category.{u} D]
  (q : C ⥤ D)

def inducedCategoryBarEvaluationIso (X : D) :
    (alternatingFaceMapComplex (ModuleCat.{u} R)).obj
      (inducedCategoryBarSimplicial R q ⋙ (evaluation Dᵒᵖ (ModuleCat.{u} R)).obj (op X)) ≅
      (((evaluation Dᵒᵖ (ModuleCat.{u} R)).obj (op X)).mapHomologicalComplex _).obj
        (inducedCategoryBarComplex R q) :=
  eqToIso (Functor.congr_obj
    (map_alternatingFaceMapComplex ((evaluation Dᵒᵖ (ModuleCat.{u} R)).obj (op X))).symm
    (inducedCategoryBarSimplicial R q))

/-- The actual evaluated bar is isomorphic to native comma-category chains. -/
def inducedCategoryBarCommaChainIso (X : D) :
    (((evaluation Dᵒᵖ (ModuleCat.{u} R)).obj (op X)).mapHomologicalComplex _).obj
        (inducedCategoryBarComplex R q) ≅
      (nerve (StructuredArrow X q)).chainComplex (ModuleCat.of R R) :=
  (inducedCategoryBarEvaluationIso R q X).symm ≪≫
    (alternatingFaceMapComplex (ModuleCat.{u} R)).mapIso
      (inducedCategoryBarCommaSimplicialIso R q X)

theorem inducedCategoryBarCommaChainIso_f (X : D) (n : ℕ) :
    (inducedCategoryBarCommaChainIso R q X).hom.f n =
      (inducedCategoryBarCommaDegreeIso R q X n).hom := by
  simp [inducedCategoryBarCommaChainIso, inducedCategoryBarEvaluationIso,
    inducedCategoryBarCommaSimplicialIso]

/-- The comparison preserves the ordinary augmentation, including degree zero. -/
theorem inducedCategoryBarCommaChainIso_augmentation (X : D) :
    (((evaluation Dᵒᵖ (ModuleCat.{u} R)).obj (op X)).mapHomologicalComplex _).map
        (inducedCategoryBarAugmentationChain R q) ≫
      (HomologicalComplex.singleMapHomologicalComplex _ _ _).hom.app (constantCoefficient R D) =
    (inducedCategoryBarCommaChainIso R q X).hom ≫
      inducedCommaNerveAugmentation R (nerve (StructuredArrow X q)) := by
  apply HomologicalComplex.to_single_hom_ext
  change (inducedCategoryBarAugmentation (R := R) (q := q) 0).app (op X) ≫ 𝟙 _ =
    (inducedCategoryBarCommaChainIso R q X).hom.f 0 ≫
      (inducedCommaNerveAugmentation R (nerve (StructuredArrow X q))).f 0
  rw [Category.comp_id, inducedCategoryBarCommaChainIso_f]
  apply ModuleCat.free_hom_ext
  rintro ⟨s, g⟩
  simp only [ModuleCat.comp_apply]
  erw [inducedCategoryBarAugmentation_freeMk, inducedCategoryBarCommaDegreeIso_hom_freeMk]
  change (1 : R) = ((nerve (StructuredArrow X q)).ιChainComplex
    (inducedBarCommaString q s g) ≫
    (inducedCommaNerveAugmentation R (nerve (StructuredArrow X q))).f 0) 1
  rw [inducedCommaNerveAugmentation_ι]
  rfl

/-- Actual acyclicity of all comma nerves proves that the induced bar augmentation
is a quasi-isomorphism of coefficient diagrams. -/
theorem inducedCategoryBarAugmentationChain_quasiIso_of_comma
    (h : ∀ X : D, QuasiIso (SSet.chainComplexMap
      (nerveMap (Functor.star.{u} (StructuredArrow X q))) (ModuleCat.of R R))) :
    QuasiIso (inducedCategoryBarAugmentationChain R q) := by
  rw [HomologicalComplex.quasiIso_iff_evaluation]
  intro X
  haveI := inducedCommaNerveAugmentation_quasiIso_of_star R (StructuredArrow X.unop q) (h X.unop)
  have ht : QuasiIso ((inducedCategoryBarCommaChainIso R q X.unop).hom ≫
      inducedCommaNerveAugmentation R (nerve (StructuredArrow X.unop q))) := inferInstance
  rw [← inducedCategoryBarCommaChainIso_augmentation R q X.unop] at ht
  exact quasiIso_of_comp_right (hφφ' := ht)

end Sharpness.Unconditional
