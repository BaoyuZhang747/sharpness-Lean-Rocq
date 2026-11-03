import Sharpness.Unconditional.InducedCategoryBarConstruction

/-! The cochain complex obtained by applying linear Hom to the concrete bar
chain complex is the project's existing coefficient cochain complex. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace Sharpness.Unconditional
open CategoryTheory CategoryTheory.Limits Opposite Simplicial

variable {R C D : Type u} [CommRing R] [Category.{u} C] [Category.{u} D]
  {q : C ⥤ D}

/-- Applying Hom to the explicit projective bar terms recovers the existing
coefficient complex, with its actual alternating coface differential. -/
def inducedCategoryBarHomComplexIso (q : C ⥤ D) (M : CoefficientCategory R D) :
    (inducedCategoryBarComplex R q).linearYonedaObj R M ≅ coefficientCochains (q.op ⋙ M) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => (inducedCategoryBarHomEquiv n M).toModuleIso) (by
      intro i j hij
      have hj : i + 1 = j := hij
      subst j
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro α
      change (coefficientCochains (q.op ⋙ M)).d i (i + 1)
          (inducedCategoryBarHomEquiv i M α) =
        inducedCategoryBarHomEquiv (i + 1) M ((inducedCategoryBarComplex R q).d (i + 1) i ≫ α)
      simp only [coefficientCochains, AlgebraicTopology.alternatingCofaceMapComplex,
        AlgebraicTopology.AlternatingCofaceMapComplex.obj, CochainComplex.of_d,
        AlgebraicTopology.AlternatingCofaceMapComplex.objD, inducedCategoryBarComplex,
        AlgebraicTopology.alternatingFaceMapComplex_obj_d,
        AlgebraicTopology.AlternatingFaceMapComplex.objD,
        Preadditive.sum_comp, Preadditive.zsmul_comp, map_sum, map_zsmul,
        ModuleCat.hom_sum, ModuleCat.hom_zsmul, LinearMap.sum_apply, LinearMap.smul_apply]
      apply Finset.sum_congr rfl
      intro k hk
      congr 1
      exact (inducedCategoryBarHomEquiv_map (SimplexCategory.δ k) M α).symm)

/-- The actual induced bar augmentation to the constant target diagram. -/
def inducedCategoryBarAugmentationChain (R : Type u) [CommRing R] (q : C ⥤ D) :
    inducedCategoryBarComplex R q ⟶
      (ChainComplex.single₀ (CoefficientCategory R D)).obj (constantCoefficient R D) :=
  AlgebraicTopology.AlternatingFaceMapComplex.ε.app (inducedCategoryBarAugmented R q)

end Sharpness.Unconditional
