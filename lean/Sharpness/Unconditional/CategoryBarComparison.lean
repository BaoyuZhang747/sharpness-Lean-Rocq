import Sharpness.Unconditional.CategoryBarConstruction

/-! The cochain complex obtained by applying linear Hom to the concrete bar
chain complex is the project's existing coefficient cochain complex. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace Sharpness.Unconditional
open CategoryTheory CategoryTheory.Limits Opposite Simplicial

variable {R C : Type u} [CommRing R] [Category.{u} C]

/-- Applying Hom to the explicit projective bar terms recovers the existing
coefficient complex, with its actual alternating coface differential. -/
def categoryBarHomComplexIso (M : CoefficientCategory R C) :
    (categoryBarComplex R C).linearYonedaObj R M ≅ coefficientCochains M :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => (categoryBarHomEquiv n M).toModuleIso) (by
      intro i j hij
      have hj : i + 1 = j := hij
      subst j
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro α
      change (coefficientCochains M).d i (i + 1)
          (categoryBarHomEquiv i M α) =
        categoryBarHomEquiv (i + 1) M ((categoryBarComplex R C).d (i + 1) i ≫ α)
      simp only [coefficientCochains, AlgebraicTopology.alternatingCofaceMapComplex,
        AlgebraicTopology.AlternatingCofaceMapComplex.obj, CochainComplex.of_d,
        AlgebraicTopology.AlternatingCofaceMapComplex.objD, categoryBarComplex,
        AlgebraicTopology.alternatingFaceMapComplex_obj_d,
        AlgebraicTopology.AlternatingFaceMapComplex.objD,
        Preadditive.sum_comp, Preadditive.zsmul_comp, map_sum, map_zsmul,
        ModuleCat.hom_sum, ModuleCat.hom_zsmul, LinearMap.sum_apply, LinearMap.smul_apply]
      apply Finset.sum_congr rfl
      intro k hk
      congr 1
      exact (categoryBarHomEquiv_map (SimplexCategory.δ k) M α).symm)

/-- Coefficient maps act on bar Hom complexes by postcomposition. -/
def categoryBarHomComplexMap {M N : CoefficientCategory R C} (a : M ⟶ N) :
    (categoryBarComplex R C).linearYonedaObj R M ⟶
      (categoryBarComplex R C).linearYonedaObj R N where
  f n := ModuleCat.ofHom (Linear.rightComp R _ a)
  comm' i j hij := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro α
    change (categoryBarComplex R C).d j i ≫ (α ≫ a) =
      ((categoryBarComplex R C).d j i ≫ α) ≫ a
    exact (Category.assoc _ _ _).symm

/-- The bar Hom complex is functorial in the coefficient diagram. -/
def categoryBarHomComplexFunctor :
    CoefficientCategory R C ⥤ CochainComplex (ModuleCat.{u} R) ℕ where
  obj M := (categoryBarComplex R C).linearYonedaObj R M
  map := categoryBarHomComplexMap
  map_id M := by
    apply HomologicalComplex.Hom.ext
    funext n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro α
    change α ≫ 𝟙 M = α
    exact Category.comp_id _
  map_comp a b := by
    apply HomologicalComplex.Hom.ext
    funext n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro α
    change α ≫ (a ≫ b) = (α ≫ a) ≫ b
    exact (Category.assoc _ _ _).symm

/-- The bar/coefficient cochain identification is natural in all coefficient
maps; it is not merely an objectwise isomorphism of cohomology groups. -/
def categoryBarHomComplexNatIso :
    categoryBarHomComplexFunctor (R := R) (C := C) ≅ coefficientCochainFunctor :=
  NatIso.ofComponents categoryBarHomComplexIso (by
    intro M N a
    apply HomologicalComplex.Hom.ext
    funext n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro α
    rfl)

end Sharpness.Unconditional
