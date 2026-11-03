import Sharpness.Unconditional.InducedCategoryBarResolution
import Sharpness.Unconditional.CategoryBarCalculation

/-! Naturality of the actual induced-bar comparison in all coefficient maps. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
noncomputable section
universe u
namespace Sharpness.Unconditional
open CategoryTheory CategoryTheory.Limits Opposite
variable {R C D : Type u} [CommRing R] [Category.{u} C] [Category.{u} D]
  {q : C ⥤ D}

/-- Coefficient maps act on bar Hom complexes by postcomposition. -/
def inducedCategoryBarHomComplexMap {M N : CoefficientCategory R D} (a : M ⟶ N) :
    (inducedCategoryBarComplex R q).linearYonedaObj R M ⟶
      (inducedCategoryBarComplex R q).linearYonedaObj R N where
  f n := ModuleCat.ofHom (Linear.rightComp R _ a)
  comm' i j hij := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro α
    change (inducedCategoryBarComplex R q).d j i ≫ (α ≫ a) =
      ((inducedCategoryBarComplex R q).d j i ≫ α) ≫ a
    exact (Category.assoc _ _ _).symm

/-- The bar Hom complex is functorial in the coefficient diagram. -/
def inducedCategoryBarHomComplexFunctor :
    CoefficientCategory R D ⥤ CochainComplex (ModuleCat.{u} R) ℕ where
  obj M := (inducedCategoryBarComplex R q).linearYonedaObj R M
  map := inducedCategoryBarHomComplexMap
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
def inducedCategoryBarHomComplexNatIso :
    inducedCategoryBarHomComplexFunctor (R := R) (q := q) ≅ restrictionCoefficientFunctor R q ⋙ coefficientCochainFunctor :=
  NatIso.ofComponents (inducedCategoryBarHomComplexIso q) (by
    intro M N a
    apply HomologicalComplex.Hom.ext
    funext n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro α
    rfl)



variable [QuasiIso (inducedCategoryBarAugmentationChain R q)]

def inducedCategoryBarExtIso (M : CoefficientCategory R D) (n : ℕ) :
    higherLimit M n ≅ ((inducedCategoryBarComplex R q).linearYonedaObj R M).homology n :=
  (inducedCategoryBarResolution R q).isoExt n M

set_option maxHeartbeats 800000 in
theorem inducedCategoryBarExtIso_naturality {M N : CoefficientCategory R D} (a : M ⟶ N) (n : ℕ) :
    (higherLimitFunctor R D n).map a ≫ (inducedCategoryBarExtIso (q := q) N n).hom =
      (inducedCategoryBarExtIso (q := q) M n).hom ≫
        HomologicalComplex.homologyMap (inducedCategoryBarHomComplexMap a) n := by
  change ((((linearYoneda R (CoefficientCategory R D)).map a).rightOp.leftDerived n).app
    (constantCoefficient R D)).unop ≫ _ = _
  rw [(inducedCategoryBarResolution R q).leftDerived_app_eq
    ((linearYoneda R (CoefficientCategory R D)).map a).rightOp n]
  dsimp [inducedCategoryBarExtIso, ProjectiveResolution.isoExt]
  simp only [unop_comp, Category.assoc, ← Iso.unop_hom, ← Iso.unop_inv,
    Iso.hom_inv_id_assoc]
  congr 1
  have h := (HomologicalComplex.homologyOpNatIso (ModuleCat.{u} R)
    (ComplexShape.up ℕ) n).inv.naturality (inducedCategoryBarHomComplexMap (q := q) a).op
  exact (congrArg Quiver.Hom.unop h).symm

def inducedCategoryBarExtNatIso (n : ℕ) :
    higherLimitFunctor R D n ≅
      inducedCategoryBarHomComplexFunctor (R := R) (q := q) ⋙
        HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℕ) n :=
  NatIso.ofComponents (fun M => inducedCategoryBarExtIso M n) (by
    intro M N a
    exact inducedCategoryBarExtIso_naturality a n)

/-- The comparison is natural for arbitrary coefficient diagrams. -/
def higherLimitNatIsoOfInducedBarAugmentation (q : C ⥤ D)
    [QuasiIso (inducedCategoryBarAugmentationChain R q)] (n : ℕ) :
    higherLimitFunctor R D n ≅
      restrictionCoefficientFunctor R q ⋙ higherLimitFunctor R C n :=
  inducedCategoryBarExtNatIso n ≪≫
    Functor.isoWhiskerRight inducedCategoryBarHomComplexNatIso
      (HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℕ) n) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (restrictionCoefficientFunctor R q)
      (categoryBarCohomologyNatIso n).symm

end Sharpness.Unconditional
