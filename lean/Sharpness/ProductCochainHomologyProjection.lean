import Sharpness.ProductCochainHomology
import Sharpness.ProductCochainLifts
import Sharpness.PiHomologyClasses

/-! Every component of the actual product-cochain cohomology
comparison is the native homology map of the actual projection. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace Sharpness
open CategoryTheory
variable {R ι : Type u} [CommRing R]
    (K : ι → CochainComplex (ModuleCat.{u} R) ℕ)

theorem productCochainsHomologyIso_projection (n : ℕ) (i : ι) :
    (productCochainsHomologyIso K n).hom ≫ ModuleCat.ofHom (LinearMap.proj i) =
      HomologicalComplex.homologyMap (productCochainsProjection K i) n := by
  have hc : (productCochainsShortComplexIso K n).hom ≫
      piShortComplexProjection (fun j => (K j).sc n) i =
    (HomologicalComplex.shortComplexFunctor (ModuleCat.{u} R) (ComplexShape.up ℕ) n).map
      (productCochainsProjection K i) := by
    apply ShortComplex.hom_ext <;> rfl
  calc
    _ = ShortComplex.homologyMap (productCochainsShortComplexIso K n).hom ≫
        ((piShortComplexHomologyIso (fun j => (K j).sc n)).hom ≫
          ModuleCat.ofHom (LinearMap.proj i)) := by
      simp only [productCochainsHomologyIso, Iso.trans_hom, Category.assoc]
      rfl
    _ = ShortComplex.homologyMap (productCochainsShortComplexIso K n).hom ≫
        ShortComplex.homologyMap (piShortComplexProjection (fun j => (K j).sc n) i) := by
      rw [piShortComplexHomologyIso_projection]
    _ = _ := by rw [← ShortComplex.homologyMap_comp, hc]; rfl

end Sharpness
