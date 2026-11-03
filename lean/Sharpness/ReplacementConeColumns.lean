import Sharpness.ProductCochainLifts
import Sharpness.CategoryCochainReplacementLaws
import Sharpness.AlternatingCofaceCoaugmentation

/-! A genuine cone of cochain maps gives compatible maps to every
replacement column. In particular its column-zero map is killed by
the actual horizontal differential. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness
open CategoryTheory Simplicial Opposite
variable {R C : Type u} [CommRing R] [Category.{u} C]
    (D : Cᵒᵖ ⥤ CochainComplex (ModuleCat.{u} R) ℕ)
    {A : CochainComplex (ModuleCat.{u} R) ℕ}
    (a : (Functor.const Cᵒᵖ).obj A ⟶ D)

def replacementConeColumnMap (i : SimplexCategory) : A ⟶ cochainReplacementColumn D i :=
  productCochainsLift (fun s : ComposableArrows C i.len => D.obj (op (chainHead s)))
    (fun s => a.app (op (chainHead s)))

theorem replacementConeColumnMap_naturality {i j : SimplexCategory} (f : i ⟶ j) :
    replacementConeColumnMap D a i ≫ cochainReplacementMap D f = replacementConeColumnMap D a j := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  funext s
  have h : a.app (op (chainHead (restrictCategoryChain f s))) ≫
      D.map (categoryChainHeadArrow f s).op = a.app (op (chainHead s)) :=
    (a.naturality (categoryChainHeadArrow f s).op).symm.trans (Category.id_comp _)
  exact congrArg (fun t => t.f n x) h

theorem replacementConeColumnMap_horizontal_zero :
    replacementConeColumnMap D a ⦋0⦌ ≫ (cochainReplacementBicomplex D).d 0 1 = 0 := by
  exact alternatingCoface_coaugmentation_zero (cochainReplacement D)
    (replacementConeColumnMap D a ⦋0⦌) (replacementConeColumnMap D a ⦋1⦌)
      (replacementConeColumnMap_naturality D a (SimplexCategory.δ (0 : Fin 2)))
      (replacementConeColumnMap_naturality D a (SimplexCategory.δ (1 : Fin 2)))

theorem replacementConeColumnMap_projection (i : SimplexCategory) (s : ComposableArrows C i.len) :
    replacementConeColumnMap D a i ≫
      productCochainsProjection (fun t : ComposableArrows C i.len => D.obj (op (chainHead t))) s =
    a.app (op (chainHead s)) :=
  productCochainsLift_projection _ _ s

end Sharpness
