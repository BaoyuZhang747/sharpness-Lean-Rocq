import Sharpness.ModuleDirectSumMaps
import Mathlib.CategoryTheory.Linear.Basic

/-! Applying Hom_R(-,A) to the actual infinite module direct sum gives
the actual product of Hom modules, with its summand formula. There is
no finite-generation, projectivity or injectivity condition on A. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness
open CategoryTheory
variable {R : Type u} [CommRing R] {ι : Type u}
    (M : ι → ModuleCat.{u} R) (A : ModuleCat.{u} R)

def moduleDirectSumHomEquiv : (moduleDirectSum M ⟶ A) ≃ₗ[R] ∀ i, M i ⟶ A where
  toFun f i := moduleDirectSumInclusion M i ≫ f
  invFun := moduleDirectSumDesc M
  left_inv f := by
    apply moduleDirectSum_hom_ext
    intro i
    exact moduleDirectSumInclusion_desc M _ i
  right_inv f := funext (moduleDirectSumInclusion_desc M f)
  map_add' f g := by
    funext i
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl
  map_smul' r f := by
    funext i
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl

theorem moduleDirectSumHomEquiv_component (f : moduleDirectSum M ⟶ A) (i : ι) :
    moduleDirectSumHomEquiv M A f i = moduleDirectSumInclusion M i ≫ f := rfl

end Sharpness
