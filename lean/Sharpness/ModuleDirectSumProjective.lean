import Sharpness.ModuleDirectSumMaps
import Mathlib.Algebra.Category.ModuleCat.Products
import Mathlib.Algebra.Category.ModuleCat.Projective

/-! Projectivity of the concrete direct sums used in chain replacement.
The lift is built from the lifts on all actual summands. -/
set_option autoImplicit false
noncomputable section
universe u v
namespace Sharpness
open CategoryTheory CategoryTheory.Limits
variable {R : Type u} [CommRing R] {ι : Type v}
    (M : ι → ModuleCat.{max u v} R)

theorem moduleDirectSum_projective [∀ i, Projective (M i)] :
    Projective (moduleDirectSum M) where
  factors f e _ := by
    refine ⟨moduleDirectSumDesc M (fun i =>
      Projective.factorThru (moduleDirectSumInclusion M i ≫ f) e), ?_⟩
    apply moduleDirectSum_hom_ext
    intro i
    rw [← Category.assoc, moduleDirectSumInclusion_desc, Projective.factorThru_comp]

end Sharpness
