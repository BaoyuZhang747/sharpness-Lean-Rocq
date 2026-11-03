import Sharpness.ReplacementConeAugmentation
import Sharpness.ZeroColumnTotalProjection

/-! Projection of the actual augmented total complex onto each
column-zero factor is an equality of entire cochain maps. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness
open CategoryTheory Simplicial Opposite
variable {R C : Type u} [CommRing R] [Category.{u} C]
    (D : Cᵒᵖ ⥤ CochainComplex (ModuleCat.{u} R) ℕ)

def replacementTotalProjection (s : ComposableArrows C 0) :
    cochainReplacementTotal D ⟶ D.obj (op (chainHead s)) :=
  zeroColumnTotalProjection (cochainReplacementBicomplex D) ≫
    productCochainsProjection (fun t : ComposableArrows C 0 => D.obj (op (chainHead t))) s

set_option backward.isDefEq.respectTransparency false in
theorem replacementConeAugmentation_comp_projection {A : CochainComplex (ModuleCat.{u} R) ℕ}
    (a : (Functor.const Cᵒᵖ).obj A ⟶ D) (s : ComposableArrows C 0) :
    replacementConeAugmentation D a ≫ replacementTotalProjection D s = a.app (op (chainHead s)) := by
  apply HomologicalComplex.Hom.ext
  funext n
  exact replacementConeAugmentation_projection D a n s

end Sharpness
