import Sharpness.ReplacementConeColumns
import Sharpness.ZeroColumnTotalMap

/-! Actual augmentation of a replacement total complex by a cone of
cochain maps. Its projection onto every column-zero factor is exactly
the corresponding cone map in every cochain degree. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness
open CategoryTheory Simplicial Opposite
variable {R C : Type u} [CommRing R] [Category.{u} C]
    (D : Cᵒᵖ ⥤ CochainComplex (ModuleCat.{u} R) ℕ)
    {A : CochainComplex (ModuleCat.{u} R) ℕ}
    (a : (Functor.const Cᵒᵖ).obj A ⟶ D)

def replacementConeAugmentation : A ⟶ cochainReplacementTotal D :=
  zeroColumnTotalMap (cochainReplacementBicomplex D) (replacementConeColumnMap D a ⦋0⦌)
    (replacementConeColumnMap_horizontal_zero D a)

set_option backward.isDefEq.respectTransparency false in
theorem replacementConeAugmentation_projection (n : ℕ) (s : ComposableArrows C 0) :
    (replacementConeAugmentation D a).f n ≫
      totalSummandProjectionAt (cochainReplacementBicomplex D) 0 n n (by omega) ≫
        (productCochainsProjection (fun t : ComposableArrows C 0 => D.obj (op (chainHead t))) s).f n =
    (a.app (op (chainHead s))).f n := by
  have h := zeroColumnTotalMap_projection (cochainReplacementBicomplex D)
    (replacementConeColumnMap D a ⦋0⦌) (replacementConeColumnMap_horizontal_zero D a) n
  have hπ := HomologicalComplex.congr_hom (replacementConeColumnMap_projection D a ⦋0⦌ s) n
  calc
    _ = (replacementConeColumnMap D a ⦋0⦌).f n ≫
        (productCochainsProjection (fun t : ComposableArrows C 0 => D.obj (op (chainHead t))) s).f n :=
      (Category.assoc _ _ _).symm.trans
        (congrArg (fun t => t ≫
          (productCochainsProjection (fun t : ComposableArrows C 0 => D.obj (op (chainHead t))) s).f n) h)
    _ = _ := hπ

end Sharpness
