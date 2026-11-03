import Sharpness.Unconditional.InducedCategoryBarComparison
import Sharpness.Unconditional.CategoryBarExt

/-! An acyclic actual induced bar augmentation gives a projective resolution
and hence the all-degree restriction comparison for arbitrary coefficients.
The augmentation condition is discharged separately by its actual comma nerve.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace Sharpness.Unconditional
open CategoryTheory CategoryTheory.Limits Opposite
variable (R : Type u) [CommRing R] {C D : Type u}
  [Category.{u} C] [Category.{u} D] (q : C ⥤ D)

/-- The actual induced bar complex is a resolution when its actual
augmentation is a quasi-isomorphism. No exactness of a Kan functor is used. -/
def inducedCategoryBarResolution [QuasiIso (inducedCategoryBarAugmentationChain R q)] :
    ProjectiveResolution (constantCoefficient R D) where
  complex := inducedCategoryBarComplex R q
  π := inducedCategoryBarAugmentationChain R q

/-- All-degree comparison, computed from the induced projective bar resolution
and the ordinary bar resolution on the source category. -/
def higherLimitIsoOfInducedBarAugmentation
    [QuasiIso (inducedCategoryBarAugmentationChain R q)]
    (M : CoefficientCategory R D) (n : ℕ) :
    higherLimit M n ≅ higherLimit (q.op ⋙ M) n :=
  (inducedCategoryBarResolution R q).isoExt n M ≪≫
    (HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℕ) n).mapIso
      (inducedCategoryBarHomComplexIso q M) ≪≫
    (categoryBarCohomologyIso (q.op ⋙ M) n).symm

end Sharpness.Unconditional
