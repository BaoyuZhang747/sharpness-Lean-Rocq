import Sharpness.SingularCochains
import Mathlib.Algebra.Category.ModuleCat.Projective

/-! Actual singular chain modules are projective: in each degree they
are the chosen coproduct of copies of the free rank-one module R. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness.SingularCohomology
open CategoryTheory CategoryTheory.Limits Simplicial
variable (R : Type u) [CommRing R]

theorem simplicialChains_projective (X : SSet.{u}) (n : ℕ) :
    Projective ((X.chainComplex (ModuleCat.of R R)).X n) := by
  change Projective (∐ fun _ : X.obj (Opposite.op ⦋n⦌) => ModuleCat.of R R)
  infer_instance

theorem chainsFunctor_projective (X : TopCat.{u}) (n : ℕ) :
    Projective (((chainsFunctor R).obj X).X n) :=
  simplicialChains_projective R (TopCat.toSSet.obj X) n

end Sharpness.SingularCohomology
