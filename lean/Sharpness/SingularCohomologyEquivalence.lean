import Sharpness.SingularCohomologyHomotopy
import Sharpness.SingularCochainFunctor

/-! Homotopy inverses of actual space maps induce inverse native
cohomology maps, for every constant coefficient module. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness.SingularCohomology
open CategoryTheory
variable (R : Type u) [CommRing R]

def pullIsoOfHomotopyInverse {X Y : TopCat.{u}} (f : X ⟶ Y) (g : Y ⟶ X)
    (hX : TopCat.Homotopy (f ≫ g) (𝟙 X))
    (hY : TopCat.Homotopy (g ≫ f) (𝟙 Y)) (A : ModuleCat.{u} R) (n : ℕ) :
    cohomology R Y A n ≅ cohomology R X A n where
  hom := pull R f A n
  inv := pull R g A n
  hom_inv_id := by
    rw [← pull_comp]
    exact (pull_eq_of_homotopy R hY A n).trans (pull_id R Y A n)
  inv_hom_id := by
    rw [← pull_comp]
    exact (pull_eq_of_homotopy R hX A n).trans (pull_id R X A n)

def cohomologyCoefficientMap (X : TopCat.{u}) {A B : ModuleCat.{u} R}
    (a : A ⟶ B) (n : ℕ) : cohomology R X A n ⟶ cohomology R X B n :=
  HomologicalComplex.homologyMap (chainDualCoefficientMap R ((chainsFunctor R).obj X) a) n

theorem pull_coefficientMap {X Y : TopCat.{u}} (f : X ⟶ Y)
    {A B : ModuleCat.{u} R} (a : A ⟶ B) (n : ℕ) :
    pull R f A n ≫ cohomologyCoefficientMap R X a n =
      cohomologyCoefficientMap R Y a n ≫ pull R f B n := by
  have h := (coefficientNatTrans R a).naturality f.op
  have hh := congrArg (fun t => HomologicalComplex.homologyMap t n) h
  simp only [HomologicalComplex.homologyMap_comp] at hh
  exact hh

end Sharpness.SingularCohomology
