import Sharpness.SingularCochains

/-! Actual singular cochains are contravariantly functorial in the
space and covariantly natural in the arbitrary coefficient module. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness.SingularCohomology
open CategoryTheory Opposite
variable (R : Type u) [CommRing R]

def cochainFunctor (A : ModuleCat.{u} R) :
    TopCat.{u}ᵒᵖ ⥤ CochainComplex (ModuleCat.{u} R) ℕ where
  obj X := cochains R X.unop A
  map f := cochainPull R f.unop A
  map_id X := cochainPull_id R X.unop A
  map_comp f g := cochainPull_comp R g.unop f.unop A

def cohomologyFunctor (A : ModuleCat.{u} R) (n : ℕ) : TopCat.{u}ᵒᵖ ⥤ ModuleCat.{u} R :=
  cochainFunctor R A ⋙ HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℕ) n

def chainDualCoefficientMap (K : ChainComplex (ModuleCat.{u} R) ℕ)
    {A B : ModuleCat.{u} R} (a : A ⟶ B) : K.linearYonedaObj R A ⟶ K.linearYonedaObj R B where
  f n := ModuleCat.ofHom (Linear.rightComp R _ a)
  comm' i j _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    change (K.d j i ≫ z) ≫ a = K.d j i ≫ (z ≫ a)
    exact Category.assoc _ _ _

theorem chainDualCoefficientMap_component (K : ChainComplex (ModuleCat.{u} R) ℕ)
    {A B : ModuleCat.{u} R} (a : A ⟶ B) (n : ℕ) (z : K.X n ⟶ A) :
    (chainDualCoefficientMap R K a).f n z = z ≫ a := rfl

def coefficientNatTrans {A B : ModuleCat.{u} R} (a : A ⟶ B) :
    cochainFunctor R A ⟶ cochainFunctor R B where
  app X := chainDualCoefficientMap R ((chainsFunctor R).obj X.unop) a
  naturality {X Y} f := by
    apply HomologicalComplex.Hom.ext
    funext n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    change (((chainsFunctor R).map f.unop).f n ≫ z) ≫ a =
      ((chainsFunctor R).map f.unop).f n ≫ (z ≫ a)
    exact Category.assoc _ _ _

end Sharpness.SingularCohomology
