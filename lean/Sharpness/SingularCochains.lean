import Sharpness.HigherLimits
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Algebra.Homology.Linear

/-! Actual singular cochains with arbitrary constant module coefficients:
C^n(X;A) = Hom_R(C_n(X;R),A). Topological pullback is induced from
the actual singular-chain functor, not an unspecified cohomology map. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness.SingularCohomology
open CategoryTheory CategoryTheory.Limits
variable (R : Type u) [CommRing R]

abbrev chainsFunctor : TopCat.{u} ⥤ ChainComplex (ModuleCat.{u} R) ℕ :=
  (AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{u} R)).obj (ModuleCat.of R R)

def cochains (X : TopCat.{u}) (A : ModuleCat.{u} R) : CochainComplex (ModuleCat.{u} R) ℕ :=
  ((chainsFunctor R).obj X).linearYonedaObj R A

def chainDualMap {K L : ChainComplex (ModuleCat.{u} R) ℕ} (f : K ⟶ L) (A : ModuleCat.{u} R) :
    L.linearYonedaObj R A ⟶ K.linearYonedaObj R A :=
  (HomologicalComplex.unopFunctor (ModuleCat.{u} R) (ComplexShape.down ℕ)).map
    (((((linearYoneda R (ModuleCat.{u} R)).obj A).rightOp.mapHomologicalComplex
      (ComplexShape.down ℕ)).map f).op)

theorem chainDualMap_component {K L : ChainComplex (ModuleCat.{u} R) ℕ} (f : K ⟶ L)
    (A : ModuleCat.{u} R) (n : ℕ) (a : L.X n ⟶ A) :
    (chainDualMap R f A).f n a = f.f n ≫ a := rfl

def cochainPull {X Y : TopCat.{u}} (f : X ⟶ Y) (A : ModuleCat.{u} R) :
    cochains R Y A ⟶ cochains R X A :=
  chainDualMap R ((chainsFunctor R).map f) A

theorem cochainPull_id (X : TopCat.{u}) (A : ModuleCat.{u} R) :
    cochainPull R (𝟙 X) A = 𝟙 _ := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  change ((chainsFunctor R).map (𝟙 X)).f n ≫ a = a
  rw [(chainsFunctor R).map_id]
  exact Category.id_comp a

theorem cochainPull_comp {X Y Z : TopCat.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (A : ModuleCat.{u} R) : cochainPull R (f ≫ g) A = cochainPull R g A ≫ cochainPull R f A := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  change ((chainsFunctor R).map (f ≫ g)).f n ≫ a =
    ((chainsFunctor R).map f).f n ≫ (((chainsFunctor R).map g).f n ≫ a)
  rw [(chainsFunctor R).map_comp]
  exact Category.assoc _ _ _

def cohomology (X : TopCat.{u}) (A : ModuleCat.{u} R) (n : ℕ) : ModuleCat.{u} R :=
  (cochains R X A).homology n

def pull {X Y : TopCat.{u}} (f : X ⟶ Y) (A : ModuleCat.{u} R) (n : ℕ) :
    cohomology R Y A n ⟶ cohomology R X A n :=
  HomologicalComplex.homologyMap (cochainPull R f A) n

theorem pull_id (X : TopCat.{u}) (A : ModuleCat.{u} R) (n : ℕ) :
    pull R (𝟙 X) A n = 𝟙 _ := by
  rw [pull, cochainPull_id, HomologicalComplex.homologyMap_id]
  rfl

theorem pull_comp {X Y Z : TopCat.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (A : ModuleCat.{u} R) (n : ℕ) :
    pull R (f ≫ g) A n = pull R g A n ≫ pull R f A n := by
  rw [pull, cochainPull_comp, HomologicalComplex.homologyMap_comp]
  rfl

end Sharpness.SingularCohomology
