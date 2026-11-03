import Sharpness.RealizationUnitCochains
import Sharpness.SingularCochainFunctor
import Sharpness.ChainDualFunctor

/-! Naturality of the actual realization-unit cochain map, in the
simplicial set and in every constant coefficient module. These
equalities do not require the unit to be a quasi-isomorphism. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace Sharpness
open CategoryTheory
variable (R : Type u) [CommRing R]

theorem realizationUnitChainMap_naturality {X Y : SSet.{u}} (f : X ⟶ Y) :
    (simplicialChainsFunctor R).map f ≫ realizationUnitChainMap R Y =
      realizationUnitChainMap R X ≫
        (SingularCohomology.chainsFunctor R).map (SSet.toTop.map f) := by
  calc
    _ = (simplicialChainsFunctor R).map (f ≫ realizationSingularUnit Y) :=
      ((simplicialChainsFunctor R).map_comp _ _).symm
    _ = (simplicialChainsFunctor R).map
        (realizationSingularUnit X ≫ realizationSingularFunctor.map f) :=
      congrArg (fun t => (simplicialChainsFunctor R).map t)
        (realizationSingularUnit_naturality f)
    _ = _ := (simplicialChainsFunctor R).map_comp _ _

theorem realizationUnitCochainMap_naturality {X Y : SSet.{u}} (f : X ⟶ Y)
    (A : ModuleCat.{u} R) :
    SingularCohomology.cochainPull R (SSet.toTop.map f) A ≫
        realizationUnitCochainMap R X A =
      realizationUnitCochainMap R Y A ≫
        SingularCohomology.chainDualMap R ((simplicialChainsFunctor R).map f) A := by
  change SingularCohomology.chainDualMap R _ A ≫
      SingularCohomology.chainDualMap R _ A =
    SingularCohomology.chainDualMap R _ A ≫ SingularCohomology.chainDualMap R _ A
  rw [← SingularCohomology.chainDualMap_comp, ← SingularCohomology.chainDualMap_comp,
    realizationUnitChainMap_naturality]

theorem realizationUnitCochainMap_coefficient (X : SSet.{u})
    {A B : ModuleCat.{u} R} (a : A ⟶ B) :
    SingularCohomology.chainDualCoefficientMap R
        ((SingularCohomology.chainsFunctor R).obj (SSet.toTop.obj X)) a ≫
        realizationUnitCochainMap R X B =
      realizationUnitCochainMap R X A ≫
        SingularCohomology.chainDualCoefficientMap R (X.chainComplex (ModuleCat.of R R)) a := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  change (realizationUnitChainMap R X).f n ≫ (z ≫ a) =
    ((realizationUnitChainMap R X).f n ≫ z) ≫ a
  exact (Category.assoc _ _ _).symm

end Sharpness
