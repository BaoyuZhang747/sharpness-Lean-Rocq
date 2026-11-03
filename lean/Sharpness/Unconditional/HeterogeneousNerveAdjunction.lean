import Sharpness.Unconditional.HeterogeneousNerve
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.Algebra.Homology.QuasiIso

/-! Chain homotopy equivalence for an actual adjunction between categories
with different object universes, including one-object group categories. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u v w a b
namespace Sharpness
open CategoryTheory CategoryTheory.Limits
variable {C : Type u} {D : Type v}
    [Category.{max u v w} C] [Category.{max u v w} D]
    {A : Type a} [Category.{b} A] [Preadditive A] [HasCoproducts.{max u v w} A]
    {T : C ⥤ D} {U : D ⥤ C}

def heterogeneousNerveAdjunctionChainHomotopyEquiv (adj : T ⊣ U) (R : A) :
    HomotopyEquiv ((nerve C).chainComplex R) ((nerve D).chainComplex R) where
  hom := SSet.chainComplexMap (heterogeneousNerveMap.{u,v,w} T) R
  inv := SSet.chainComplexMap (heterogeneousNerveMap.{v,u,w} U) R
  homotopyHomInvId := by
    have h := (nerveNaturalTransformationChainHomotopy adj.unit R).symm
    have hc : SSet.chainComplexMap (nerveMap (T ⋙ U)) R =
        SSet.chainComplexMap (heterogeneousNerveMap.{u,v,w} T) R ≫
          SSet.chainComplexMap (heterogeneousNerveMap.{v,u,w} U) R :=
      ((SSet.chainComplexFunctor A).obj R).map_comp
        (heterogeneousNerveMap.{u,v,w} T) (heterogeneousNerveMap.{v,u,w} U)
    have hi : SSet.chainComplexMap (nerveMap (𝟭 C)) R = 𝟙 ((nerve C).chainComplex R) :=
      ((SSet.chainComplexFunctor A).obj R).map_id (nerve C)
    simpa only [hc, hi] using h
  homotopyInvHomId := by
    have h := nerveNaturalTransformationChainHomotopy adj.counit R
    have hc : SSet.chainComplexMap (nerveMap (U ⋙ T)) R =
        SSet.chainComplexMap (heterogeneousNerveMap.{v,u,w} U) R ≫
          SSet.chainComplexMap (heterogeneousNerveMap.{u,v,w} T) R :=
      ((SSet.chainComplexFunctor A).obj R).map_comp
        (heterogeneousNerveMap.{v,u,w} U) (heterogeneousNerveMap.{u,v,w} T)
    have hi : SSet.chainComplexMap (nerveMap (𝟭 D)) R = 𝟙 ((nerve D).chainComplex R) :=
      ((SSet.chainComplexFunctor A).obj R).map_id (nerve D)
    simpa only [hc, hi] using h

theorem heterogeneousNerveAdjunction_left_quasiIso [CategoryWithHomology A]
    (adj : T ⊣ U) (R : A) :
    QuasiIso (SSet.chainComplexMap (heterogeneousNerveMap.{u,v,w} T) R) :=
  (heterogeneousNerveAdjunctionChainHomotopyEquiv adj R).quasiIso_hom

theorem heterogeneousNerveAdjunction_right_quasiIso [CategoryWithHomology A]
    (adj : T ⊣ U) (R : A) :
    QuasiIso (SSet.chainComplexMap (heterogeneousNerveMap.{v,u,w} U) R) :=
  (heterogeneousNerveAdjunctionChainHomotopyEquiv adj R).quasiIso_inv

end Sharpness
