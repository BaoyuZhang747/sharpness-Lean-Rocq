import Sharpness.Unconditional.NerveNaturalTransformation
import Sharpness.CostructuredGrothendieckAdjunction
import Mathlib.Algebra.Homology.QuasiIso

/-! Actual nerve-chain homotopy equivalences induced by an adjunction.
This is an algebraic consequence of the constructed nerve prism, independent
of realization and of any topological comparison input. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u v w z
namespace Sharpness
open CategoryTheory CategoryTheory.Limits

variable {C D : Type u} [Category.{v} C] [Category.{v} D]
    {A : Type w} [Category.{z} A] [Preadditive A] [HasCoproducts.{max u v} A]
    {T : C ⥤ D} {U : D ⥤ C}

/-- The actual nerve maps of the two adjoints are mutually inverse up to
the chain homotopies induced by their unit and counit. -/
def nerveAdjunctionChainHomotopyEquiv (adj : T ⊣ U) (R : A) :
    HomotopyEquiv ((nerve C).chainComplex R) ((nerve D).chainComplex R) where
  hom := SSet.chainComplexMap (nerveMap T) R
  inv := SSet.chainComplexMap (nerveMap U) R
  homotopyHomInvId := by
    have h := (nerveNaturalTransformationChainHomotopy adj.unit R).symm
    have hc : SSet.chainComplexMap (nerveMap (T ⋙ U)) R =
        SSet.chainComplexMap (nerveMap T) R ≫ SSet.chainComplexMap (nerveMap U) R :=
      ((SSet.chainComplexFunctor A).obj R).map_comp (nerveMap T) (nerveMap U)
    have hi : SSet.chainComplexMap (nerveMap (𝟭 C)) R = 𝟙 ((nerve C).chainComplex R) :=
      ((SSet.chainComplexFunctor A).obj R).map_id (nerve C)
    simpa only [hc, hi] using h
  homotopyInvHomId := by
    have h := nerveNaturalTransformationChainHomotopy adj.counit R
    have hc : SSet.chainComplexMap (nerveMap (U ⋙ T)) R =
        SSet.chainComplexMap (nerveMap U) R ≫ SSet.chainComplexMap (nerveMap T) R :=
      ((SSet.chainComplexFunctor A).obj R).map_comp (nerveMap U) (nerveMap T)
    have hi : SSet.chainComplexMap (nerveMap (𝟭 D)) R = 𝟙 ((nerve D).chainComplex R) :=
      ((SSet.chainComplexFunctor A).obj R).map_id (nerve D)
    simpa only [hc, hi] using h

theorem nerveAdjunction_left_quasiIso [CategoryWithHomology A]
    (adj : T ⊣ U) (R : A) : QuasiIso (SSet.chainComplexMap (nerveMap T) R) :=
  (nerveAdjunctionChainHomotopyEquiv adj R).quasiIso_hom

theorem nerveAdjunction_right_quasiIso [CategoryWithHomology A]
    (adj : T ⊣ U) (R : A) : QuasiIso (SSet.chainComplexMap (nerveMap U) R) :=
  (nerveAdjunctionChainHomotopyEquiv adj R).quasiIso_inv

end Sharpness
