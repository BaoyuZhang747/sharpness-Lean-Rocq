import Sharpness.Unconditional.NerveOppositeChainsSimplicial
import Sharpness.Unconditional.NerveOppositeChainsSigns
import Mathlib.Algebra.Homology.QuasiIso

/-! Actual signed opposite-nerve chain isomorphisms and quasi-isomorphism transport. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe w v u vA uA

namespace Sharpness
open CategoryTheory CategoryTheory.Limits Simplicial Opposite

variable {A : Type uA} [Category.{vA} A] [Preadditive A]

def simplicialOpChainIso [HasCoproducts.{w} A] (X : SSet.{w}) (R : A) :
    X.op.chainComplex R ≅ X.chainComplex R :=
  alternatingFaceMapComplexOpIso (X ⋙ sigmaConst.obj R)

theorem simplicialOpChainIso_naturality [HasCoproducts.{w} A]
    {X Y : SSet.{w}} (f : X ⟶ Y) (R : A) :
    SSet.chainComplexMap (SSet.opFunctor.map f) R ≫ (simplicialOpChainIso Y R).hom =
      (simplicialOpChainIso X R).hom ≫ SSet.chainComplexMap f R :=
  alternatingFaceMapComplexOpIso_naturality (((Functor.whiskeringRight _ _ _).obj (sigmaConst.obj R)).map f)

variable {C D : Type u} [Category.{v} C] [Category.{v} D]
variable [HasCoproducts.{max u v} A]

def nerveOppositeChainIso (C : Type u) [Category.{v} C] (R : A) :
    (nerve Cᵒᵖ).chainComplex R ≅ (nerve C).chainComplex R :=
  ((SSet.chainComplexFunctor A).obj R).mapIso (nerveOppositeSimplicialIso C) ≪≫
    simplicialOpChainIso (nerve C) R

theorem nerveOppositeChainIso_naturality (T : C ⥤ D) (R : A) :
    SSet.chainComplexMap (nerveMap T.op) R ≫ (nerveOppositeChainIso D R).hom =
      (nerveOppositeChainIso C R).hom ≫ SSet.chainComplexMap (nerveMap T) R := by
  let J := (SSet.chainComplexFunctor A).obj R
  change J.map (nerveMap T.op) ≫
      (J.map (nerveOppositeSimplicialIso D).hom ≫ (simplicialOpChainIso (nerve D) R).hom) =
    (J.map (nerveOppositeSimplicialIso C).hom ≫ (simplicialOpChainIso (nerve C) R).hom) ≫
      J.map (nerveMap T)
  rw [← Category.assoc, ← J.map_comp, nerveOppositeSimplicialIso_naturality,
    J.map_comp, Category.assoc, simplicialOpChainIso_naturality, Category.assoc]

theorem nerveOppositeChainMap_quasiIso_iff [CategoryWithHomology A]
    (T : C ⥤ D) (R : A) :
    QuasiIso (SSet.chainComplexMap (nerveMap T.op) R) ↔
      QuasiIso (SSet.chainComplexMap (nerveMap T) R) := by
  constructor
  · intro h
    letI := h
    haveI : QuasiIso (SSet.chainComplexMap (nerveMap T.op) R ≫
        (nerveOppositeChainIso D R).hom) := inferInstance
    rw [nerveOppositeChainIso_naturality] at this
    exact quasiIso_of_comp_left (nerveOppositeChainIso C R).hom
      (SSet.chainComplexMap (nerveMap T) R)
  · intro h
    letI := h
    haveI : QuasiIso ((nerveOppositeChainIso C R).hom ≫
        SSet.chainComplexMap (nerveMap T) R) := inferInstance
    rw [← nerveOppositeChainIso_naturality] at this
    exact quasiIso_of_comp_right (SSet.chainComplexMap (nerveMap T.op) R)
      (nerveOppositeChainIso D R).hom

end Sharpness
