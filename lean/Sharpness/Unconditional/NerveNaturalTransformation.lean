import Mathlib.AlgebraicTopology.SimplicialSet.Nerve
import Mathlib.AlgebraicTopology.SimplicialSet.Homology.HomotopyInvariance
import Mathlib.CategoryTheory.Functor.Currying

/-! The actual simplicial prism induced by a natural transformation. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

universe v u w z

open CategoryTheory CategoryTheory.Limits Simplicial Opposite MonoidalCategory

namespace Sharpness

variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  {T U : C ⥤ D}

/-- The categorical cylinder functor associated to a natural transformation. -/
def naturalTransformationCylinder (α : T ⟶ U) : Fin 2 × C ⥤ D :=
  Functor.uncurry.obj (ComposableArrows.mk₁ α)

/-- At each simplex, evaluate the categorical cylinder on its order-preserving
map to the ordinal `[1]` and on its chain in `C`. -/
def nerveNaturalTransformationMap (α : T ⟶ U) : nerve C ⊗ Δ[1] ⟶ nerve D where
  app n := ↾fun x =>
    ((SimplexCategory.toCat.map (SSet.stdSimplex.objEquiv x.2)).toFunctor.prod' x.1) ⋙
      naturalTransformationCylinder α
  naturality := by
    intro n m f
    ext x
    rfl

theorem nerveNaturalTransformationMap_zero (α : T ⟶ U) :
    SSet.ι₀ ≫ nerveNaturalTransformationMap α = nerveMap T := by
  ext n x
  refine CategoryTheory.Functor.ext (fun i => ?_) ?_
  · rfl
  intro i j f
  change 𝟙 (T.obj (x.obj i)) ≫ T.map (x.map f) = 𝟙 _ ≫ T.map (x.map f) ≫ 𝟙 _
  simp

theorem nerveNaturalTransformationMap_one (α : T ⟶ U) :
    SSet.ι₁ ≫ nerveNaturalTransformationMap α = nerveMap U := by
  ext n x
  refine CategoryTheory.Functor.ext (fun i => ?_) ?_
  · rfl
  intro i j f
  change 𝟙 (U.obj (x.obj i)) ≫ U.map (x.map f) = 𝟙 _ ≫ U.map (x.map f) ≫ 𝟙 _
  simp

/-- A natural transformation gives a homotopy between the actual nerve maps. -/
def nerveNaturalTransformationHomotopy (α : T ⟶ U) :
    SSet.Homotopy (nerveMap T) (nerveMap U) where
  h := nerveNaturalTransformationMap α
  h₀ := nerveNaturalTransformationMap_zero α
  h₁ := nerveNaturalTransformationMap_one α
  rel := by
    ext n x
    exact False.elim x.1.property

/-- The induced prism homotopy on simplicial chains, for arbitrary coefficients
in any preadditive category with the required coproducts. -/
def nerveNaturalTransformationChainHomotopy
    {A : Type w} [Category.{z} A] [Preadditive A] [HasCoproducts.{max u v} A]
    (α : T ⟶ U) (R : A) :
    _root_.Homotopy (SSet.chainComplexMap (nerveMap T) R)
      (SSet.chainComplexMap (nerveMap U) R) :=
  (nerveNaturalTransformationHomotopy α).chainComplexMap R

end Sharpness
