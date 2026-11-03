import Sharpness.Unconditional.NerveNaturalTransformation
import Sharpness.SmallNerveMap

/-! Native nerve maps and prisms when the categories have different object
universes. Their hom universe supplies the common simplicial-set universe.
This includes the actual one-object group categories and linking comma categories. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u v w z a b
namespace Sharpness
open CategoryTheory CategoryTheory.Limits Simplicial Opposite MonoidalCategory

section Base
variable {C : Type u} {D : Type v}
    [Category.{max u v w} C] [Category.{max u v w} D]

def heterogeneousNerveMap (T : C ⥤ D) : nerve C ⟶ nerve D where
  app _ := ↾fun X => X ⋙ T
  naturality := by intros; rfl

def heterogeneousNervePrism {T U : C ⥤ D} (α : T ⟶ U) :
    nerve C ⊗ Δ[1] ⟶ nerve D where
  app n := ↾fun x =>
    ((SimplexCategory.toCat.map (SSet.stdSimplex.objEquiv x.2)).toFunctor.prod' x.1) ⋙
      Functor.uncurry.obj (ComposableArrows.mk₁ α)
  naturality := by intros; rfl

theorem heterogeneousNervePrism_zero {T U : C ⥤ D} (α : T ⟶ U) :
    SSet.ι₀ ≫ heterogeneousNervePrism α = heterogeneousNerveMap T := by
  ext n x
  refine CategoryTheory.Functor.ext (fun i => ?_) ?_
  · rfl
  intro i j f
  change 𝟙 (T.obj (x.obj i)) ≫ T.map (x.map f) = 𝟙 _ ≫ T.map (x.map f) ≫ 𝟙 _
  simp

theorem heterogeneousNervePrism_one {T U : C ⥤ D} (α : T ⟶ U) :
    SSet.ι₁ ≫ heterogeneousNervePrism α = heterogeneousNerveMap U := by
  ext n x
  refine CategoryTheory.Functor.ext (fun i => ?_) ?_
  · rfl
  intro i j f
  change 𝟙 (U.obj (x.obj i)) ≫ U.map (x.map f) = 𝟙 _ ≫ U.map (x.map f) ≫ 𝟙 _
  simp

def heterogeneousNerveHomotopy {T U : C ⥤ D} (α : T ⟶ U) :
    SSet.Homotopy (heterogeneousNerveMap T) (heterogeneousNerveMap U) where
  h := heterogeneousNervePrism α
  h₀ := heterogeneousNervePrism_zero α
  h₁ := heterogeneousNervePrism_one α
  rel := by ext n x; exact False.elim x.1.property

def heterogeneousNerveChainHomotopy
    {A : Type a} [Category.{b} A] [Preadditive A] [HasCoproducts.{max u v w} A]
    {T U : C ⥤ D} (α : T ⟶ U) (R : A) :
    _root_.Homotopy (SSet.chainComplexMap (heterogeneousNerveMap T) R)
      (SSet.chainComplexMap (heterogeneousNerveMap U) R) :=
  (heterogeneousNerveHomotopy α).chainComplexMap R
end Base

section Composition
variable {C : Type u} {D : Type v} {E : Type z}
    [Category.{max u v w z} C] [Category.{max u v w z} D] [Category.{max u v w z} E]

theorem heterogeneousNerveMap_comp (T : C ⥤ D) (U : D ⥤ E) :
    heterogeneousNerveMap.{u, z, max v w} (T ⋙ U) =
      heterogeneousNerveMap.{u, v, max w z} T ≫
        heterogeneousNerveMap.{v, z, max u w} U := rfl
end Composition

theorem heterogeneousNerveMap_id {C : Type u} [Category.{max u w} C] :
    heterogeneousNerveMap (𝟭 C) = 𝟙 (nerve C) := rfl

theorem heterogeneousNerveMap_eq_nerveMap {C D : Type u}
    [Category.{max u w} C] [Category.{max u w} D] (T : C ⥤ D) :
    heterogeneousNerveMap T = nerveMap T := rfl

theorem heterogeneousNerveMap_eq_singleObj {G : Type u} [Monoid G]
    {D : Type u} [Category.{u} D] (T : SingleObj G ⥤ D) :
    heterogeneousNerveMap T = nerveMapSingleObj G T := rfl

end Sharpness
