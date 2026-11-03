import Sharpness.SimplicialReplacementAugmentationNaturality
import Mathlib.AlgebraicTopology.SimplicialSet.TopAdj

/-! The actual realization/singular adjunction unit, its action on
diagrams and their diagonal replacements, and its strict commuting
square with any actual cocone augmentation. No equivalence property
of the unit is assumed here. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace Sharpness
open CategoryTheory Simplicial Opposite

abbrev realizationSingularFunctor : SSet.{u} ⥤ SSet.{u} := SSet.toTop ⋙ TopCat.toSSet

def realizationSingularUnit (X : SSet.{u}) : X ⟶ realizationSingularFunctor.obj X :=
  sSetTopAdj.unit.app X

theorem realizationSingularUnit_naturality {X Y : SSet.{u}} (f : X ⟶ Y) :
    f ≫ realizationSingularUnit Y = realizationSingularUnit X ≫ realizationSingularFunctor.map f :=
  sSetTopAdj.unit.naturality f

variable {C : Type u} [Category.{u} C] (D : C ⥤ SSet.{u})

def realizationDiagramUnit : D ⟶ D ⋙ realizationSingularFunctor where
  app P := realizationSingularUnit (D.obj P)
  naturality {P Q} f := realizationSingularUnit_naturality (D.map f)

def realizationReplacementUnit :
    simplicialReplacementDiagonal D ⟶ simplicialReplacementDiagonal (D ⋙ realizationSingularFunctor) :=
  simplicialReplacementDiagonalMap (realizationDiagramUnit D)

variable {X : SSet.{u}} (a : D ⟶ (Functor.const C).obj X)

def realizationCocone : D ⋙ realizationSingularFunctor ⟶
    (Functor.const C).obj (realizationSingularFunctor.obj X) where
  app P := realizationSingularFunctor.map (a.app P)
  naturality {P Q} f := by
    change realizationSingularFunctor.map (D.map f) ≫ realizationSingularFunctor.map (a.app Q) =
      realizationSingularFunctor.map (a.app P) ≫ 𝟙 _
    calc
      _ = realizationSingularFunctor.map (D.map f ≫ a.app Q) :=
        (realizationSingularFunctor.map_comp _ _).symm
      _ = realizationSingularFunctor.map (a.app P) :=
        congrArg (fun t => realizationSingularFunctor.map t)
          ((a.naturality f).trans (Category.comp_id _))
      _ = _ := (Category.comp_id _).symm

theorem realizationReplacementUnit_augmentation :
    realizationReplacementUnit D ≫
        simplicialReplacementDiagonalAugmentation (D ⋙ realizationSingularFunctor) (realizationCocone D a) =
      simplicialReplacementDiagonalAugmentation D a ≫ realizationSingularUnit X :=
  simplicialReplacementDiagonalAugmentation_naturality (realizationDiagramUnit D) a
    (realizationCocone D a) (realizationSingularUnit X)
    (fun P => (realizationSingularUnit_naturality (a.app P)).symm)

end Sharpness
