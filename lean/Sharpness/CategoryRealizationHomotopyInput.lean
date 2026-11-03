import Mathlib.AlgebraicTopology.SimplicialSet.Nerve
import Mathlib.AlgebraicTopology.SimplicialSet.TopAdj
import Mathlib.Topology.Homotopy.TopCat.Basic

/-! The general published realization theorem AKO III.2.1, p.123
(Segal Proposition 2.1): a natural transformation induces a homotopy.
Only this uniform theorem is an input. No specific functor, inverse,
Grothendieck construction, cohomology or convergence is in this input. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness
open CategoryTheory

def categoryRealization (C : Type u) [Category.{u} C] : TopCat.{u} :=
  SSet.toTop.obj (CategoryTheory.nerve C)

def categoryRealizationMap {C D : Type u} [Category.{u} C] [Category.{u} D] (T : C ⥤ D) :
    categoryRealization C ⟶ categoryRealization D :=
  SSet.toTop.map (CategoryTheory.nerveMap T)

theorem categoryRealizationMap_comp {C D E : Type u}
    [Category.{u} C] [Category.{u} D] [Category.{u} E] (T : C ⥤ D) (U : D ⥤ E) :
    categoryRealizationMap (T ⋙ U) = categoryRealizationMap T ≫ categoryRealizationMap U :=
  SSet.toTop.map_comp (CategoryTheory.nerveMap T) (CategoryTheory.nerveMap U)

theorem categoryRealizationMap_id (C : Type u) [Category.{u} C] :
    categoryRealizationMap (𝟭 C) = 𝟙 (categoryRealization C) :=
  SSet.toTop.map_id (CategoryTheory.nerve C)

structure CategoryRealizationHomotopyInput where
  AKO_III_2_1 : ∀ {C D : Type u} [Category.{u} C] [Category.{u} D]
    {T U : C ⥤ D}, (T ⟶ U) → Nonempty (TopCat.Homotopy (categoryRealizationMap T) (categoryRealizationMap U))

end Sharpness
