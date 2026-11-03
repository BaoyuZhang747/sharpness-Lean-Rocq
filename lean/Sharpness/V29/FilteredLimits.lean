import Sharpness.V29.FilteredLimitsHomology
import Sharpness.Unconditional.CategoryBarCalculation
import Sharpness.Unconditional.FiniteBarConstruction
import Mathlib.Algebra.Category.ModuleCat.Products

/-!
Filtered colimits commute with the actual higher inverse limits of
contravariant module diagrams on a finite category.  The proof goes through
the explicit finite products in the bar cochains and exactness of filtered
colimits.  The comparison map is the canonical colimit comparison, and is
natural in the entire coefficient diagram.
-/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace Sharpness.V29
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite

variable {R C : Type u} [CommRing R] [Category.{u} C]

/-- Restrict a coefficient diagram to the finite discrete family of heads of
all chains of the given length. -/
def coefficientCoordinates (n : ℕ) :
    CoefficientCategory R C ⥤ Discrete (ComposableArrows C n) ⥤ ModuleCat.{u} R :=
  (whiskeringLeft _ _ _).obj
    (Discrete.functor (fun s : ComposableArrows C n => op (s.obj 0)))

def coefficientCoordinatesObjIso (n : ℕ) (M : CoefficientCategory R C) :
    limit ((coefficientCoordinates n).obj M) ≅
      ModuleCat.of R (∀ s : ComposableArrows C n, M.obj (op (s.obj 0))) :=
  HasLimit.isoOfNatIso
    (Discrete.compNatIsoDiscrete (fun s : ComposableArrows C n => op (s.obj 0)) M) ≪≫
    ModuleCat.piIsoPi.{u,u,u} (fun s : ComposableArrows C n => M.obj (op (s.obj 0)))

@[reassoc (attr := simp)]
theorem coefficientCoordinatesObjIso_proj (n : ℕ) (M : CoefficientCategory R C)
    (s : ComposableArrows C n) :
    (coefficientCoordinatesObjIso n M).hom ≫ ModuleCat.ofHom (LinearMap.proj s) =
      limit.π ((coefficientCoordinates n).obj M) (Discrete.mk s) := by
  simp only [coefficientCoordinatesObjIso, Iso.trans_hom, Category.assoc,
    ModuleCat.piIsoPi_hom_ker_subtype, Pi.π]
  erw [HasLimit.isoOfNatIso_hom_π]
  simp
  exact Category.comp_id _

/-- The concrete functions used by the bar complex are the categorical
product of its coefficient coordinates, with the same maps. -/
def coefficientCoordinatesIso (n : ℕ) :
    coefficientCoordinates (R := R) (C := C) n ⋙ lim ≅
      coefficientCochainFunctor ⋙
        HomologicalComplex.eval (ModuleCat.{u} R) (ComplexShape.up ℕ) n := by
  refine NatIso.ofComponents (fun M => coefficientCoordinatesObjIso n M) ?_
  intro M N a
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  funext s
  have h : (coefficientCoordinates (R := R) (C := C) n ⋙ lim).map a ≫
      (coefficientCoordinatesObjIso n N).hom ≫
        ModuleCat.ofHom (LinearMap.proj s) =
    (coefficientCoordinatesObjIso n M).hom ≫
      ModuleCat.ofHom ((a.app (op (s.obj 0))).hom.comp (LinearMap.proj s)) := by
    rw [coefficientCoordinatesObjIso_proj]
    change limMap ((coefficientCoordinates (R := R) (C := C) n).map a) ≫
      limit.π ((coefficientCoordinates n).obj N) (Discrete.mk s) = _
    rw [limMap_π]
    change limit.π ((coefficientCoordinates n).obj M) (Discrete.mk s) ≫
      a.app (op (s.obj 0)) = _
    rw [← coefficientCoordinatesObjIso_proj]
    rfl
  exact congrArg (fun f => f x) h

variable [Finite C] [∀ X Y : C, Finite (X ⟶ Y)]
  {J : Type u} [Category.{u} J] [IsFiltered J]

/-- Each bar cochain degree is a finite product of evaluation functors. -/
instance coefficientCochainsPreserveFilteredColimits :
    PreservesColimitsOfShape J (coefficientCochainFunctor (R := R) (C := C)) := by
  apply HomologicalComplex.preservesColimitsOfShape_of_eval
  intro n
  letI : Finite (ComposableArrows C n) := Unconditional.finiteComposableArrows n
  letI : PreservesColimitsOfShape J
      (lim : (Discrete (ComposableArrows C n) ⥤ ModuleCat.{u} R) ⥤ _) :=
    limitPreservesExactColimits
  letI : PreservesColimitsOfShape J (coefficientCoordinates (R := R) (C := C) n) := by
    unfold coefficientCoordinates
    infer_instance
  exact preservesColimitsOfShape_of_natIso (coefficientCoordinatesIso (R := R) (C := C) n)

/-- The actual derived inverse-limit functor preserves filtered colimits on a
finite category, over an arbitrary commutative ring and in every degree. -/
instance higherLimitPreservesFilteredColimits (n : ℕ) :
    PreservesColimitsOfShape J (higherLimitFunctor R C n) := by
  letI : PreservesColimitsOfShape J
      (coefficientCohomologyFunctor (R := R) (C := C) n) :=
    inferInstanceAs (PreservesColimitsOfShape J
      (coefficientCochainFunctor ⋙
        HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℕ) n))
  exact preservesColimitsOfShape_of_natIso
    (Unconditional.categoryBarCohomologyNatIso (R := R) (C := C) n).symm

/-- The canonical comparison `colim_j lim^n F_j ≅ lim^n (colim_j F_j)`. -/
def filteredColimitHigherLimitIso (F : J ⥤ CoefficientCategory R C) (n : ℕ) :
    colimit (F ⋙ higherLimitFunctor R C n) ≅ higherLimit (colimit F) n :=
  (preservesColimitIso (higherLimitFunctor R C n) F).symm

@[reassoc]
theorem filteredColimitHigherLimitIso_ι (F : J ⥤ CoefficientCategory R C)
    (n : ℕ) (j : J) :
    colimit.ι (F ⋙ higherLimitFunctor R C n) j ≫
        (filteredColimitHigherLimitIso F n).hom =
      (higherLimitFunctor R C n).map (colimit.ι F j) := by
  exact colimit.ι_post F (higherLimitFunctor R C n) j

/-- Naturality in the full filtered coefficient diagram. -/
theorem filteredColimitHigherLimitIso_naturality
    {F G : J ⥤ CoefficientCategory R C} (a : F ⟶ G) (n : ℕ) :
    colim.map (whiskerRight a (higherLimitFunctor R C n)) ≫
        (filteredColimitHigherLimitIso G n).hom =
      (filteredColimitHigherLimitIso F n).hom ≫
        (higherLimitFunctor R C n).map (colim.map a) := by
  exact (preservesColimitNatIso (higherLimitFunctor R C n)).inv.naturality a

end Sharpness.V29
