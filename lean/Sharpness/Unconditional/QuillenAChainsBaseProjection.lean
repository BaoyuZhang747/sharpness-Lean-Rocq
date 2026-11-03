import Sharpness.Unconditional.CanonicalReplacementInvarianceColumns
import Sharpness.CostructuredDiagonalComparison
import Mathlib.CategoryTheory.PUnit

/-! The actual base projection of the bisimplicial replacement. Objectwise
native nerve-to-point quasi-isomorphisms imply its column quasi-isomorphisms. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace Sharpness
open CategoryTheory Simplicial Opposite

variable {C : Type u} [Category.{u} C] (D : C ⥤ SSet.{u})

def simplicialReplacementBaseColumn (i : SimplexCategory) :
    simplicialReplacementColumn D i ⟶
      (Functor.const SimplexCategoryᵒᵖ).obj (ComposableArrows C i.len) where
  app _ := ↾Sigma.fst
  naturality {_ _} _ := rfl

def simplicialReplacementBaseProjection : simplicialSetReplacement D ⟶
    ((Functor.const SimplexCategoryᵒᵖ).obj (nerve C)).flip where
  app i := simplicialReplacementBaseColumn D i.unop
  naturality {_ _} _ := rfl

def simplicialReplacementBaseDiagonal : simplicialReplacementDiagonal D ⟶ nerve C where
  app _ := ↾Sigma.fst
  naturality {_ _} _ := rfl

abbrev simplicialPointNerve : SSet.{u} := nerve (Discrete PUnit.{u+1})

def pointNerveReplacementColumnSection (i : SimplexCategory) :
    (Functor.const SimplexCategoryᵒᵖ).obj (ComposableArrows C i.len) ⟶
      simplicialReplacementColumn ((Functor.const C).obj simplicialPointNerve) i where
  app n := ↾fun s => ⟨s, Functor.star (Fin (n.unop.len+1))⟩
  naturality {n m} f := by
    ext s
    apply Sigma.ext rfl
    exact heq_of_eq (Functor.punit_ext' _ _)

def pointNerveReplacementColumnIso (i : SimplexCategory) :
    simplicialReplacementColumn ((Functor.const C).obj simplicialPointNerve) i ≅
      (Functor.const SimplexCategoryᵒᵖ).obj (ComposableArrows C i.len) where
  hom := simplicialReplacementBaseColumn _ i
  inv := pointNerveReplacementColumnSection i
  hom_inv_id := by
    ext n x
    apply Sigma.ext rfl
    exact heq_of_eq (Functor.punit_ext' _ _)
  inv_hom_id := by ext n x; rfl

theorem simplicialReplacementBaseColumn_factor
    (a : D ⟶ (Functor.const C).obj simplicialPointNerve) (i : SimplexCategory) :
    simplicialReplacementColumnMap a i ≫ (pointNerveReplacementColumnIso i).hom =
      simplicialReplacementBaseColumn D i := by
  ext n x
  rfl

theorem simplicialReplacementBaseColumn_quasiIso (R : Type u) [CommRing R]
    (a : D ⟶ (Functor.const C).obj simplicialPointNerve)
    (ha : ∀ c, QuasiIso (SSet.chainComplexMap (a.app c) (ModuleCat.of R R)))
    (i : SimplexCategory) :
    QuasiIso (SSet.chainComplexMap (simplicialReplacementBaseColumn D i) (ModuleCat.of R R)) := by
  let J := (SSet.chainComplexFunctor (ModuleCat.{u} R)).obj (ModuleCat.of R R)
  haveI : QuasiIso (J.map (simplicialReplacementColumnMap a i)) :=
    TotalComparison.replacementColumnChainMap_quasiIso a ha i
  change QuasiIso (J.map (simplicialReplacementBaseColumn D i))
  rw [← simplicialReplacementBaseColumn_factor D a i, J.map_comp]
  infer_instance

variable {E : Type u} [Category.{u} E] (T : C ⥤ E)

def costructuredNervePointCocone : costructuredNerveDiagram T ⟶
    (Functor.const E).obj simplicialPointNerve where
  app d := nerveMap (Functor.star (CostructuredArrow T d))
  naturality {d e} f := by
    ext n x
    exact Functor.punit_ext' _ _

theorem costructuredBaseColumn_quasiIso (R : Type u) [CommRing R]
    (h : ∀ d, QuasiIso (SSet.chainComplexMap
      (nerveMap (Functor.star (CostructuredArrow T d))) (ModuleCat.of R R)))
    (i : SimplexCategory) :
    QuasiIso (SSet.chainComplexMap
      ((simplicialReplacementBaseProjection (costructuredNerveDiagram T)).app (op i))
      (ModuleCat.of R R)) :=
  simplicialReplacementBaseColumn_quasiIso (costructuredNerveDiagram T) R
    (costructuredNervePointCocone T) h i

end Sharpness
