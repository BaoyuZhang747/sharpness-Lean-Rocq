import Sharpness.CategorySimplicialReplacement

/-! A genuine cocone of simplicial sets augments the actual
replacement in every column and its diagonal. These are explicit
simplicial maps, before any geometric equivalence is asserted. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u
namespace Sharpness
open CategoryTheory Simplicial Opposite
variable {C : Type u} [Category.{u} C] (D : C ⥤ SSet.{u})
    {X : SSet.{u}} (a : D ⟶ (Functor.const C).obj X)

def simplicialReplacementColumnAugmentation (i : SimplexCategory) :
    simplicialReplacementColumn D i ⟶ X where
  app j := ↾fun x => (a.app (chainHead x.1)).app j x.2
  naturality {j k} f := by
    apply ConcreteCategory.ext_apply
    rintro ⟨s, x⟩
    change (a.app (chainHead s)).app k ((D.obj (chainHead s)).map f x) =
      X.map f ((a.app (chainHead s)).app j x)
    exact congrArg (fun t => t x) ((a.app (chainHead s)).naturality f)

theorem simplicialReplacementColumnAugmentation_naturality {i j : SimplexCategory}
    (f : i ⟶ j) :
    simplicialReplacementMap D f ≫ simplicialReplacementColumnAugmentation D a i =
      simplicialReplacementColumnAugmentation D a j := by
  apply NatTrans.ext
  funext k
  apply ConcreteCategory.ext_apply
  rintro ⟨s, x⟩
  change (a.app (chainHead (restrictCategoryChain f s))).app k
      ((D.map (categoryChainHeadArrow f s)).app k x) =
    (a.app (chainHead s)).app k x
  have h : D.map (categoryChainHeadArrow f s) ≫
      a.app (chainHead (restrictCategoryChain f s)) = a.app (chainHead s) :=
    (a.naturality (categoryChainHeadArrow f s)).trans (Category.comp_id _)
  exact congrArg (fun t => t.app k x) h

def simplicialReplacementDiagonalAugmentation : simplicialReplacementDiagonal D ⟶ X where
  app i := (simplicialReplacementColumnAugmentation D a i.unop).app i
  naturality {i j} f := by
    apply ConcreteCategory.ext_apply
    rintro ⟨s, x⟩
    change (a.app (chainHead (restrictCategoryChain f.unop s))).app j
        ((D.obj (chainHead (restrictCategoryChain f.unop s))).map f
          ((D.map (categoryChainHeadArrow f.unop s)).app i x)) =
      X.map f ((a.app (chainHead s)).app i x)
    have h₁ := congrArg (fun t => t ((D.map (categoryChainHeadArrow f.unop s)).app i x))
      ((a.app (chainHead (restrictCategoryChain f.unop s))).naturality f)
    have ha : D.map (categoryChainHeadArrow f.unop s) ≫
        a.app (chainHead (restrictCategoryChain f.unop s)) = a.app (chainHead s) :=
      (a.naturality (categoryChainHeadArrow f.unop s)).trans (Category.comp_id _)
    have h₂ := congrArg (fun t => t.app i x) ha
    exact h₁.trans (congrArg (fun y => X.map f y) h₂)

theorem simplicialReplacementDiagonalAugmentation_component (i : SimplexCategoryᵒᵖ)
    (s : ComposableArrows C i.unop.len) (x : (D.obj (chainHead s)).obj i) :
    (simplicialReplacementDiagonalAugmentation D a).app i ⟨s, x⟩ =
      (a.app (chainHead s)).app i x := rfl

end Sharpness
