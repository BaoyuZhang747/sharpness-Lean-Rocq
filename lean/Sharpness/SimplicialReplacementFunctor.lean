import Sharpness.CategorySimplicialReplacement

/-! Actual functoriality of the bisimplicial replacement under a
natural transformation of simplicial-set diagrams. Every map keeps
the actual indexing string and applies the given map at its head. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u
namespace Sharpness
open CategoryTheory Simplicial Opposite
variable {C : Type u} [Category.{u} C] {D E H : C ⥤ SSet.{u}}

def simplicialReplacementColumnMap (a : D ⟶ E) (i : SimplexCategory) :
    simplicialReplacementColumn D i ⟶ simplicialReplacementColumn E i where
  app j := ↾fun x => ⟨x.1, (a.app (chainHead x.1)).app j x.2⟩
  naturality {j k} f := by
    apply ConcreteCategory.ext_apply
    rintro ⟨s, x⟩
    change replacementSimplex E i k s ((a.app (chainHead s)).app k ((D.obj (chainHead s)).map f x)) =
      replacementSimplex E i k s ((E.obj (chainHead s)).map f ((a.app (chainHead s)).app j x))
    exact congrArg (replacementSimplex E i k s)
      (congrArg (fun t => t x) ((a.app (chainHead s)).naturality f))

theorem simplicialReplacementColumnMap_naturality (a : D ⟶ E)
    {i j : SimplexCategory} (f : i ⟶ j) :
    simplicialReplacementMap D f ≫ simplicialReplacementColumnMap a i =
      simplicialReplacementColumnMap a j ≫ simplicialReplacementMap E f := by
  apply NatTrans.ext
  funext k
  apply ConcreteCategory.ext_apply
  rintro ⟨s, x⟩
  change replacementSimplex E i k (restrictCategoryChain f s)
      ((a.app (chainHead (restrictCategoryChain f s))).app k
        ((D.map (categoryChainHeadArrow f s)).app k x)) =
    replacementSimplex E i k (restrictCategoryChain f s)
      ((E.map (categoryChainHeadArrow f s)).app k ((a.app (chainHead s)).app k x))
  exact congrArg (replacementSimplex E i k (restrictCategoryChain f s))
    (congrArg (fun t => t.app k x) (a.naturality (categoryChainHeadArrow f s)))

def simplicialReplacementNatTrans (a : D ⟶ E) : simplicialSetReplacement D ⟶ simplicialSetReplacement E where
  app i := simplicialReplacementColumnMap a i.unop
  naturality {i j} f := simplicialReplacementColumnMap_naturality a f.unop

def simplicialReplacementDiagonalMap (a : D ⟶ E) :
    simplicialReplacementDiagonal D ⟶ simplicialReplacementDiagonal E :=
  Functor.whiskerLeft (Functor.diag SimplexCategoryᵒᵖ) (Functor.uncurry.map (simplicialReplacementNatTrans a))

theorem simplicialReplacementDiagonalMap_component (a : D ⟶ E) (i : SimplexCategoryᵒᵖ)
    (s : ComposableArrows C i.unop.len) (x : (D.obj (chainHead s)).obj i) :
    (simplicialReplacementDiagonalMap a).app i ⟨s, x⟩ =
      replacementSimplex E i.unop i s ((a.app (chainHead s)).app i x) := rfl

theorem simplicialReplacementDiagonalMap_id (D : C ⥤ SSet.{u}) :
    simplicialReplacementDiagonalMap (𝟙 D) = 𝟙 _ := by
  apply NatTrans.ext
  funext i
  apply ConcreteCategory.ext_apply
  rintro ⟨s, x⟩
  rfl

theorem simplicialReplacementDiagonalMap_comp (a : D ⟶ E) (b : E ⟶ H) :
    simplicialReplacementDiagonalMap (a ≫ b) =
      simplicialReplacementDiagonalMap a ≫ simplicialReplacementDiagonalMap b := by
  apply NatTrans.ext
  funext i
  apply ConcreteCategory.ext_apply
  rintro ⟨s, x⟩
  rfl

end Sharpness
