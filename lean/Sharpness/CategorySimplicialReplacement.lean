import Sharpness.CategoryChains
import Mathlib.CategoryTheory.Functor.Currying
import Mathlib.CategoryTheory.Products.Basic

/-! The actual bisimplicial replacement of a diagram of simplicial
sets. A (p,q)-simplex is a composable p-string together with a
q-simplex at its head. Every order map and both simplicial directions
are defined, including the action of the head arrow. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u
namespace Sharpness
open CategoryTheory Simplicial Opposite
variable {C : Type u} [Category.{u} C] (D : C ⥤ SSet.{u})

def replacementSimplex (i : SimplexCategory) (j : SimplexCategoryᵒᵖ)
    (s : ComposableArrows C i.len) (x : (D.obj (chainHead s)).obj j) :
    Σ t : ComposableArrows C i.len, (D.obj (chainHead t)).obj j := ⟨s, x⟩

def simplicialReplacementColumn (i : SimplexCategory) : SSet.{u} where
  obj j := Σ s : ComposableArrows C i.len, (D.obj (chainHead s)).obj j
  map f := ↾fun x => ⟨x.1, (D.obj (chainHead x.1)).map f x.2⟩
  map_id j := by
    apply ConcreteCategory.ext_apply
    rintro ⟨s, x⟩
    change replacementSimplex D i j s ((D.obj (chainHead s)).map (𝟙 j) x) =
      replacementSimplex D i j s x
    rw [(D.obj (chainHead s)).map_id]
    rfl
  map_comp {j k l} f g := by
    apply ConcreteCategory.ext_apply
    rintro ⟨s, x⟩
    change replacementSimplex D i l s ((D.obj (chainHead s)).map (f ≫ g) x) =
      replacementSimplex D i l s ((D.obj (chainHead s)).map g ((D.obj (chainHead s)).map f x))
    rw [(D.obj (chainHead s)).map_comp]
    rfl

def simplicialReplacementMap {i j : SimplexCategory} (f : i ⟶ j) :
    simplicialReplacementColumn D j ⟶ simplicialReplacementColumn D i where
  app k := ↾fun x => ⟨restrictCategoryChain f x.1,
    (D.map (categoryChainHeadArrow f x.1)).app k x.2⟩
  naturality {k l} a := by
    apply ConcreteCategory.ext_apply
    rintro ⟨s, x⟩
    change replacementSimplex D i l (restrictCategoryChain f s)
        ((D.map (categoryChainHeadArrow f s)).app l ((D.obj (chainHead s)).map a x)) =
      replacementSimplex D i l (restrictCategoryChain f s)
        ((D.obj (chainHead (restrictCategoryChain f s))).map a
          ((D.map (categoryChainHeadArrow f s)).app k x))
    exact congrArg (replacementSimplex D i l (restrictCategoryChain f s))
      (congrArg (fun t => t x) ((D.map (categoryChainHeadArrow f s)).naturality a))

theorem simplicialReplacementMap_id (i : SimplexCategory) :
    simplicialReplacementMap D (𝟙 i) = 𝟙 _ := by
  apply NatTrans.ext
  funext k
  apply ConcreteCategory.ext_apply
  rintro ⟨s, x⟩
  change replacementSimplex D i k s ((D.map (categoryChainHeadArrow (𝟙 i) s)).app k x) =
    replacementSimplex D i k s x
  rw [categoryChainHeadArrow_id, D.map_id]
  rfl

theorem simplicialReplacementMap_comp {i j k : SimplexCategory}
    (f : i ⟶ j) (g : j ⟶ k) :
    simplicialReplacementMap D (f ≫ g) =
      simplicialReplacementMap D g ≫ simplicialReplacementMap D f := by
  apply NatTrans.ext
  funext a
  apply ConcreteCategory.ext_apply
  rintro ⟨s, x⟩
  change replacementSimplex D i a (restrictCategoryChain (f ≫ g) s)
      ((D.map (categoryChainHeadArrow (f ≫ g) s)).app a x) =
    replacementSimplex D i a (restrictCategoryChain (f ≫ g) s)
      ((D.map (categoryChainHeadArrow f (restrictCategoryChain g s))).app a
        ((D.map (categoryChainHeadArrow g s)).app a x))
  rw [categoryChainHeadArrow_comp, D.map_comp]
  rfl

def simplicialSetReplacement : SimplicialObject SSet.{u} where
  obj i := simplicialReplacementColumn D i.unop
  map f := simplicialReplacementMap D f.unop
  map_id i := simplicialReplacementMap_id D i.unop
  map_comp f g := simplicialReplacementMap_comp D g.unop f.unop

def simplicialReplacementDiagonal : SSet.{u} :=
  Functor.diag SimplexCategoryᵒᵖ ⋙ Functor.uncurry.obj (simplicialSetReplacement D)

theorem simplicialReplacementDiagonal_map {i j : SimplexCategoryᵒᵖ} (f : i ⟶ j)
    (s : ComposableArrows C i.unop.len) (x : (D.obj (chainHead s)).obj i) :
    (simplicialReplacementDiagonal D).map f ⟨s, x⟩ =
      ⟨restrictCategoryChain f.unop s,
        (D.obj (chainHead (restrictCategoryChain f.unop s))).map f
          ((D.map (categoryChainHeadArrow f.unop s)).app i x)⟩ := rfl

end Sharpness
