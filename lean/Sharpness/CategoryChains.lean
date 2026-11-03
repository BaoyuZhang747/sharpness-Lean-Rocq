import Mathlib.AlgebraicTopology.SimplicialSet.Nerve

/-! Actual strings of arrows and the head arrow induced by an order map.
These define the cosimplicial replacement for contravariant coefficients. -/
set_option autoImplicit false
universe u
namespace Sharpness
open CategoryTheory Simplicial Opposite
variable {C : Type u} [Category.{u} C]

abbrev chainHead {n : SimplexCategory} (s : ComposableArrows C n.len) : C := s.obj 0

def restrictCategoryChain {n m : SimplexCategory} (f : n ⟶ m)
    (s : ComposableArrows C m.len) : ComposableArrows C n.len :=
  (CategoryTheory.nerve C).map f.op s

def categoryChainHeadArrow {n m : SimplexCategory} (f : n ⟶ m)
    (s : ComposableArrows C m.len) : chainHead s ⟶ chainHead (restrictCategoryChain f s) :=
  s.map (homOfLE (show (0 : Fin (m.len+1)) ≤
      (SimplexCategory.toCat.map f).toFunctor.obj (0 : Fin (n.len+1)) from Nat.zero_le _))

theorem restrictCategoryChain_id {n : SimplexCategory} (s : ComposableArrows C n.len) :
    restrictCategoryChain (𝟙 n) s = s := rfl

theorem categoryChainHeadArrow_id {n : SimplexCategory} (s : ComposableArrows C n.len) :
    categoryChainHeadArrow (𝟙 n) s = 𝟙 (chainHead s) := s.map_id _

theorem restrictCategoryChain_comp {n m l : SimplexCategory} (f : n ⟶ m) (g : m ⟶ l)
    (s : ComposableArrows C l.len) :
    restrictCategoryChain (f ≫ g) s = restrictCategoryChain f (restrictCategoryChain g s) := rfl

theorem categoryChainHeadArrow_comp {n m l : SimplexCategory} (f : n ⟶ m) (g : m ⟶ l)
    (s : ComposableArrows C l.len) :
    categoryChainHeadArrow (f ≫ g) s =
      categoryChainHeadArrow g s ≫ categoryChainHeadArrow f (restrictCategoryChain g s) := by
  change s.map _ = s.map _ ≫ s.map _
  rw [← s.map_comp]
  congr 1

end Sharpness
