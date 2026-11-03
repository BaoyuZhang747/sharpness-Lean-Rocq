import Sharpness.CategoryChains

/-! The head of a deleted-vertex string: deleting vertex zero uses
the first actual arrow; deleting any later vertex fixes the head. -/
set_option autoImplicit false
universe u
namespace Sharpness
open CategoryTheory Simplicial
variable {C : Type u} [Category.{u} C]

theorem categoryChainHeadArrow_coface_zero (n : ℕ) (s : ComposableArrows C (n+1)) :
    categoryChainHeadArrow (SimplexCategory.δ (0 : Fin (n+2))) s = s.map' 0 1 := by
  rfl

theorem categoryChainHeadArrow_coface_succ (n : ℕ) (i : Fin (n+1)) (s : ComposableArrows C (n+1)) :
    categoryChainHeadArrow (SimplexCategory.δ i.succ) s = 𝟙 (chainHead s) := by
  exact s.map_id _

end Sharpness
