import Sharpness.CoefficientCochainFormula
import Sharpness.CategoryChainCofaces

/-! The actual coefficient differential has exactly the displayed
AKO III.5.3 bar formula: first-arrow pullback plus signed deletion of
each later vertex. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness
open CategoryTheory Simplicial Opposite
variable {R C : Type u} [CommRing R] [Category.{u} C]
    (M : Cᵒᵖ ⥤ ModuleCat.{u} R)

set_option backward.isDefEq.respectTransparency false in
theorem coefficientCochains_bar_d (n : ℕ) (x : (coefficientCochains M).X n)
    (s : ComposableArrows C (n+1)) :
    (coefficientCochains M).d n (n+1) x s =
      (show M.obj (op (chainHead s)) from
        M.map (s.map' 0 1).op (x (restrictCategoryChain (SimplexCategory.δ (0 : Fin (n+2))) s))) +
        ∑ i : Fin (n+1), (-1 : ℤ)^((i : ℕ)+1) •
          (show M.obj (op (chainHead s)) from x (restrictCategoryChain (SimplexCategory.δ i.succ) s)) := by
  rw [coefficientCochains_d_apply, Fin.sum_univ_succ]
  simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_succ, categoryChainHeadArrow_coface_zero]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [categoryChainHeadArrow_coface_succ]
  change (-1 : ℤ)^((i : ℕ)+1) • M.map (𝟙 _) _ = _
  rw [M.map_id]
  rfl

end Sharpness
