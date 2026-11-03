import Sharpness.CategoryChainCofaces

/-! Actual zero strings and the endpoints of a one-arrow string.
These identify the lowest bar terms without choosing representatives. -/
set_option autoImplicit false
universe u
namespace Sharpness
open CategoryTheory Simplicial
variable {C : Type u} [Category.{u} C]

theorem categoryZeroChain_eq (s : ComposableArrows C 0) :
    s = ComposableArrows.mk₀ (chainHead s) := by
  obtain ⟨X, rfl⟩ := ComposableArrows.mk₀_surjective s
  rfl

theorem categoryChain_coface_zero_mk₁ {P Q : C} (f : P ⟶ Q) :
    restrictCategoryChain (SimplexCategory.δ (0 : Fin 2)) (ComposableArrows.mk₁ f) =
      ComposableArrows.mk₀ Q := by
  exact ComposableArrows.ext₀ rfl

theorem categoryChain_coface_one_mk₁ {P Q : C} (f : P ⟶ Q) :
    restrictCategoryChain (SimplexCategory.δ (1 : Fin 2)) (ComposableArrows.mk₁ f) =
      ComposableArrows.mk₀ P := by
  exact ComposableArrows.ext₀ rfl

end Sharpness
