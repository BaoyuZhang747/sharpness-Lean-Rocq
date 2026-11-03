import Sharpness.CategoryChains
import Mathlib.CategoryTheory.Comma.StructuredArrow.Functor

/-! Concrete comma-category strings from the diagonal replacement.
The arrow square follows from the original comma square and the
initial-vertex arrow in the base string. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace Sharpness
open CategoryTheory Simplicial Opposite

def categoryStringInitialArrow {D : Type u} [Category.{u} D] {n : ℕ}
    (s : ComposableArrows D n) (i : Fin (n+1)) : s.obj 0 ⟶ s.obj i :=
  s.map (homOfLE (show (0 : Fin (n+1)) ≤ i from Nat.zero_le _))

theorem categoryStringInitialArrow_comp {D : Type u} [Category.{u} D] {n : ℕ}
    (s : ComposableArrows D n) {i j : Fin (n+1)} (f : i ⟶ j) :
    categoryStringInitialArrow s i ≫ s.map f = categoryStringInitialArrow s j := by
  rw [categoryStringInitialArrow, ← s.map_comp]
  exact congrArg s.map (Subsingleton.elim _ _)

variable {C D : Type u} [Category.{u} C] [Category.{u} D] (T : C ⥤ D)

def costructuredDiagonalCommaString {n : ℕ} (s : ComposableArrows D n)
    (x : ComposableArrows (CostructuredArrow T (chainHead s)) n) :
    ComposableArrows (Comma T (𝟭 D)) n where
  obj i := ⟨(x.obj i).left, s.obj i, (x.obj i).hom ≫ categoryStringInitialArrow s i⟩
  map {i j} f := ⟨(x.map f).left, s.map f, by
    change T.map (x.map f).left ≫ ((x.obj j).hom ≫ categoryStringInitialArrow s j) =
      ((x.obj i).hom ≫ categoryStringInitialArrow s i) ≫ s.map f
    rw [← Category.assoc, CostructuredArrow.w, Category.assoc, categoryStringInitialArrow_comp]⟩
  map_id i := by
    refine Comma.hom_ext _ _ ?_ ?_
    · change (x.map (𝟙 i)).left = 𝟙 (x.obj i).left
      rw [x.map_id]
      rfl
    · exact s.map_id i
  map_comp f g := by
    refine Comma.hom_ext _ _ ?_ ?_
    · change (x.map (f ≫ g)).left = (x.map f).left ≫ (x.map g).left
      rw [x.map_comp]
      rfl
    · exact s.map_comp f g

theorem costructuredDiagonalCommaString_fst {n : ℕ} (s : ComposableArrows D n)
    (x : ComposableArrows (CostructuredArrow T (chainHead s)) n) :
    costructuredDiagonalCommaString T s x ⋙ Comma.fst T (𝟭 D) =
      x ⋙ CostructuredArrow.proj T (chainHead s) := rfl

theorem costructuredDiagonalCommaString_snd {n : ℕ} (s : ComposableArrows D n)
    (x : ComposableArrows (CostructuredArrow T (chainHead s)) n) :
    costructuredDiagonalCommaString T s x ⋙ Comma.snd T (𝟭 D) = s := rfl

end Sharpness
