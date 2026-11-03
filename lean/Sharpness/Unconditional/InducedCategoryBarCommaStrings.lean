import Sharpness.CategoryChains
import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic

/-! A string in X↓q is exactly a C-string together with its first arrow
from X to q of the first object. This correspondence respects every simplex map. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace Sharpness.Unconditional
open CategoryTheory Simplicial Opposite
variable {C D : Type u} [Category.{u} C] [Category.{u} D] (q : C ⥤ D)

def inducedBarCommaInitialArrow {n : ℕ} (s : ComposableArrows C n) (j : Fin (n+1)) :
    s.obj 0 ⟶ s.obj j := s.map (homOfLE (Nat.zero_le _))

theorem inducedBarCommaInitialArrow_comp {n : ℕ} (s : ComposableArrows C n)
    {j k : Fin (n+1)} (f : j ⟶ k) :
    inducedBarCommaInitialArrow s j ≫ s.map f = inducedBarCommaInitialArrow s k := by
  rw [inducedBarCommaInitialArrow, ← s.map_comp]
  exact congrArg s.map (Subsingleton.elim _ _)

def inducedBarCommaString {n : ℕ} {X : D} (s : ComposableArrows C n)
    (g : X ⟶ q.obj (chainHead s)) : ComposableArrows (StructuredArrow X q) n where
  obj j := StructuredArrow.mk (g ≫ q.map (inducedBarCommaInitialArrow s j))
  map {j k} f := StructuredArrow.homMk (s.map f) (by
    change (g ≫ q.map (inducedBarCommaInitialArrow s j)) ≫ q.map (s.map f) = _
    rw [Category.assoc, ← q.map_comp, inducedBarCommaInitialArrow_comp]
    rfl)
  map_id j := by apply StructuredArrow.hom_ext; exact s.map_id j
  map_comp f g := by apply StructuredArrow.hom_ext; exact s.map_comp f g

theorem inducedBarCommaString_projection {n : ℕ} {X : D} (s : ComposableArrows C n)
    (g : X ⟶ q.obj (chainHead s)) :
    inducedBarCommaString q s g ⋙ StructuredArrow.proj X q = s := rfl

@[simp] theorem inducedBarCommaString_first {n : ℕ} {X : D} (s : ComposableArrows C n)
    (g : X ⟶ q.obj (chainHead s)) : ((inducedBarCommaString q s g).obj 0).hom = g := by
  change g ≫ q.map (s.map _) = g
  have hs : s.map (homOfLE (show (0 : Fin (n+1)) ≤ 0 from le_rfl)) = 𝟙 _ := s.map_id _
  rw [hs, q.map_id, Category.comp_id]

theorem inducedBarCommaString_recover {n : ℕ} {X : D}
    (s : ComposableArrows (StructuredArrow X q) n) :
    inducedBarCommaString q (s ⋙ StructuredArrow.proj X q) (s.obj 0).hom = s := by
  refine CategoryTheory.Functor.ext (fun j => ?_) ?_
  · refine StructuredArrow.obj_ext
      ((inducedBarCommaString q (s ⋙ StructuredArrow.proj X q) (s.obj 0).hom).obj j)
      (s.obj j) rfl ?_
    simp only [eqToHom_refl, q.map_id, Category.comp_id]
    exact StructuredArrow.w (s.map (homOfLE (show (0 : Fin (n+1)) ≤ j from Nat.zero_le _)))
  · intro j k f
    apply StructuredArrow.hom_ext
    simp only [StructuredArrow.comp_right, StructuredArrow.eqToHom_right]
    change (s.map f).right = (𝟙 _) ≫ (s.map f).right ≫ (𝟙 _)
    simp only [Category.id_comp, Category.comp_id]

theorem inducedBarCommaString_restrict {n m : SimplexCategory} {X : D}
    (f : n ⟶ m) (s : ComposableArrows C m.len) (g : X ⟶ q.obj (chainHead s)) :
    inducedBarCommaString q (restrictCategoryChain f s) (g ≫ q.map (categoryChainHeadArrow f s)) =
      restrictCategoryChain f (inducedBarCommaString q s g) := by
  let k : Fin (n.len+1) ⥤ Fin (m.len+1) := (SimplexCategory.toCat.map f).toFunctor
  refine CategoryTheory.Functor.ext (fun j => ?_) ?_
  · refine StructuredArrow.obj_ext _ _ rfl ?_
    simp only [eqToHom_refl, q.map_id, Category.comp_id]
    change (g ≫ q.map (inducedBarCommaInitialArrow s (k.obj 0))) ≫
      q.map (s.map (k.map (homOfLE (show (0 : Fin (n.len+1)) ≤ j from Nat.zero_le _)))) = _
    rw [Category.assoc, ← q.map_comp, inducedBarCommaInitialArrow_comp]
    rfl
  · intro j l h
    apply StructuredArrow.hom_ext
    simp only [StructuredArrow.comp_right, StructuredArrow.eqToHom_right]
    change s.map (k.map h) = (𝟙 _) ≫ s.map (k.map h) ≫ (𝟙 _)
    simp only [Category.id_comp, Category.comp_id]

def inducedBarCommaBasisEquiv (X : D) (n : ℕ) :
    (Σ s : ComposableArrows C n, X ⟶ q.obj (chainHead s)) ≃
      ComposableArrows (StructuredArrow X q) n where
  toFun b := inducedBarCommaString q b.1 b.2
  invFun s := ⟨s ⋙ StructuredArrow.proj X q, (s.obj 0).hom⟩
  left_inv b := by
    rcases b with ⟨s, g⟩
    change (⟨s, ((inducedBarCommaString q s g).obj 0).hom⟩ :
      Σ s : ComposableArrows C n, X ⟶ q.obj (chainHead s)) = ⟨s, g⟩
    rw [inducedBarCommaString_first]
  right_inv := inducedBarCommaString_recover q

end Sharpness.Unconditional
