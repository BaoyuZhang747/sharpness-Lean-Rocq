import Sharpness.CategoryChains
import Mathlib.CategoryTheory.Grothendieck

/-! The concrete Grothendieck string associated to a diagonal
simplex of the covariant nerve replacement. It is built using the
native map and base-change functors, so all arrow compositions are
checked by their functor structures. No comparison or equivalence
theorem is an input. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace Sharpness
open CategoryTheory Simplicial Opposite

def constantGrothendieckString (A : Cat.{u,u}) {n : ℕ} (x : ComposableArrows A n) :
    ComposableArrows (Grothendieck ((Functor.const (Fin (n+1))).obj A)) n where
  obj i := ⟨i, x.obj i⟩
  map f := ⟨f, x.map f⟩
  map_id i := by
    refine Grothendieck.ext _ _ ?_ ?_
    · rfl
    · change (𝟙 _) ≫ x.map (𝟙 i) = 𝟙 _
      rw [x.map_id, Category.id_comp]
  map_comp f g := by
    refine Grothendieck.ext _ _ ?_ ?_
    · rfl
    · change (𝟙 _) ≫ x.map (f ≫ g) = (𝟙 _) ≫ x.map f ≫ x.map g
      simpa only [Category.id_comp] using x.map_comp f g

variable {C : Type u} [Category.{u} C] (B : C ⥤ Cat.{u,u})

def categoryStringHeadDiagram {n : ℕ} (s : ComposableArrows C n) :
    (Functor.const (Fin (n+1))).obj (B.obj (chainHead s)) ⟶ s ⋙ B where
  app i := B.map (s.map (homOfLE (show (0 : Fin (n+1)) ≤ i from Nat.zero_le _)))
  naturality {i j} f := by
    change (𝟙 _) ≫ B.map (s.map (homOfLE (show (0 : Fin (n+1)) ≤ j from Nat.zero_le _))) =
      B.map (s.map (homOfLE (show (0 : Fin (n+1)) ≤ i from Nat.zero_le _))) ≫ B.map (s.map f)
    calc
      _ = B.map (s.map (homOfLE (show (0 : Fin (n+1)) ≤ j from Nat.zero_le _))) := Category.id_comp _
      _ = B.map (s.map ((homOfLE (show (0 : Fin (n+1)) ≤ i from Nat.zero_le _)) ≫ f)) :=
        congrArg (fun t => B.map (s.map t)) (Subsingleton.elim _ _)
      _ = B.map (s.map (homOfLE (show (0 : Fin (n+1)) ≤ i from Nat.zero_le _)) ≫ s.map f) :=
        congrArg (fun t => B.map t) (s.map_comp _ _)
      _ = _ := B.map_comp _ _

def grothendieckDiagonalString {n : ℕ} (s : ComposableArrows C n)
    (x : ComposableArrows (B.obj (chainHead s)) n) : ComposableArrows (Grothendieck B) n :=
  constantGrothendieckString (B.obj (chainHead s)) x ⋙
    Grothendieck.map (categoryStringHeadDiagram B s) ⋙ Grothendieck.pre B s

theorem grothendieckDiagonalString_obj_base {n : ℕ} (s : ComposableArrows C n)
    (x : ComposableArrows (B.obj (chainHead s)) n) (i : Fin (n+1)) :
    ((grothendieckDiagonalString B s x).obj i).base = s.obj i := rfl

theorem grothendieckDiagonalString_obj_fiber {n : ℕ} (s : ComposableArrows C n)
    (x : ComposableArrows (B.obj (chainHead s)) n) (i : Fin (n+1)) :
    ((grothendieckDiagonalString B s x).obj i).fiber =
      (B.map (s.map (homOfLE (show (0 : Fin (n+1)) ≤ i from Nat.zero_le _)))).toFunctor.obj (x.obj i) := rfl

theorem grothendieckDiagonalString_map_base {n : ℕ} (s : ComposableArrows C n)
    (x : ComposableArrows (B.obj (chainHead s)) n) {i j : Fin (n+1)} (f : i ⟶ j) :
    ((grothendieckDiagonalString B s x).map f).base = s.map f := rfl

end Sharpness
