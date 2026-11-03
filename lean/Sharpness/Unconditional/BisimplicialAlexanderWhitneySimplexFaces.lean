import Sharpness.Unconditional.BisimplicialAlexanderWhitneyFaces

/-! The front/back face identities evaluated in arbitrary bisimplicial sets. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u

namespace Sharpness
open CategoryTheory Simplicial Opposite

variable (X : SimplicialObject SSet.{u})

/-- Pullback in both simplex coordinates, using the actual uncurried functor. -/
def bisimplicialSimplexPull {p q m n : ℕ} (f : ⦋p⦌ ⟶ ⦋m⦌) (g : ⦋q⦌ ⟶ ⦋n⦌) :
    (X.obj (op ⦋m⦌)).obj (op ⦋n⦌) ⟶ (X.obj (op ⦋p⦌)).obj (op ⦋q⦌) :=
  (Functor.uncurry.obj X).map
    (show (op ⦋m⦌, op ⦋n⦌) ⟶ (op ⦋p⦌, op ⦋q⦌) from (f.op, g.op))

theorem bisimplicialSimplexPull_apply {p q m n : ℕ}
    (f : ⦋p⦌ ⟶ ⦋m⦌) (g : ⦋q⦌ ⟶ ⦋n⦌)
    (x : (X.obj (op ⦋m⦌)).obj (op ⦋n⦌)) :
    bisimplicialSimplexPull X f g x =
      (X.map f.op).app (op ⦋q⦌) ((X.obj (op ⦋m⦌)).map g.op x) := by
  exact congrArg (fun z => z x) ((X.map f.op).naturality g.op).symm

theorem bisimplicialSimplexPull_comp {p q m n a b : ℕ}
    (f : ⦋p⦌ ⟶ ⦋m⦌) (g : ⦋q⦌ ⟶ ⦋n⦌)
    (f' : ⦋a⦌ ⟶ ⦋p⦌) (g' : ⦋b⦌ ⟶ ⦋q⦌) :
    bisimplicialSimplexPull X f g ≫ bisimplicialSimplexPull X f' g' =
      bisimplicialSimplexPull X (f' ≫ f) (g' ≫ g) := by
  dsimp only [bisimplicialSimplexPull]
  rw [← Functor.map_comp]
  rfl

theorem bisimplicialSimplexPull_comp_apply {p q m n a b : ℕ}
    (f : ⦋p⦌ ⟶ ⦋m⦌) (g : ⦋q⦌ ⟶ ⦋n⦌)
    (f' : ⦋a⦌ ⟶ ⦋p⦌) (g' : ⦋b⦌ ⟶ ⦋q⦌)
    (x : (X.obj (op ⦋m⦌)).obj (op ⦋n⦌)) :
    bisimplicialSimplexPull X f' g' (bisimplicialSimplexPull X f g x) =
      bisimplicialSimplexPull X (f' ≫ f) (g' ≫ g) x :=
  congrArg (fun z => z x) (bisimplicialSimplexPull_comp X f g f' g')

theorem alexanderWhitneySimplex_eq_pull (p q n : ℕ) (h : p + q = n)
    (x : (bisimplicialDiagonal X).obj (op ⦋n⦌)) :
    alexanderWhitneySimplex X p q n h x =
      bisimplicialSimplexPull X (alexanderWhitneyFront p q n h)
        (alexanderWhitneyBack p q n h) x :=
  (bisimplicialSimplexPull_apply X _ _ x).symm

theorem bisimplicialSimplexPull_id_right {p m n : ℕ} (f : ⦋p⦌ ⟶ ⦋m⦌) :
    bisimplicialSimplexPull X f (𝟙 ⦋n⦌) = (X.map f.op).app (op ⦋n⦌) := by
  simp [bisimplicialSimplexPull, Functor.uncurry]

theorem bisimplicialSimplexPull_id_left {q m n : ℕ} (g : ⦋q⦌ ⟶ ⦋n⦌) :
    bisimplicialSimplexPull X (𝟙 ⦋m⦌) g = (X.obj (op ⦋m⦌)).map g.op := by
  simp [bisimplicialSimplexPull, Functor.uncurry]

theorem alexanderWhitneySimplex_face_early (p q n : ℕ) (h : p + q = n)
    (i : Fin (p + 1)) (x : (bisimplicialDiagonal X).obj (op ⦋n + 1⦌)) :
    alexanderWhitneySimplex X p q n h
        ((bisimplicialDiagonal X).δ ⟨i.val, by omega⟩ x) =
      (X.map (SimplexCategory.δ i.castSucc).op).app (op ⦋q⦌)
        (alexanderWhitneySimplex X (p + 1) q (n + 1) (by omega) x) := by
  rw [alexanderWhitneySimplex_eq_pull, alexanderWhitneySimplex_eq_pull,
    ← bisimplicialSimplexPull_id_right]
  change bisimplicialSimplexPull X _ _
      (bisimplicialSimplexPull X (SimplexCategory.δ _) (SimplexCategory.δ _) x) = _
  rw [bisimplicialSimplexPull_comp_apply, bisimplicialSimplexPull_comp_apply,
    Category.id_comp, alexanderWhitneyFront_face_early p q n h,
    alexanderWhitneyBack_face_early p q n h]

theorem alexanderWhitneySimplex_face_late (p q n : ℕ) (h : p + q = n)
    (j : Fin (q + 1)) (x : (bisimplicialDiagonal X).obj (op ⦋n + 1⦌)) :
    alexanderWhitneySimplex X p q n h
        ((bisimplicialDiagonal X).δ ⟨p + 1 + j.val, by omega⟩ x) =
      (X.obj (op ⦋p⦌)).δ j.succ
        (alexanderWhitneySimplex X p (q + 1) (n + 1) (by omega) x) := by
  rw [alexanderWhitneySimplex_eq_pull, alexanderWhitneySimplex_eq_pull]
  change bisimplicialSimplexPull X _ _
      (bisimplicialSimplexPull X (SimplexCategory.δ _) (SimplexCategory.δ _) x) =
    (X.obj (op ⦋p⦌)).map (SimplexCategory.δ j.succ).op _
  rw [← bisimplicialSimplexPull_id_left, bisimplicialSimplexPull_comp_apply,
    bisimplicialSimplexPull_comp_apply, Category.id_comp,
    alexanderWhitneyFront_face_late p q n h, alexanderWhitneyBack_face_late p q n h]

theorem alexanderWhitneySimplex_face_middle (p q n : ℕ) (h : p + q = n)
    (x : (bisimplicialDiagonal X).obj (op ⦋n + 1⦌)) :
    (X.map (SimplexCategory.δ (Fin.last (p + 1))).op).app (op ⦋q⦌)
        (alexanderWhitneySimplex X (p + 1) q (n + 1) (by omega) x) =
      (X.obj (op ⦋p⦌)).δ (0 : Fin (q + 2))
        (alexanderWhitneySimplex X p (q + 1) (n + 1) (by omega) x) := by
  rw [alexanderWhitneySimplex_eq_pull, alexanderWhitneySimplex_eq_pull,
    ← bisimplicialSimplexPull_id_right]
  change _ = (X.obj (op ⦋p⦌)).map (SimplexCategory.δ (0 : Fin (q + 2))).op _
  rw [← bisimplicialSimplexPull_id_left, bisimplicialSimplexPull_comp_apply,
    bisimplicialSimplexPull_comp_apply, Category.id_comp, Category.id_comp,
    alexanderWhitneyFront_face_middle p q n h, alexanderWhitneyBack_face_middle p q n h]

end Sharpness
