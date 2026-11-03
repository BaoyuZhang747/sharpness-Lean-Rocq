import Sharpness.CostructuredDiagonalCommaString

/-! Naturality of the concrete comma string under every order-map
functor, including those defining faces and degeneracies. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace Sharpness
open CategoryTheory Simplicial Opposite
variable {C D : Type u} [Category.{u} C] [Category.{u} D] (T : C ⥤ D)

def costructuredShiftString {n m : ℕ} (s : ComposableArrows D n)
    (x : ComposableArrows (CostructuredArrow T (chainHead s)) n)
    (r : Fin (m+1) ⥤ Fin (n+1)) :
    ComposableArrows (CostructuredArrow T (chainHead (r ⋙ s))) m :=
  r ⋙ x ⋙ CostructuredArrow.map (categoryStringInitialArrow s (r.obj 0))

theorem costructuredDiagonalCommaString_restrict_obj {n m : ℕ} (s : ComposableArrows D n)
    (x : ComposableArrows (CostructuredArrow T (chainHead s)) n)
    (r : Fin (m+1) ⥤ Fin (n+1)) (i : Fin (m+1)) :
    (costructuredDiagonalCommaString T (r ⋙ s) (costructuredShiftString T s x r)).obj i =
      (costructuredDiagonalCommaString T s x).obj (r.obj i) := by
  apply congrArg (fun a : T.obj (x.obj (r.obj i)).left ⟶ s.obj (r.obj i) =>
    (⟨(x.obj (r.obj i)).left, s.obj (r.obj i), a⟩ : Comma T (𝟭 D)))
  change ((x.obj (r.obj i)).hom ≫ categoryStringInitialArrow s (r.obj 0)) ≫
      s.map (r.map (homOfLE (show (0 : Fin (m+1)) ≤ i from Nat.zero_le _))) = _
  rw [Category.assoc, categoryStringInitialArrow_comp]

theorem costructuredDiagonalCommaString_restrict {n m : ℕ} (s : ComposableArrows D n)
    (x : ComposableArrows (CostructuredArrow T (chainHead s)) n)
    (r : Fin (m+1) ⥤ Fin (n+1)) :
    costructuredDiagonalCommaString T (r ⋙ s) (costructuredShiftString T s x r) =
      r ⋙ costructuredDiagonalCommaString T s x := by
  refine CategoryTheory.Functor.ext (costructuredDiagonalCommaString_restrict_obj T s x r) ?_
  intro i j f
  apply Comma.hom_ext
  · simp only [Comma.comp_left, Comma.eqToHom_left]
    change (x.map (r.map f)).left = (𝟙 _) ≫ (x.map (r.map f)).left ≫ (𝟙 _)
    simp only [Category.id_comp, Category.comp_id]
  · simp only [Comma.comp_right, Comma.eqToHom_right]
    change s.map (r.map f) = (𝟙 _) ≫ s.map (r.map f) ≫ (𝟙 _)
    simp only [Category.id_comp, Category.comp_id]

end Sharpness
