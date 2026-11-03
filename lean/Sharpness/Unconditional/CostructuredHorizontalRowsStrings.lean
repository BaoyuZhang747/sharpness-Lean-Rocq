import Sharpness.CostructuredDiagonalComparison
import Mathlib.CategoryTheory.Comma.Over.Basic

/-! A comma-category string is recovered from its projected string and
its last arrow. Dually, a coslice string is recovered from its projected
string and its first arrow. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace Sharpness
open CategoryTheory Simplicial Opposite
variable {C D : Type u} [Category.{u} C] [Category.{u} D] (T : C ⥤ D)

def categoryStringTerminalArrow {q : ℕ} (c : ComposableArrows C q) (i : Fin (q+1)) :
    c.obj i ⟶ c.obj (Fin.last q) := c.map (homOfLE (Fin.le_last i))

theorem categoryStringTerminalArrow_comp {q : ℕ} (c : ComposableArrows C q)
    {i j : Fin (q+1)} (f : i ⟶ j) :
    c.map f ≫ categoryStringTerminalArrow c j = categoryStringTerminalArrow c i := by
  rw [categoryStringTerminalArrow, ← c.map_comp]
  exact congrArg c.map (Subsingleton.elim _ _)

@[simp] theorem categoryStringTerminalArrow_last {q : ℕ} (c : ComposableArrows C q) :
    categoryStringTerminalArrow c (Fin.last q) = 𝟙 _ := by
  exact c.map_id _

/-- Extend the last arrow backwards along a fixed C-string. -/
def costructuredStringFromLast {q : ℕ} (c : ComposableArrows C q) {d : D}
    (a : T.obj (c.obj (Fin.last q)) ⟶ d) : ComposableArrows (CostructuredArrow T d) q where
  obj i := CostructuredArrow.mk (T.map (categoryStringTerminalArrow c i) ≫ a)
  map {i j} f := CostructuredArrow.homMk (c.map f) (by
    change T.map (c.map f) ≫ (T.map (categoryStringTerminalArrow c j) ≫ a) =
      T.map (categoryStringTerminalArrow c i) ≫ a
    rw [← Category.assoc, ← T.map_comp, categoryStringTerminalArrow_comp])
  map_id i := by
    apply CostructuredArrow.hom_ext
    exact c.map_id i
  map_comp f g := by
    apply CostructuredArrow.hom_ext
    exact c.map_comp f g

theorem costructuredStringFromLast_projection {q : ℕ} (c : ComposableArrows C q) {d : D}
    (a : T.obj (c.obj (Fin.last q)) ⟶ d) :
    costructuredStringFromLast T c a ⋙ CostructuredArrow.proj T d = c := rfl

/-- Every actual comma string is determined by the last comma arrow. -/
theorem costructuredStringFromLast_recover {q : ℕ} {d : D}
    (x : ComposableArrows (CostructuredArrow T d) q) :
    costructuredStringFromLast T (x ⋙ CostructuredArrow.proj T d)
      (x.obj (Fin.last q)).hom = x := by
  refine CategoryTheory.Functor.ext (fun i => ?_) ?_
  · refine CostructuredArrow.obj_ext
      ((costructuredStringFromLast T (x ⋙ CostructuredArrow.proj T d)
        (x.obj (Fin.last q)).hom).obj i) (x.obj i) rfl ?_
    simp only [eqToHom_refl, T.map_id, Category.id_comp]
    exact (CostructuredArrow.w (x.map (homOfLE (Fin.le_last i)))).symm
  · intro i j f
    apply CostructuredArrow.hom_ext
    simp only [CostructuredArrow.comp_left, CostructuredArrow.eqToHom_left]
    change (x.map f).left = (𝟙 _) ≫ (x.map f).left ≫ (𝟙 _)
    simp only [Category.id_comp, Category.comp_id]

/-- Extend a first arrow forwards along a fixed D-string. -/
def underStringFromHead {p : ℕ} (s : ComposableArrows D p) {d : D}
    (a : d ⟶ s.obj 0) : ComposableArrows (Under d) p where
  obj i := Under.mk (a ≫ categoryStringInitialArrow s i)
  map {i j} f := Under.homMk (s.map f) (by
    change (a ≫ categoryStringInitialArrow s i) ≫ s.map f =
      a ≫ categoryStringInitialArrow s j
    rw [Category.assoc, categoryStringInitialArrow_comp])
  map_id i := by
    apply StructuredArrow.hom_ext
    exact s.map_id i
  map_comp f g := by
    apply StructuredArrow.hom_ext
    exact s.map_comp f g

theorem underStringFromHead_projection {p : ℕ} (s : ComposableArrows D p) {d : D}
    (a : d ⟶ s.obj 0) : underStringFromHead s a ⋙ Under.forget d = s := rfl

@[simp] theorem underStringFromHead_first {p : ℕ} (s : ComposableArrows D p) {d : D}
    (a : d ⟶ s.obj 0) : ((underStringFromHead s a).obj 0).hom = a := by
  change a ≫ s.map _ = a
  have he : s.map (homOfLE (show (0 : Fin (p+1)) ≤ 0 from le_rfl)) = 𝟙 _ := s.map_id _
  rw [he, Category.comp_id]

/-- Every actual coslice string is determined by its first arrow. -/
theorem underStringFromHead_recover {p : ℕ} {d : D}
    (x : ComposableArrows (Under d) p) :
    underStringFromHead (x ⋙ Under.forget d) (x.obj 0).hom = x := by
  refine CategoryTheory.Functor.ext (fun i => ?_) ?_
  · refine StructuredArrow.obj_ext
      ((underStringFromHead (x ⋙ Under.forget d) (x.obj 0).hom).obj i) (x.obj i) rfl ?_
    simp only [eqToHom_refl, CategoryTheory.Functor.map_id, Category.comp_id]
    exact Under.w (x.map (homOfLE (show (0 : Fin (p+1)) ≤ i from Nat.zero_le _)))
  · intro i j f
    apply StructuredArrow.hom_ext
    simp only [Under.comp_right, Under.eqToHom_right]
    change (x.map f).right = (𝟙 _) ≫ (x.map f).right ≫ (𝟙 _)
    simp only [Category.id_comp, Category.comp_id]

/-- Compatibility with every order-map functor in the varying D-string. -/
theorem underStringFromHead_restrict {p r : ℕ} (s : ComposableArrows D p) {d : D}
    (a : d ⟶ s.obj 0) (k : Fin (r+1) ⥤ Fin (p+1)) :
    underStringFromHead (k ⋙ s) (a ≫ categoryStringInitialArrow s (k.obj 0)) =
      k ⋙ underStringFromHead s a := by
  refine CategoryTheory.Functor.ext (fun i => ?_) ?_
  · refine StructuredArrow.obj_ext
      ((underStringFromHead (k ⋙ s) (a ≫ categoryStringInitialArrow s (k.obj 0))).obj i)
      ((underStringFromHead s a).obj (k.obj i)) rfl ?_
    simp only [eqToHom_refl, CategoryTheory.Functor.map_id, Category.comp_id]
    change (a ≫ categoryStringInitialArrow s (k.obj 0)) ≫
      s.map (k.map (homOfLE (show (0 : Fin (r+1)) ≤ i from Nat.zero_le _))) = _
    rw [Category.assoc, categoryStringInitialArrow_comp]
    rfl
  · intro i j f
    apply StructuredArrow.hom_ext
    simp only [Under.comp_right, Under.eqToHom_right]
    change s.map (k.map f) = (𝟙 _) ≫ s.map (k.map f) ≫ (𝟙 _)
    simp only [Category.id_comp, Category.comp_id]

end Sharpness
