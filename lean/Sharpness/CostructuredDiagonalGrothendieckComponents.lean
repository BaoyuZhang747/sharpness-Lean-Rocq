import Sharpness.CostructuredDiagonalComparison
import Sharpness.CostructuredDiagonalProjection

/-! The concrete simplicial comparison agrees with the actual
Grothendieck string functor, on all vertices and arrows. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace Sharpness
open CategoryTheory Simplicial Opposite
variable {C D : Type u} [Category.{u} C] [Category.{u} D] (T : C ⥤ D)

theorem costructuredDiagonalString_toComma {n : ℕ} (s : ComposableArrows D n)
    (x : ComposableArrows (CostructuredArrow T (chainHead s)) n) :
    grothendieckDiagonalString (CostructuredArrow.functor T) s x ⋙
        CostructuredArrow.grothendieckPrecompFunctorToComma T (𝟭 D) =
      costructuredDiagonalCommaString T s x := by
  refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
  intro i j f
  simp only [eqToHom_refl, Category.comp_id, Category.id_comp]
  apply Comma.hom_ext
  · exact costructuredDiagonalString_projection_map T s x f
  · rfl

theorem costructuredDiagonalGrothendieckMap_component (i : SimplexCategoryᵒᵖ)
    (s : ComposableArrows D i.unop.len)
    (x : ComposableArrows (CostructuredArrow T (chainHead s)) i.unop.len) :
    (costructuredDiagonalGrothendieckMap T).app i ⟨s, x⟩ =
      grothendieckDiagonalString (CostructuredArrow.functor T) s x := by
  change costructuredDiagonalCommaString T s x ⋙
      CostructuredArrow.commaToGrothendieckPrecompFunctor T (𝟭 D) = _
  rw [← costructuredDiagonalString_toComma T s x]
  rfl

end Sharpness
