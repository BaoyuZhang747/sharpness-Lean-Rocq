import Sharpness.GrothendieckDiagonalString
import Sharpness.CostructuredGrothendieckSection

/-! The actual projection of a diagonal comma string. This proves both
its object and arrow components, hence the full projected string,
without any homotopy-colimit comparison premise. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace Sharpness
open CategoryTheory Simplicial Opposite
variable {C D : Type u} [Category.{u} C] [Category.{u} D] (T : C ⥤ D)

theorem costructuredDiagonalString_projection_obj {n : ℕ} (s : ComposableArrows D n)
    (x : ComposableArrows (CostructuredArrow T (chainHead s)) n) (i : Fin (n+1)) :
    (CostructuredArrow.grothendieckProj T).obj
      ((grothendieckDiagonalString (CostructuredArrow.functor T) s x).obj i) =
        (x.obj i).left := rfl

theorem costructuredDiagonalString_projection_map {n : ℕ} (s : ComposableArrows D n)
    (x : ComposableArrows (CostructuredArrow T (chainHead s)) n)
    {i j : Fin (n+1)} (f : i ⟶ j) :
    (CostructuredArrow.grothendieckProj T).map
      ((grothendieckDiagonalString (CostructuredArrow.functor T) s x).map f) =
        (x.map f).left := by
  change ((eqToHom ((categoryStringHeadDiagram (CostructuredArrow.functor T) s).naturality f).symm).toNatTrans.app (x.obj i) ≫
    ((categoryStringHeadDiagram (CostructuredArrow.functor T) s).app j).toFunctor.map (x.map f)).left = _
  rw [Cat.eqToHom_app]
  change (CostructuredArrow.proj T (s.obj j)).map (eqToHom _ ≫
    ((categoryStringHeadDiagram (CostructuredArrow.functor T) s).app j).toFunctor.map (x.map f)) = _
  rw [(CostructuredArrow.proj T (s.obj j)).map_comp, eqToHom_map]
  change (𝟙 (x.obj i).left) ≫ (x.map f).left = (x.map f).left
  exact Category.id_comp ((x.map f).left)

theorem costructuredDiagonalString_projection {n : ℕ} (s : ComposableArrows D n)
    (x : ComposableArrows (CostructuredArrow T (chainHead s)) n) :
    grothendieckDiagonalString (CostructuredArrow.functor T) s x ⋙
      CostructuredArrow.grothendieckProj T = x ⋙ CostructuredArrow.proj T (chainHead s) := by
  refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
  intro i j f
  simpa only [Functor.comp_map, CostructuredArrow.proj_map,
    eqToHom_refl, Category.comp_id, Category.id_comp] using
    costructuredDiagonalString_projection_map T s x f

end Sharpness
