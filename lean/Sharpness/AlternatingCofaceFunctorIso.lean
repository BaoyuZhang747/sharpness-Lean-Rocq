import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
import Mathlib.Algebra.Homology.Additive

/-! An additive functor commutes with the actual alternating-coface
complex. In particular it preserves its concrete finite alternating
sum, rather than only the objects of the cosimplicial diagram. -/
set_option autoImplicit false
noncomputable section
universe u v u' v'
namespace Sharpness
open CategoryTheory Simplicial
variable {C : Type u} [Category.{v} C] [Preadditive C]
    {D : Type u'} [Category.{v'} D] [Preadditive D]

theorem alternatingCoface_d (X : CosimplicialObject C) (n : ℕ) :
    ((AlgebraicTopology.alternatingCofaceMapComplex C).obj X).d n (n+1) =
      ∑ i : Fin (n+2), (-1 : ℤ)^(i : ℕ) • X.δ i :=
  CochainComplex.of_d (fun n => X.obj ⦋n⦌)
    (AlgebraicTopology.AlternatingCofaceMapComplex.objD X) n

set_option backward.isDefEq.respectTransparency false in
def alternatingCofaceFunctorIso (F : C ⥤ D) [F.Additive] (X : CosimplicialObject C) :
    (F.mapHomologicalComplex (ComplexShape.up ℕ)).obj
        ((AlgebraicTopology.alternatingCofaceMapComplex C).obj X) ≅
      (AlgebraicTopology.alternatingCofaceMapComplex D).obj (X ⋙ F) :=
  HomologicalComplex.Hom.isoOfComponents (fun _ => Iso.refl _) (by
    intro i j hij
    have hj : i+1 = j := hij
    subst j
    simp only [Iso.refl_hom, Category.id_comp, Category.comp_id, Functor.mapHomologicalComplex_obj_d,
      alternatingCoface_d, Functor.map_sum, Functor.map_zsmul, CosimplicialObject.δ, Functor.comp_map])

end Sharpness
