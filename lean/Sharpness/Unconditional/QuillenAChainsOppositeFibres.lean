import Sharpness.Unconditional.NerveOppositeChains
import Sharpness.Unconditional.NerveAdjunctionChains
import Mathlib.CategoryTheory.PUnit

/-! Actual transport of fibre-to-point quasi-isomorphisms through categorical
equivalences and opposite categories. This fixes the comma orientation. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u vA uA

namespace Sharpness
open CategoryTheory CategoryTheory.Limits Opposite

variable {C D : Type u} [Category.{u} C] [Category.{u} D]
variable {A : Type uA} [Category.{vA} A] [Preadditive A]
  [HasCoproducts.{u} A] [CategoryWithHomology A]

theorem nerveStar_quasiIso_of_equivalence (e : C ≌ D) (R : A)
    (h : QuasiIso (SSet.chainComplexMap (nerveMap (Functor.star.{u} C)) R)) :
    QuasiIso (SSet.chainComplexMap (nerveMap (Functor.star.{u} D)) R) := by
  let J := (SSet.chainComplexFunctor A).obj R
  haveI : QuasiIso (J.map (nerveMap e.functor)) :=
    nerveAdjunction_left_quasiIso e.toAdjunction R
  have he : e.functor ⋙ Functor.star.{u} D = Functor.star.{u} C :=
    Functor.punit_ext' _ _
  haveI : QuasiIso (J.map (nerveMap e.functor) ≫ J.map (nerveMap (Functor.star.{u} D))) := by
    rw [← J.map_comp]
    change QuasiIso (J.map (nerveMap (e.functor ⋙ Functor.star.{u} D)))
    rw [he]
    exact h
  exact quasiIso_of_comp_left (J.map (nerveMap e.functor))
    (J.map (nerveMap (Functor.star.{u} D)))

theorem nerveStar_op_quasiIso (R : A)
    (h : QuasiIso (SSet.chainComplexMap (nerveMap (Functor.star.{u} C)) R)) :
    QuasiIso (SSet.chainComplexMap (nerveMap (Functor.star.{u} Cᵒᵖ)) R) := by
  let J := (SSet.chainComplexFunctor A).obj R
  let e := Discrete.opposite PUnit.{u+1}
  haveI : QuasiIso (J.map (nerveMap (Functor.star.{u} C).op)) :=
    (nerveOppositeChainMap_quasiIso_iff (Functor.star.{u} C) R).mpr h
  haveI : QuasiIso (J.map (nerveMap e.functor)) :=
    nerveAdjunction_left_quasiIso e.toAdjunction R
  have he : (Functor.star.{u} C).op ⋙ e.functor = Functor.star.{u} Cᵒᵖ :=
    Functor.punit_ext' _ _
  change QuasiIso (J.map (nerveMap (Functor.star.{u} Cᵒᵖ)))
  rw [← he]
  change QuasiIso (J.map (nerveMap (Functor.star.{u} C).op ≫ nerveMap e.functor))
  rw [J.map_comp]
  infer_instance

theorem costructured_op_fibre_quasiIso_of_structured (T : C ⥤ D) (R : A)
    (h : ∀ d, QuasiIso (SSet.chainComplexMap
      (nerveMap (Functor.star.{u} (StructuredArrow d T))) R)) (d : Dᵒᵖ) :
    QuasiIso (SSet.chainComplexMap
      (nerveMap (Functor.star.{u} (CostructuredArrow T.op d))) R) :=
  nerveStar_quasiIso_of_equivalence (structuredArrowOpEquivalence T d.unop) R
    (nerveStar_op_quasiIso R (h d.unop))

end Sharpness
