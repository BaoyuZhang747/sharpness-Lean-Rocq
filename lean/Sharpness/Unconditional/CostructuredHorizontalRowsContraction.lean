import Sharpness.Unconditional.CostructuredHorizontalRowsAugmentation
import Sharpness.Unconditional.NerveNaturalTransformation
import Mathlib.Algebra.Homology.QuasiIso

/-! Contract each actual coslice component by its identity initial object.
The resulting componentwise simplicial prism contracts the horizontal-row
projection and induces a native quasi-isomorphism on simplicial chains. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u w z

namespace Sharpness
open CategoryTheory CategoryTheory.Limits Simplicial Opposite MonoidalCategory
variable {C D : Type u} [Category.{u} C] [Category.{u} D] (T : C ⥤ D)

def underInitialTransformation (d : D) :
    (CategoryTheory.Functor.const (Under d)).obj (Under.mk (𝟙 d)) ⟶ 𝟭 (Under d) where
  app x := Under.homMk x.hom (by
    change (𝟙 d) ≫ x.hom = x.hom
    exact Category.id_comp _)
  naturality {x y} f := by
    apply StructuredArrow.hom_ext
    change (𝟙 d) ≫ y.hom = x.hom ≫ f.right
    exact (Category.id_comp _).trans (Under.w f).symm

def costructuredHorizontalRowModelSection (q : ℕ) :
    (CategoryTheory.Functor.const SimplexCategoryᵒᵖ).obj (ComposableArrows C q) ⟶
      costructuredHorizontalRowModel T q where
  app p := ↾fun c => ⟨c, (CategoryTheory.Functor.const (Fin (p.unop.len+1))).obj
    (Under.mk (𝟙 (T.obj (c.obj (Fin.last q)))))⟩
  naturality {_ _} f := rfl

theorem costructuredHorizontalRowModelSection_projection (q : ℕ) :
    costructuredHorizontalRowModelSection T q ≫ costructuredHorizontalRowModelProjection T q =
      𝟙 _ := rfl

def costructuredHorizontalRowModelPrism (q : ℕ) :
    costructuredHorizontalRowModel T q ⊗ Δ[1] ⟶ costructuredHorizontalRowModel T q where
  app p := ↾fun x => ⟨x.1.1,
    (nerveNaturalTransformationMap
      (underInitialTransformation (T.obj (x.1.1.obj (Fin.last q))))).app p (x.1.2, x.2)⟩
  naturality {p r} f := by
    apply ConcreteCategory.ext_apply
    rintro ⟨⟨c, x⟩, t⟩
    apply congrArg (fun y => (⟨c, y⟩ : (costructuredHorizontalRowModel T q).obj r))
    exact congrArg (fun h => h (x, t))
      ((nerveNaturalTransformationMap (underInitialTransformation
        (T.obj (c.obj (Fin.last q))))).naturality f)

theorem costructuredHorizontalRowModelPrism_zero (q : ℕ) :
    SSet.ι₀ ≫ costructuredHorizontalRowModelPrism T q =
      costructuredHorizontalRowModelProjection T q ≫ costructuredHorizontalRowModelSection T q := by
  apply NatTrans.ext
  funext p
  apply ConcreteCategory.ext_apply
  rintro ⟨c, x⟩
  apply congrArg (fun y => (⟨c, y⟩ : (costructuredHorizontalRowModel T q).obj p))
  exact congrArg (fun h => h.app p x)
    (nerveNaturalTransformationMap_zero (underInitialTransformation (T.obj (c.obj (Fin.last q)))))

theorem costructuredHorizontalRowModelPrism_one (q : ℕ) :
    SSet.ι₁ ≫ costructuredHorizontalRowModelPrism T q = 𝟙 _ := by
  apply NatTrans.ext
  funext p
  apply ConcreteCategory.ext_apply
  rintro ⟨c, x⟩
  apply congrArg (fun y => (⟨c, y⟩ : (costructuredHorizontalRowModel T q).obj p))
  exact congrArg (fun h => h.app p x)
    (nerveNaturalTransformationMap_one (underInitialTransformation (T.obj (c.obj (Fin.last q)))))

def costructuredHorizontalRowModelContraction (q : ℕ) :
    SSet.Homotopy
      (costructuredHorizontalRowModelProjection T q ≫ costructuredHorizontalRowModelSection T q)
      (𝟙 (costructuredHorizontalRowModel T q)) where
  h := costructuredHorizontalRowModelPrism T q
  h₀ := costructuredHorizontalRowModelPrism_zero T q
  h₁ := costructuredHorizontalRowModelPrism_one T q
  rel := by
    ext p x
    exact False.elim x.1.property

variable {A : Type w} [Category.{z} A] [Preadditive A] [HasCoproducts.{u} A]

def costructuredHorizontalRowModelChainHomotopyEquiv (q : ℕ) (R : A) :
    HomotopyEquiv ((costructuredHorizontalRowModel T q).chainComplex R)
      (SSet.chainComplex ((CategoryTheory.Functor.const SimplexCategoryᵒᵖ).obj
        (ComposableArrows C q)) R) where
  hom := SSet.chainComplexMap (costructuredHorizontalRowModelProjection T q) R
  inv := SSet.chainComplexMap (costructuredHorizontalRowModelSection T q) R
  homotopyHomInvId := by
    have h := (costructuredHorizontalRowModelContraction T q).chainComplexMap R
    have hc := ((SSet.chainComplexFunctor A).obj R).map_comp
      (costructuredHorizontalRowModelProjection T q) (costructuredHorizontalRowModelSection T q)
    have hi := ((SSet.chainComplexFunctor A).obj R).map_id (costructuredHorizontalRowModel T q)
    simpa only [hc, hi] using h
  homotopyInvHomId := Homotopy.ofEq (by
    rw [← ((SSet.chainComplexFunctor A).obj R).map_comp,
      costructuredHorizontalRowModelSection_projection,
      ((SSet.chainComplexFunctor A).obj R).map_id])

theorem costructuredHorizontalRowAugmentation_quasiIso [CategoryWithHomology A]
    (q : ℕ) (R : A) : QuasiIso (SSet.chainComplexMap (costructuredHorizontalRowAugmentation T q) R) := by
  haveI : QuasiIso (SSet.chainComplexMap (costructuredHorizontalRowModelProjection T q) R) :=
    (costructuredHorizontalRowModelChainHomotopyEquiv T q R).quasiIso_hom
  have he := congrArg ((SSet.chainComplexFunctor A).obj R).map
    (costructuredHorizontalRowIso_projection T q)
  rw [((SSet.chainComplexFunctor A).obj R).map_comp] at he
  change QuasiIso (((SSet.chainComplexFunctor A).obj R).map
    (costructuredHorizontalRowAugmentation T q))
  rw [← he]
  infer_instance

end Sharpness
