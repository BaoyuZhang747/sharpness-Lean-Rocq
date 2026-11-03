import Sharpness.CostructuredDiagonalCommaNaturality
import Sharpness.SimplicialReplacementAugmentation

/-! The actual simplicial comparison from the comma-nerve diagonal
to the nerve of its Grothendieck category. Naturality is proved for
every simplicial operator, and projection agrees with the actual
forgetful augmentation. No weak-equivalence premise is used. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace Sharpness
open CategoryTheory Simplicial Opposite
variable {C D : Type u} [Category.{u} C] [Category.{u} D] (T : C ⥤ D)

def costructuredNerveDiagram : D ⥤ SSet.{u} :=
  CostructuredArrow.functor T ⋙ CategoryTheory.nerveFunctor

def costructuredDiagonalCommaMap :
    simplicialReplacementDiagonal (costructuredNerveDiagram T) ⟶
      CategoryTheory.nerve (Comma T (𝟭 D)) where
  app i := ↾fun x => costructuredDiagonalCommaString T x.1 x.2
  naturality {i j} f := by
    apply ConcreteCategory.ext_apply
    rintro ⟨s, x⟩
    exact costructuredDiagonalCommaString_restrict T s x
      (SimplexCategory.toCat.map f.unop).toFunctor

def costructuredDiagonalGrothendieckMap :
    simplicialReplacementDiagonal (costructuredNerveDiagram T) ⟶
      CategoryTheory.nerve (Grothendieck (CostructuredArrow.functor T)) :=
  costructuredDiagonalCommaMap T ≫
    CategoryTheory.nerveMap (CostructuredArrow.commaToGrothendieckPrecompFunctor T (𝟭 D))

def costructuredNerveCocone : costructuredNerveDiagram T ⟶
    (Functor.const D).obj (CategoryTheory.nerve C) where
  app P := CategoryTheory.nerveMap (CostructuredArrow.proj T P)
  naturality {P Q} f := by
    change CategoryTheory.nerveMap (CostructuredArrow.map f) ≫
        CategoryTheory.nerveMap (CostructuredArrow.proj T Q) =
      CategoryTheory.nerveMap (CostructuredArrow.proj T P) ≫ 𝟙 _
    rw [Category.comp_id]
    rfl

theorem costructuredDiagonalCommaMap_projection :
    costructuredDiagonalCommaMap T ≫ CategoryTheory.nerveMap (Comma.fst T (𝟭 D)) =
      simplicialReplacementDiagonalAugmentation (costructuredNerveDiagram T)
        (costructuredNerveCocone T) := by
  apply NatTrans.ext
  funext i
  apply ConcreteCategory.ext_apply
  rintro ⟨s, x⟩
  exact costructuredDiagonalCommaString_fst T s x

theorem costructuredDiagonalGrothendieckMap_projection :
    costructuredDiagonalGrothendieckMap T ≫
        CategoryTheory.nerveMap (CostructuredArrow.grothendieckProj T) =
      simplicialReplacementDiagonalAugmentation (costructuredNerveDiagram T)
        (costructuredNerveCocone T) := by
  apply NatTrans.ext
  funext i
  apply ConcreteCategory.ext_apply
  rintro ⟨s, x⟩
  exact costructuredDiagonalCommaString_fst T s x

end Sharpness
