import Sharpness.LinkingCategory
import Sharpness.SmallNerveMap

/-! BLO Definition 1.7 on actual subgroup objects and raw fusion maps.
The free central action and its orbit fibers are expressed as unique
central translates. The distinguished monomorphisms and axiom (C) are
part of the definition of a linking system, never sharpness hypotheses.

Our existing fusion convention conjugates x by s as s⁻¹*x*s. Thus the
usual left-conjugation map in BLO's distinguished group homomorphism
is written using inner(g⁻¹); this normalizes the native Aut multiplication.
-/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness.FusionSystem
open CategoryTheory
variable {S : Type u} [Group S] (F : FusionSystem S)

structure CentricLinkingSystem extends F.LinkingCategoryData where
  distinguished : ∀ P : toLinkingCategoryData.Object, P.as.val →* Aut P
  distinguished_injective : ∀ P, Function.Injective (distinguished P)
  projection_surjective : ∀ P Q : toLinkingCategoryData.Object,
    Function.Surjective (toLinkingCategoryData.projection.map : (P ⟶ Q) → _)
  central_fiber : ∀ {P Q : toLinkingCategoryData.Object} (f g : P ⟶ Q),
    toLinkingCategoryData.projection.map f = toLinkingCategoryData.projection.map g ↔
      ∃! z : Subgroup.center P.as.val, (distinguished P z.val).hom ≫ f = g
  project_distinguished : ∀ (P : toLinkingCategoryData.Object) (x : P.as.val),
    toLinkingCategoryData.projection.map (distinguished P x).hom =
      F.inner (toLinkingCategoryData.rawObject P) x⁻¹
  commutation : ∀ {P Q : toLinkingCategoryData.Object} (f : P ⟶ Q) (x : P.as.val),
    (distinguished P x).hom ≫ f =
      f ≫ (distinguished Q ((toLinkingCategoryData.projection.map f).val x)).hom

namespace CentricLinkingSystem
variable {F} (L : F.CentricLinkingSystem)

abbrev Object := L.toLinkingCategoryData.Object
abbrev projection : L.Object ⥤ F.Object := L.toLinkingCategoryData.projection
abbrev classifyingSpace : TopCat.{u} := L.toLinkingCategoryData.classifyingSpace

def distinguishedFunctor (P : L.Object) : SingleObj P.as.val ⥤ L.Object :=
  SingleObj.functor ((Aut.toEnd P).comp (L.distinguished P))

theorem distinguishedFunctor_map (P : L.Object) (g : P.as.val) :
    (L.distinguishedFunctor P).map (X := SingleObj.star P.as.val)
      (Y := SingleObj.star P.as.val) g = (L.distinguished P g).hom := rfl

def distinguishedNaturality {P Q : L.Object} (f : P ⟶ Q) :
    L.distinguishedFunctor P ⟶
      (L.projection.map f).val.toFunctor ⋙ L.distinguishedFunctor Q :=
  SingleObj.natTrans f (fun g => L.commutation f g)

def groupClassifyingSpace (P : L.Object) : TopCat.{u} :=
  SSet.toTop.obj (CategoryTheory.nerve (SingleObj P.as.val))

/-- The actual iota_P of Corollary 4.1, induced by delta_P. -/
def subgroupClassifyingMap (P : L.Object) : L.groupClassifyingSpace P ⟶ L.classifyingSpace :=
  SSet.toTop.map (nerveMapSingleObj P.as.val (L.distinguishedFunctor P))

def classifyingMapOfProjection {P Q : L.Object} (f : P ⟶ Q) :
    L.groupClassifyingSpace P ⟶ L.groupClassifyingSpace Q :=
  SSet.toTop.map (CategoryTheory.nerveMap (L.projection.map f).val.toFunctor)

end CentricLinkingSystem
end Sharpness.FusionSystem
