import Sharpness.Unconditional.LinkingCommaReflectionFiber
import Mathlib.CategoryTheory.Adjunction.Basic

/-! A left adjoint to the actual distinguished subgroup functor into
the linking/orbit comma category. The choices are actual orbit lifts;
the adjunction is obtained from the proved target-subgroup torsor. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace Sharpness.FusionSystem.CentricLinkingSystem
open CategoryTheory
variable {S : Type u} [Group S] {F : FusionSystem S} (L : F.CentricLinkingSystem)

def linkingCommaBase (P : L.Object)
    (X : L.subgroupDiagramCategory (L.orbitProjection.obj P)) :
    X ⟶ (L.subgroupComparisonFunctor P).obj (SingleObj.star P.as.val) :=
  CostructuredArrow.homMk (L.liftOrbitArrow X.hom) (by
    change L.orbitProjection.map (L.liftOrbitArrow X.hom) ≫ 𝟙 _ = X.hom
    rw [Category.comp_id]
    exact L.orbitProjection_liftOrbitArrow X.hom)

def linkingCommaHomEquiv (P : L.Object)
    (X : L.subgroupDiagramCategory (L.orbitProjection.obj P)) (Y : SingleObj P.as.val) :
    (SingleObj.star P.as.val ⟶ Y) ≃ (X ⟶ (L.subgroupComparisonFunctor P).obj Y) :=
  Equiv.ofBijective (fun g => L.linkingCommaBase P X ≫ (L.subgroupComparisonFunctor P).map g) (by
    constructor
    · intro a b hab
      exact L.linking_distinguished_post_injective (L.liftOrbitArrow X.hom)
        (congrArg (fun t => t.left) hab)
    · intro f
      have hf : L.orbitProjection.map f.left = X.hom := by
        have h := CostructuredArrow.w f
        change L.orbitProjection.map f.left ≫ 𝟙 _ = X.hom at h
        exact (Category.comp_id _).symm.trans h
      obtain ⟨g, hg, _⟩ := L.linking_orbit_fiber (L.liftOrbitArrow X.hom) f.left
        ((L.orbitProjection_liftOrbitArrow X.hom).trans hf.symm)
      exact ⟨g, CostructuredArrow.hom_ext _ _ hg⟩)

theorem linkingCommaHomEquiv_naturality (P : L.Object)
    (X : L.subgroupDiagramCategory (L.orbitProjection.obj P))
    (Y Y' : SingleObj P.as.val) (g : Y ⟶ Y') (h : SingleObj.star P.as.val ⟶ Y) :
    L.linkingCommaHomEquiv P X Y' (h ≫ g) =
      L.linkingCommaHomEquiv P X Y h ≫ (L.subgroupComparisonFunctor P).map g := by
  change L.linkingCommaBase P X ≫ (L.subgroupComparisonFunctor P).map (h ≫ g) = _
  rw [(L.subgroupComparisonFunctor P).map_comp]
  exact (Category.assoc _ _ _).symm

def linkingCommaReflection (P : L.Object) :
    L.subgroupDiagramCategory (L.orbitProjection.obj P) ⥤ SingleObj P.as.val :=
  Adjunction.leftAdjointOfEquiv (L.linkingCommaHomEquiv P)
    (L.linkingCommaHomEquiv_naturality P)

def linkingCommaAdjunction (P : L.Object) :
    L.linkingCommaReflection P ⊣ L.subgroupComparisonFunctor P :=
  Adjunction.adjunctionOfEquivLeft (L.linkingCommaHomEquiv P)
    (L.linkingCommaHomEquiv_naturality P)

/-- The actual comparison square is naturally homotopic through the
linking arrow, before any geometric realization theorem is used. -/
def linkingCommaComparisonNaturality {P Q : L.Object} (f : P ⟶ Q) :
    L.subgroupComparisonFunctor P ⋙ CostructuredArrow.map (L.orbitProjection.map f) ⟶
      (L.projection.map f).val.toFunctor ⋙ L.subgroupComparisonFunctor Q :=
  SingleObj.natTrans (CostructuredArrow.homMk f (by
    change L.orbitProjection.map f ≫ 𝟙 _ = 𝟙 _ ≫ L.orbitProjection.map f
    rw [Category.comp_id, Category.id_comp])) (by
    intro g
    apply CostructuredArrow.hom_ext
    exact L.commutation f g)

end Sharpness.FusionSystem.CentricLinkingSystem
