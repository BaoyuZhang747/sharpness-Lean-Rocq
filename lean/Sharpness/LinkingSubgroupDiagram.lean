import Sharpness.CentricLinkingSystem
import Mathlib.CategoryTheory.Comma.StructuredArrow.Functor

/-! The actual subgroup diagram used in BLO Proposition 2.2:
Btilde(P) is the realization of (pi_tilde down P). Its functoriality
comes from actual postcomposition in the comma categories. The map
BP -> Btilde(P) is constructed from delta_P, and its composite with
the forgetful map to |L| is exactly the distinguished iota_P. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness.FusionSystem.CentricLinkingSystem
open CategoryTheory
variable {S : Type u} [Group S] {F : FusionSystem S} (L : F.CentricLinkingSystem)

abbrev orbitProjection : L.Object ⥤ F.CentricOrbit := L.toLinkingCategoryData.orbitProjection

def subgroupCategoryDiagram : F.CentricOrbit ⥤ Cat.{u,u} :=
  CostructuredArrow.functor L.orbitProjection

def subgroupDiagram : F.CentricOrbit ⥤ TopCat.{u} :=
  L.subgroupCategoryDiagram ⋙ CategoryTheory.nerveFunctor ⋙ SSet.toTop

abbrev subgroupDiagramCategory (P : F.CentricOrbit) := CostructuredArrow L.orbitProjection P

def subgroupDiagramForget (P : F.CentricOrbit) :
    L.subgroupDiagram.obj P ⟶ L.classifyingSpace :=
  SSet.toTop.map (CategoryTheory.nerveMap (CostructuredArrow.proj L.orbitProjection P))

theorem orbitProjection_distinguished (P : L.Object) (g : P.as.val) :
    L.orbitProjection.map (L.distinguished P g).hom = 𝟙 (L.orbitProjection.obj P) := by
  apply ObjectProperty.hom_ext
  change F.toOrbit.map (L.projection.map (L.distinguished P g).hom) = _
  exact (congrArg (fun f => F.toOrbit.map f) (L.project_distinguished P g)).trans
    (F.inner_orbit_eq_id (L.toLinkingCategoryData.rawObject P) g⁻¹)

def subgroupComparisonFunctor (P : L.Object) :
    SingleObj P.as.val ⥤ L.subgroupDiagramCategory (L.orbitProjection.obj P) :=
  (L.distinguishedFunctor P).toCostructuredArrow L.orbitProjection
    (L.orbitProjection.obj P) (fun _ => 𝟙 _) (by
      intro X Y g
      change L.orbitProjection.map (L.distinguished P g).hom ≫ 𝟙 _ = 𝟙 _
      rw [Category.comp_id, L.orbitProjection_distinguished])

/-- The actual epsilon_P, prior to importing its homotopy-equivalence property. -/
def subgroupComparison (P : L.Object) :
    L.groupClassifyingSpace P ⟶ L.subgroupDiagram.obj (L.orbitProjection.obj P) :=
  SSet.toTop.map (nerveMapSingleObj P.as.val (L.subgroupComparisonFunctor P))

theorem subgroupComparison_comp_forget (P : L.Object) :
    L.subgroupComparison P ≫ L.subgroupDiagramForget (L.orbitProjection.obj P) =
      L.subgroupClassifyingMap P := by
  have h : nerveMapSingleObj P.as.val (L.subgroupComparisonFunctor P) ≫
      CategoryTheory.nerveMap (CostructuredArrow.proj L.orbitProjection (L.orbitProjection.obj P)) =
        nerveMapSingleObj P.as.val (L.distinguishedFunctor P) :=
    (nerveMapSingleObj_comp P.as.val (L.subgroupComparisonFunctor P)
      (CostructuredArrow.proj L.orbitProjection (L.orbitProjection.obj P))).symm
  exact (SSet.toTop.map_comp _ _).symm.trans (congrArg (fun f => SSet.toTop.map f) h)

/-- A concrete category model for the homotopy colimit of the subgroup diagram. -/
abbrev subgroupGrothendieck := Grothendieck L.subgroupCategoryDiagram

def subgroupGrothendieckSpace : TopCat.{u} :=
  SSet.toTop.obj (CategoryTheory.nerve L.subgroupGrothendieck)

def subgroupGrothendieckProjection : L.subgroupGrothendieck ⥤ L.Object :=
  CostructuredArrow.grothendieckProj L.orbitProjection

def subgroupHomotopyColimitMap : L.subgroupGrothendieckSpace ⟶ L.classifyingSpace :=
  SSet.toTop.map (CategoryTheory.nerveMap L.subgroupGrothendieckProjection)

end Sharpness.FusionSystem.CentricLinkingSystem
