import Sharpness.BLO.BLODiagram

/-! Actual BP maps into the enlarged linking categories. Every loop is
the original distinguished linking morphism; central labels make the
loop condition hold. These maps are compatible with all actual arrows
and with precomposition and the forgetful augmentation. -/
set_option autoImplicit false
noncomputable section
universe u

namespace Sharpness.FusionSystem.CentricLinkingSystem
open CategoryTheory
variable {S : Type u} [Group S] {F : FusionSystem S} (L : F.CentricLinkingSystem)

theorem BLODiagramDistinguished_fixes {E : F.Object} (A : L.BLODiagramObject E)
    (x : A.point.as.val) :
    A.label ≫ L.projection.map (L.distinguished A.point x).hom = A.label := by
  rw [L.project_distinguished]
  apply Subtype.ext
  apply MonoidHom.ext
  intro e
  apply Subtype.ext
  change (x.val⁻¹)⁻¹ * (A.label.val e).val * x.val⁻¹ = (A.label.val e).val
  rw [inv_inv]
  have hc := congrArg Subtype.val ((Subgroup.mem_center_iff.mp (A.central e)) x)
  change x.val * (A.label.val e).val = (A.label.val e).val * x.val at hc
  rw [hc, mul_assoc, mul_inv_cancel, mul_one]

def BLODiagramDistinguishedEnd {E : F.Object} (A : L.BLODiagramObject E) :
    A.point.as.val →* End A where
  toFun x := ⟨(L.distinguished A.point x).hom, L.BLODiagramDistinguished_fixes A x⟩
  map_one' := by
    apply Subtype.ext
    exact ((Aut.toEnd A.point).comp (L.distinguished A.point)).map_one
  map_mul' x y := by
    apply Subtype.ext
    exact ((Aut.toEnd A.point).comp (L.distinguished A.point)).map_mul x y

def BLODiagramDistinguishedFunctor {E : F.Object} (A : L.BLODiagramObject E) :
    SingleObj A.point.as.val ⥤ L.BLODiagramObject E :=
  SingleObj.functor (L.BLODiagramDistinguishedEnd A)

theorem BLODiagramDistinguishedFunctor_map {E : F.Object} (A : L.BLODiagramObject E)
    (x : A.point.as.val) :
    ((L.BLODiagramDistinguishedFunctor A).map
      (X := SingleObj.star A.point.as.val) (Y := SingleObj.star A.point.as.val) x).val =
      (L.distinguished A.point x).hom := rfl

theorem BLODiagramDistinguishedFunctor_forget {E : F.Object} (A : L.BLODiagramObject E) :
    L.BLODiagramDistinguishedFunctor A ⋙ L.BLODiagramForget E =
      L.distinguishedFunctor A.point := rfl

theorem BLODiagramDistinguishedFunctor_precomp {E E' : F.Object} (v : E ⟶ E')
    (A : L.BLODiagramObject E') :
    L.BLODiagramDistinguishedFunctor A ⋙ L.BLODiagramPrecomp v =
      L.BLODiagramDistinguishedFunctor ((L.BLODiagramPrecomp v).obj A) := rfl

def BLODiagramDistinguishedNaturality {E : F.Object} {A B : L.BLODiagramObject E}
    (f : A ⟶ B) : L.BLODiagramDistinguishedFunctor A ⟶
      (L.projection.map f.val).val.toFunctor ⋙ L.BLODiagramDistinguishedFunctor B :=
  SingleObj.natTrans f (fun x => Subtype.ext (L.commutation f.val x))

/-- The native map BP -> |C_L(E)|, induced by actual distinguished arrows. -/
def BLODiagramSubgroupClassifyingMap {E : F.Object} (A : L.BLODiagramObject E) :
    L.groupClassifyingSpace A.point ⟶ categoryRealization (L.BLODiagramObject E) :=
  SSet.toTop.map (nerveMapSingleObj A.point.as.val (L.BLODiagramDistinguishedFunctor A))

theorem BLODiagramSubgroupClassifyingMap_forget {E : F.Object} (A : L.BLODiagramObject E) :
    L.BLODiagramSubgroupClassifyingMap A ≫ categoryRealizationMap (L.BLODiagramForget E) =
      L.subgroupClassifyingMap A.point := by
  change SSet.toTop.map _ ≫ SSet.toTop.map _ = _
  rw [← SSet.toTop.map_comp, ← nerveMapSingleObj_comp,
    L.BLODiagramDistinguishedFunctor_forget]
  rfl

theorem BLODiagramSubgroupClassifyingMap_precomp {E E' : F.Object} (v : E ⟶ E')
    (A : L.BLODiagramObject E') :
    L.BLODiagramSubgroupClassifyingMap A ≫ categoryRealizationMap (L.BLODiagramPrecomp v) =
      L.BLODiagramSubgroupClassifyingMap ((L.BLODiagramPrecomp v).obj A) := by
  change SSet.toTop.map _ ≫ SSet.toTop.map _ = _
  rw [← SSet.toTop.map_comp, ← nerveMapSingleObj_comp,
    L.BLODiagramDistinguishedFunctor_precomp]
  rfl

end Sharpness.FusionSystem.CentricLinkingSystem
