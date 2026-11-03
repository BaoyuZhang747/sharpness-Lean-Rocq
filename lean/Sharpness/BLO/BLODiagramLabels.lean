import Sharpness.BLO.BLODiagram
import Sharpness.SubgroupAmbientGeometry

/-! Exact identification of the central-image labels with raw fusion maps
into the actual subgroup Z(P) of S. -/
set_option autoImplicit false
noncomputable section
universe u

namespace Sharpness.FusionSystem.CentricLinkingSystem
open CategoryTheory
variable {S : Type u} [Group S] {F : FusionSystem S} (L : F.CentricLinkingSystem)

def BLODiagramCenterObject (P : L.Object) : F.Object :=
  ⟨ambientSubgroup P.as.val (Subgroup.center P.as.val)⟩

def BLODiagramCenterInclusion (P : L.Object) :
    L.BLODiagramCenterObject P ⟶ L.projection.obj P :=
  F.inclusion (ambientSubgroup_le P.as.val (Subgroup.center P.as.val))

def BLODiagramCentralLabelEquiv (E : F.Object) (P : L.Object) :
    {a : E ⟶ L.projection.obj P // ∀ e, a.val e ∈ Subgroup.center P.as.val} ≃
      (E ⟶ L.BLODiagramCenterObject P) where
  toFun a := by
    let b : E.subgroup →* (L.BLODiagramCenterObject P).subgroup :=
      { toFun := fun e => ⟨(a.val.val e).val, ⟨a.val.val e, a.property e, rfl⟩⟩
        map_one' := by
          apply Subtype.ext
          exact congrArg (fun z : P.as.val => z.val) a.val.val.map_one
        map_mul' := by
          intro x y
          apply Subtype.ext
          exact congrArg (fun z : P.as.val => z.val) (a.val.val.map_mul x y) }
    refine ⟨b, F.codomain_restrict_mem a.val.val a.val.property
      (ambientSubgroup_le P.as.val (Subgroup.center P.as.val)) b ?_⟩
    ext e
    rfl
  invFun b :=
    ⟨b ≫ L.BLODiagramCenterInclusion P, by
      intro e
      obtain ⟨z, hz, h⟩ := (b.val e).property
      have he : z = (b ≫ L.BLODiagramCenterInclusion P).val e := Subtype.ext h
      exact he ▸ hz⟩
  left_inv a := by
    apply Subtype.ext
    apply Subtype.ext
    ext e
    rfl
  right_inv b := by
    apply Subtype.ext
    ext e
    rfl

theorem BLODiagramCentralLabelEquiv_comp_inclusion (E : F.Object) (P : L.Object)
    (a : {a : E ⟶ L.projection.obj P // ∀ e, a.val e ∈ Subgroup.center P.as.val}) :
    L.BLODiagramCentralLabelEquiv E P a ≫ L.BLODiagramCenterInclusion P = a.val := by
  apply Subtype.ext
  ext e
  rfl

/-- The actual object bijection with the pairs printed in BLO Theorem 2.6. -/
def BLODiagramObjectEquiv (E : F.Object) :
    L.BLODiagramObject E ≃ Σ P : L.Object, E ⟶ L.BLODiagramCenterObject P where
  toFun A := ⟨A.point, L.BLODiagramCentralLabelEquiv E A.point ⟨A.label, A.central⟩⟩
  invFun A :=
    { point := A.1
      label := ((L.BLODiagramCentralLabelEquiv E A.1).symm A.2).val
      central := ((L.BLODiagramCentralLabelEquiv E A.1).symm A.2).property }
  left_inv A := by
    cases A with
    | mk P a ha =>
      change BLODiagramObject.mk P
        (((L.BLODiagramCentralLabelEquiv E P).symm
          (L.BLODiagramCentralLabelEquiv E P ⟨a, ha⟩)).val) _ = _
      rw [Equiv.symm_apply_apply]
  right_inv A := by
    cases A with
    | mk P a =>
      change (⟨P, L.BLODiagramCentralLabelEquiv E P
        ((L.BLODiagramCentralLabelEquiv E P).symm a)⟩ :
          Σ P : L.Object, E ⟶ L.BLODiagramCenterObject P) = ⟨P, a⟩
      rw [Equiv.apply_symm_apply]

end Sharpness.FusionSystem.CentricLinkingSystem
