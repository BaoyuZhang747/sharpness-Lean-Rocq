import Sharpness.BLO.BLODiagramDistinguished
import Sharpness.Unconditional.CentralizerSaturation
import Sharpness.Unconditional.CentralizerCentric

/-! The actual centralizer linking category: its morphisms are original
linking morphisms fixing E, and its projection is transported through the
actual ambient subgroup equivalences. E <= P for every centralizer-centric
P, so BLO's product PE equals P in this elementary-abelian case. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace Sharpness.FusionSystem.CentricLinkingSystem
open CategoryTheory
variable {S : Type u} [Group S] [Finite S] {F : FusionSystem S}
    (L : F.CentricLinkingSystem) (p : ℕ) [Fact p.Prime]
    (hS : IsPGroup p S) (sat : F.Saturated p) (E : F.ElementaryCategory p)

def BLODiagramCentralizerPoint (P : (F.centralizerSystem p E).CentricSubgroup) : L.Object :=
  ⟨⟨ambientSubgroup (F.centralizerGroup p E) P.val,
    F.centralizer_centric_implies_ambient_centric p hS sat E
      (F.akoCentralizerInput p hS sat E) P.val P.property⟩⟩

def BLODiagramCentralizerPair (P : (F.centralizerSystem p E).CentricSubgroup) :
    L.BLODiagramObject E.obj where
  point := L.BLODiagramCentralizerPoint p hS sat E P
  label := F.inclusion (by
    intro z hz
    exact ⟨⟨z, F.elementary_le_centralizer p E hz⟩,
      F.elementaryInCentralizer_le_of_centric p hS sat E
        (F.akoCentralizerInput p hS sat E) P.val P.property hz, rfl⟩)
  central e := by
    apply Subgroup.mem_center_iff.mpr
    intro x
    apply Subtype.ext
    exact ((Subgroup.mem_centralizer_iff.mp
      (ambientSubgroup_le (F.centralizerGroup p E) P.val x.property)) e.val e.property).symm

def BLODiagramCentralizerRawProjection
    {P Q : (F.centralizerSystem p E).CentricSubgroup}
    (f : L.BLODiagramCentralizerPair p hS sat E P ⟶
      L.BLODiagramCentralizerPair p hS sat E Q) :
    (F.centralizerSystem p E).centricRawObject P ⟶
      (F.centralizerSystem p E).centricRawObject Q := by
  let T := F.centralizerGroup p E
  let g : P.val →* Q.val :=
    (subgroupAmbientEquiv T Q.val).symm.toMonoidHom.comp
      ((L.projection.map f.val).val.comp (subgroupAmbientEquiv T P.val).toMonoidHom)
  have hg : ambientHom T g = (L.projection.map f.val).val := by
    apply MonoidHom.ext
    intro x
    change subgroupAmbientEquiv T Q.val
      ((subgroupAmbientEquiv T Q.val).symm
        ((L.projection.map f.val).val
          (subgroupAmbientEquiv T P.val ((subgroupAmbientEquiv T P.val).symm x)))) = _
    rw [MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
    rfl
  refine ⟨g, F.centralizer_hom_of_fixes_elementary p hS sat E
    (F.akoCentralizerInput p hS sat E)
    (F.elementaryInCentralizer_le_of_centric p hS sat E
      (F.akoCentralizerInput p hS sat E) P.val P.property) g ?_ ?_⟩
  · rw [hg]
    exact (L.projection.map f.val).property
  · intro z
    apply Subtype.ext
    change ((subgroupAmbientEquiv T Q.val).symm
      ((L.projection.map f.val).val (subgroupAmbientEquiv T P.val
        ⟨z.val, _⟩))).val.val = z.val.val
    rw [subgroupAmbientEquiv_symm_val]
    have hfix := congrArg
      (fun a : E.obj ⟶ L.projection.obj (L.BLODiagramCentralizerPoint p hS sat E Q) =>
        (a.val ⟨z.val.val, z.property⟩).val) f.property
    exact hfix

theorem BLODiagramCentralizerRawProjection_ambient
    {P Q : (F.centralizerSystem p E).CentricSubgroup}
    (f : L.BLODiagramCentralizerPair p hS sat E P ⟶
      L.BLODiagramCentralizerPair p hS sat E Q) :
    ambientHom (F.centralizerGroup p E)
      (L.BLODiagramCentralizerRawProjection p hS sat E f).val =
      (L.projection.map f.val).val := by
  apply MonoidHom.ext
  intro x
  change subgroupAmbientEquiv (F.centralizerGroup p E) Q.val
    ((subgroupAmbientEquiv (F.centralizerGroup p E) Q.val).symm
      ((L.projection.map f.val).val
        (subgroupAmbientEquiv (F.centralizerGroup p E) P.val
          ((subgroupAmbientEquiv (F.centralizerGroup p E) P.val).symm x)))) = _
  rw [MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
  rfl

theorem BLODiagramCentralizerRawProjection_id
    (P : (F.centralizerSystem p E).CentricSubgroup) :
    L.BLODiagramCentralizerRawProjection p hS sat E
      (𝟙 (L.BLODiagramCentralizerPair p hS sat E P)) =
      𝟙 ((F.centralizerSystem p E).centricRawObject P) := by
  apply Subtype.ext
  apply MonoidHom.ext
  intro x
  change (subgroupAmbientEquiv (F.centralizerGroup p E) P.val).symm
    ((L.projection.map (𝟙 (L.BLODiagramCentralizerPoint p hS sat E P))).val
      (subgroupAmbientEquiv (F.centralizerGroup p E) P.val x)) = x
  rw [L.projection.map_id]
  exact (subgroupAmbientEquiv (F.centralizerGroup p E) P.val).symm_apply_apply x

theorem BLODiagramCentralizerRawProjection_comp
    {P Q R : (F.centralizerSystem p E).CentricSubgroup}
    (f : L.BLODiagramCentralizerPair p hS sat E P ⟶ L.BLODiagramCentralizerPair p hS sat E Q)
    (g : L.BLODiagramCentralizerPair p hS sat E Q ⟶ L.BLODiagramCentralizerPair p hS sat E R) :
    L.BLODiagramCentralizerRawProjection p hS sat E (f ≫ g) =
      L.BLODiagramCentralizerRawProjection p hS sat E f ≫
        L.BLODiagramCentralizerRawProjection p hS sat E g := by
  apply Subtype.ext
  apply MonoidHom.ext
  intro x
  change (subgroupAmbientEquiv (F.centralizerGroup p E) R.val).symm
    ((L.projection.map (f.val ≫ g.val)).val
      (subgroupAmbientEquiv (F.centralizerGroup p E) P.val x)) =
    (subgroupAmbientEquiv (F.centralizerGroup p E) R.val).symm
      ((L.projection.map g.val).val
        (subgroupAmbientEquiv (F.centralizerGroup p E) Q.val
          ((subgroupAmbientEquiv (F.centralizerGroup p E) Q.val).symm
            ((L.projection.map f.val).val
              (subgroupAmbientEquiv (F.centralizerGroup p E) P.val x)))))
  rw [L.projection.map_comp, MulEquiv.apply_symm_apply]
  rfl

def BLODiagramCentralizerData : (F.centralizerSystem p E).LinkingCategoryData where
  Hom P Q := L.BLODiagramCentralizerPair p hS sat E P ⟶ L.BLODiagramCentralizerPair p hS sat E Q
  id P := 𝟙 _
  comp f g := f ≫ g
  id_comp f := Category.id_comp f
  comp_id f := Category.comp_id f
  assoc f g h := Category.assoc f g h
  project f := L.BLODiagramCentralizerRawProjection p hS sat E f
  project_id P := L.BLODiagramCentralizerRawProjection_id p hS sat E P
  project_comp f g := L.BLODiagramCentralizerRawProjection_comp p hS sat E f g

def BLODiagramCentralizerDataInclusion :
    (L.BLODiagramCentralizerData p hS sat E).Object ⥤ L.BLODiagramObject E.obj where
  obj P := L.BLODiagramCentralizerPair p hS sat E P.as
  map f := f

instance BLODiagramCentralizerDataInclusion_faithful :
    (L.BLODiagramCentralizerDataInclusion p hS sat E).Faithful where
  map_injective h := h

instance BLODiagramCentralizerDataInclusion_full :
    (L.BLODiagramCentralizerDataInclusion p hS sat E).Full where
  map_surjective f := ⟨f, rfl⟩

end Sharpness.FusionSystem.CentricLinkingSystem
