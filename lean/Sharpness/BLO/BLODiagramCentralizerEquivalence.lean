import Sharpness.BLO.BLODiagramCentralizerAxioms
import Sharpness.BLO.BLODiagramLifts
import Sharpness.NormalizerAction
import Mathlib.CategoryTheory.Equivalence

/-! The actual centralizer linking category is equivalent to the enlarged
category at a fully centralized elementary abelian subgroup. The inclusion
is the actual ambient linking-arrow inclusion. Essential surjectivity is
proved by the saturation extension axiom and genuine linking isomorphism
lifts; no objectwise equivalence is assumed. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace Sharpness.FusionSystem.CentricLinkingSystem
open CategoryTheory
variable {S : Type u} [Group S] {F : FusionSystem S} (L : F.CentricLinkingSystem)

def BLODiagramIsoOfUnderlying {E : F.Object} {A B : L.BLODiagramObject E}
    (e : A.point ≅ B.point) (h : A.label ≫ L.projection.map e.hom = B.label) : A ≅ B where
  hom := ⟨e.hom, h⟩
  inv := ⟨e.inv, by
    rw [← h, Category.assoc, ← L.projection.map_comp, e.hom_inv_id,
      L.projection.map_id, Category.comp_id]⟩
  hom_inv_id := Subtype.ext e.hom_inv_id
  inv_hom_id := Subtype.ext e.inv_hom_id

variable [Finite S] (p : ℕ) [Fact p.Prime]
    (hS : IsPGroup p S) (sat : F.Saturated p) (E : F.ElementaryCategory p)

theorem BLODiagramCentralizerRepresentative (A : L.BLODiagramObject E.obj) :
    ∃ P : (F.centralizerSystem p E).CentricSubgroup,
      Nonempty (A ≅ L.BLODiagramCentralizerPair p hS sat E P) := by
  let T := F.centralizerGroup p E
  let aRaw : E.obj.subgroup →* S := A.point.as.val.subtype.comp A.label.val
  let D := aRaw.range
  have haRaw : Function.Injective aRaw :=
    Subtype.val_injective.comp (F.injective A.label.val A.label.property)
  let a : E.obj.subgroup ≃* D := MonoidHom.ofInjective haRaw
  have hDP : D ≤ A.point.as.val := by
    rintro d ⟨e, rfl⟩
    exact (A.label.val e).property
  have ha : F.IsHom a.toMonoidHom := by
    apply F.codomain_restrict_mem A.label.val A.label.property hDP a.toMonoidHom
    ext e
    rfl
  have hPC : A.point.as.val ≤ Subgroup.centralizer (D : Set S) := by
    intro x hx
    apply Subgroup.mem_centralizer_iff.mpr
    rintro d ⟨e, rfl⟩
    exact (congrArg (fun z : A.point.as.val => z.val)
      ((Subgroup.mem_center_iff.mp (A.central e)) ⟨x, hx⟩)).symm
  obtain ⟨bC, hbC, hbCa⟩ := F.centralizer_extension_of_fullyCentralized p sat
    a.symm (F.inverse_mem a ha) E.property.2.2.2
  let b : A.point.as.val →* T := bC.comp (subgroupInclusion _ _ hPC)
  have hb : F.IsHom b := F.comp_mem _ _ (F.inclusion_mem hPC) hbC
  let P : Subgroup T := b.range
  let eP : A.point.as.val ≃* P := MonoidHom.ofInjective (F.injective b hb)
  let eA : A.point.as.val ≃* ambientSubgroup T P := eP.trans (subgroupAmbientEquiv T P)
  have heA : F.IsHom eA.toMonoidHom := by
    apply F.codomain_restrict_mem b hb (ambientSubgroup_le T P) eA.toMonoidHom
    ext x
    rfl
  have hAP : F.IsCentric (ambientSubgroup T P) :=
    F.isoSystem.centricIn_of_iso eA heA A.point.as.property
  have hP : (F.centralizerSystem p E).IsCentric P :=
    ((F.yalcinCentralizerCentricInput p hS sat E
      (F.akoCentralizerInput p hS sat E)).lemma_8_11 P).1.mpr hAP
  let Q : (F.centralizerSystem p E).CentricSubgroup := ⟨P, hP⟩
  let rawIso : L.projection.obj A.point ≅
      L.projection.obj (L.BLODiagramCentralizerPoint p hS sat E Q) :=
    F.isoOfMulEquiv eA heA
  have hlabel : A.label ≫ rawIso.hom =
      (L.BLODiagramCentralizerPair p hS sat E Q).label := by
    apply Subtype.ext
    apply MonoidHom.ext
    intro e
    apply Subtype.ext
    have hvalue := hbCa (a e) (hPC (A.label.val e).property)
    rw [MulEquiv.symm_apply_apply] at hvalue
    exact hvalue
  let lifted := L.BLODiagramLiftIso rawIso
  refine ⟨Q, ⟨L.BLODiagramIsoOfUnderlying lifted ?_⟩⟩
  rw [L.BLODiagramLiftIso_projection]
  exact hlabel

instance BLODiagramCentralizerInclusion_faithful :
    (L.BLODiagramCentralizerInclusion p hS sat E).Faithful :=
  L.BLODiagramCentralizerDataInclusion_faithful p hS sat E

instance BLODiagramCentralizerInclusion_full :
    (L.BLODiagramCentralizerInclusion p hS sat E).Full :=
  L.BLODiagramCentralizerDataInclusion_full p hS sat E

instance BLODiagramCentralizerInclusion_essSurj :
    (L.BLODiagramCentralizerInclusion p hS sat E).EssSurj where
  mem_essImage A := by
    obtain ⟨P, ⟨e⟩⟩ := L.BLODiagramCentralizerRepresentative p hS sat E A
    exact ⟨⟨P⟩, ⟨e.symm⟩⟩

instance BLODiagramCentralizerInclusion_isEquivalence :
    (L.BLODiagramCentralizerInclusion p hS sat E).IsEquivalence where

/-- A category equivalence with the genuine centralizer linking system
constructed from L, not an assumed compatible linking-system choice. -/
def BLODiagramCentralizerEquivalence :
    (L.BLODiagramCentralizerLinking p hS sat E).Object ≌ L.BLODiagramObject E.obj :=
  (L.BLODiagramCentralizerInclusion p hS sat E).asEquivalence

theorem BLODiagramCentralizerEquivalence_functor :
    (L.BLODiagramCentralizerEquivalence p hS sat E).functor =
      L.BLODiagramCentralizerInclusion p hS sat E := rfl

end Sharpness.FusionSystem.CentricLinkingSystem
