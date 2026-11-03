import Sharpness.BLO.BLODiagramCentralizerBase

/-! All defining axioms of the centralizer linking system constructed
from the supplied ambient linking system. No linking existence or
compatibility hypothesis is added. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace Sharpness.FusionSystem.CentricLinkingSystem
open CategoryTheory
variable {S : Type u} [Group S] [Finite S] {F : FusionSystem S}
    (L : F.CentricLinkingSystem) (p : ℕ) [Fact p.Prime]
    (hS : IsPGroup p S) (sat : F.Saturated p) (E : F.ElementaryCategory p)

def BLODiagramCentralizerDistinguished
    (P : (L.BLODiagramCentralizerData p hS sat E).Object) : P.as.val →* Aut P :=
  (Aut.unitsEndEquivAut P).toMonoidHom.comp
    (((L.BLODiagramDistinguishedEnd (L.BLODiagramCentralizerPair p hS sat E P.as)).comp
      (subgroupAmbientEquiv (F.centralizerGroup p E) P.as.val).toMonoidHom).toHomUnits)

theorem BLODiagramCentralizerDistinguished_hom
    (P : (L.BLODiagramCentralizerData p hS sat E).Object) (x : P.as.val) :
    (L.BLODiagramCentralizerDistinguished p hS sat E P x).hom.val =
      (L.distinguished (L.BLODiagramCentralizerPoint p hS sat E P.as)
        (subgroupAmbientEquiv (F.centralizerGroup p E) P.as.val x)).hom := rfl

theorem BLODiagramCentralizerDistinguished_injective
    (P : (L.BLODiagramCentralizerData p hS sat E).Object) :
    Function.Injective (L.BLODiagramCentralizerDistinguished p hS sat E P) := by
  intro x y h
  apply (subgroupAmbientEquiv (F.centralizerGroup p E) P.as.val).injective
  apply L.distinguished_injective (L.BLODiagramCentralizerPoint p hS sat E P.as)
  apply Iso.ext
  exact congrArg (fun a : Aut P => a.hom.val) h

theorem BLODiagramCentralizerRawProjection_eq_iff
    {P Q : (F.centralizerSystem p E).CentricSubgroup}
    (f g : L.BLODiagramCentralizerPair p hS sat E P ⟶ L.BLODiagramCentralizerPair p hS sat E Q) :
    L.BLODiagramCentralizerRawProjection p hS sat E f =
        L.BLODiagramCentralizerRawProjection p hS sat E g ↔
      L.projection.map f.val = L.projection.map g.val := by
  constructor
  · intro h
    apply Subtype.ext
    have h' := congrArg (fun a => ambientHom (F.centralizerGroup p E) a.val) h
    simpa only [L.BLODiagramCentralizerRawProjection_ambient] using h'
  · intro h
    apply Subtype.ext
    apply MonoidHom.ext
    intro x
    change (subgroupAmbientEquiv (F.centralizerGroup p E) Q.val).symm
      ((L.projection.map f.val).val (subgroupAmbientEquiv (F.centralizerGroup p E) P.val x)) =
      (subgroupAmbientEquiv (F.centralizerGroup p E) Q.val).symm
        ((L.projection.map g.val).val (subgroupAmbientEquiv (F.centralizerGroup p E) P.val x))
    rw [h]

theorem BLODiagramCentralizerProjection_surjective
    (P Q : (L.BLODiagramCentralizerData p hS sat E).Object) :
    Function.Surjective
      ((L.BLODiagramCentralizerData p hS sat E).projection.map : (P ⟶ Q) → _) := by
  intro g
  let T := F.centralizerGroup p E
  let gF : L.projection.obj (L.BLODiagramCentralizerPoint p hS sat E P.as) ⟶
      L.projection.obj (L.BLODiagramCentralizerPoint p hS sat E Q.as) :=
    ⟨ambientHom T g.val, ((F.akoCentralizerInput p hS sat E).hom_iff g.val).mp g.property |>.1⟩
  obtain ⟨f, hf⟩ := L.projection_surjective _ _ gF
  have hf' : (L.BLODiagramCentralizerPair p hS sat E P.as).label ≫ L.projection.map f =
      (L.BLODiagramCentralizerPair p hS sat E Q.as).label := by
    rw [hf]
    apply Subtype.ext
    apply MonoidHom.ext
    intro e
    apply Subtype.ext
    let z : F.elementaryInCentralizer p E := ⟨⟨e.val, F.elementary_le_centralizer p E e.property⟩, e.property⟩
    have hEP := F.elementaryInCentralizer_le_of_centric p hS sat E
      (F.akoCentralizerInput p hS sat E) P.as.val P.as.property
    obtain ⟨_, extension, _, hP, hE⟩ := ((F.akoCentralizerInput p hS sat E).hom_iff g.val).mp g.property
    have hfix := (hP ⟨z.val, hEP z.property⟩).symm.trans (hE z)
    change (ambientHom T g.val (subgroupAmbientEquiv T P.as.val ⟨z.val, hEP z.property⟩)).val = e.val
    exact (congrArg (fun a : ambientSubgroup T Q.as.val => a.val)
      (ambientHom_apply T g.val ⟨z.val, hEP z.property⟩)).trans
        (congrArg (fun t : T => t.val) hfix)
  refine ⟨⟨f, hf'⟩, ?_⟩
  apply Subtype.ext
  apply MonoidHom.ext
  intro x
  apply (subgroupAmbientEquiv T Q.as.val).injective
  change subgroupAmbientEquiv T Q.as.val
    ((subgroupAmbientEquiv T Q.as.val).symm
      ((L.projection.map f).val (subgroupAmbientEquiv T P.as.val x))) =
      subgroupAmbientEquiv T Q.as.val (g.val x)
  rw [MulEquiv.apply_symm_apply, hf]
  exact ambientHom_apply T g.val x

theorem BLODiagramCentralizerCentralFiber
    {P Q : (L.BLODiagramCentralizerData p hS sat E).Object} (f g : P ⟶ Q) :
    (L.BLODiagramCentralizerData p hS sat E).projection.map f =
        (L.BLODiagramCentralizerData p hS sat E).projection.map g ↔
      ∃! z : Subgroup.center P.as.val,
        (L.BLODiagramCentralizerDistinguished p hS sat E P z.val).hom ≫ f = g := by
  change L.BLODiagramCentralizerRawProjection p hS sat E f =
      L.BLODiagramCentralizerRawProjection p hS sat E g ↔ _
  rw [L.BLODiagramCentralizerRawProjection_eq_iff, L.central_fiber]
  symm
  apply (Subgroup.centerCongr
    (subgroupAmbientEquiv (F.centralizerGroup p E) P.as.val)).toEquiv.existsUnique_congr
  intro z
  change ((L.BLODiagramCentralizerDistinguished p hS sat E P z.val).hom ≫ f = g) ↔
    ((L.distinguished (L.BLODiagramCentralizerPoint p hS sat E P.as)
      (subgroupAmbientEquiv (F.centralizerGroup p E) P.as.val z.val)).hom ≫ f.val = g.val)
  exact Subtype.ext_iff

theorem BLODiagramCentralizerProjectDistinguished
    (P : (L.BLODiagramCentralizerData p hS sat E).Object) (x : P.as.val) :
    (L.BLODiagramCentralizerData p hS sat E).projection.map
        (L.BLODiagramCentralizerDistinguished p hS sat E P x).hom =
      (F.centralizerSystem p E).inner
        ((L.BLODiagramCentralizerData p hS sat E).rawObject P) x⁻¹ := by
  apply Subtype.ext
  apply MonoidHom.ext
  intro y
  apply (subgroupAmbientEquiv (F.centralizerGroup p E) P.as.val).injective
  change subgroupAmbientEquiv (F.centralizerGroup p E) P.as.val
    ((subgroupAmbientEquiv (F.centralizerGroup p E) P.as.val).symm
      ((L.projection.map
        (L.distinguished (L.BLODiagramCentralizerPoint p hS sat E P.as)
          (subgroupAmbientEquiv (F.centralizerGroup p E) P.as.val x)).hom).val
        (subgroupAmbientEquiv (F.centralizerGroup p E) P.as.val y))) = _
  rw [MulEquiv.apply_symm_apply, L.project_distinguished]
  rfl

theorem BLODiagramCentralizerCommutation
    {P Q : (L.BLODiagramCentralizerData p hS sat E).Object} (f : P ⟶ Q) (x : P.as.val) :
    (L.BLODiagramCentralizerDistinguished p hS sat E P x).hom ≫ f =
      f ≫ (L.BLODiagramCentralizerDistinguished p hS sat E Q
        (((L.BLODiagramCentralizerData p hS sat E).projection.map f).val x)).hom := by
  apply Subtype.ext
  change (L.distinguished (L.BLODiagramCentralizerPoint p hS sat E P.as)
      (subgroupAmbientEquiv (F.centralizerGroup p E) P.as.val x)).hom ≫ f.val =
    f.val ≫ (L.distinguished (L.BLODiagramCentralizerPoint p hS sat E Q.as)
      (subgroupAmbientEquiv (F.centralizerGroup p E) Q.as.val
        ((subgroupAmbientEquiv (F.centralizerGroup p E) Q.as.val).symm
          ((L.projection.map f.val).val
            (subgroupAmbientEquiv (F.centralizerGroup p E) P.as.val x))))).hom
  rw [MulEquiv.apply_symm_apply]
  exact L.commutation f.val _

/-- The supplied ambient linking system constructs the actual centralizer
linking system; all defining axioms above are proved. -/
def BLODiagramCentralizerLinking : (F.centralizerSystem p E).CentricLinkingSystem where
  toLinkingCategoryData := L.BLODiagramCentralizerData p hS sat E
  distinguished := L.BLODiagramCentralizerDistinguished p hS sat E
  distinguished_injective := L.BLODiagramCentralizerDistinguished_injective p hS sat E
  projection_surjective := L.BLODiagramCentralizerProjection_surjective p hS sat E
  central_fiber := L.BLODiagramCentralizerCentralFiber p hS sat E
  project_distinguished := L.BLODiagramCentralizerProjectDistinguished p hS sat E
  commutation := L.BLODiagramCentralizerCommutation p hS sat E

def BLODiagramCentralizerInclusion :
    (L.BLODiagramCentralizerLinking p hS sat E).Object ⥤ L.BLODiagramObject E.obj :=
  L.BLODiagramCentralizerDataInclusion p hS sat E

theorem BLODiagramCentralizerDistinguishedCompatibility
    (P : (L.BLODiagramCentralizerLinking p hS sat E).Object) :
    (L.BLODiagramCentralizerLinking p hS sat E).distinguishedFunctor P ⋙
        L.BLODiagramCentralizerInclusion p hS sat E =
      (subgroupAmbientEquiv (F.centralizerGroup p E) P.as.val).toMonoidHom.toFunctor ⋙
        L.BLODiagramDistinguishedFunctor
          ((L.BLODiagramCentralizerInclusion p hS sat E).obj P) := rfl

end Sharpness.FusionSystem.CentricLinkingSystem
