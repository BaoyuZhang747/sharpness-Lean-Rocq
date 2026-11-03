import Sharpness.BLO.BLOCohomologyCentralizerPoint
import Sharpness.BLO.BLODiagramCentralizerAxioms
import Sharpness.V29.MainSubgroup

/-! The canonical comparison is identified with the actual centralizer
linking inclusion followed by the Task 1 stable-elements isomorphism.
Every component is the native subgroup restriction, with its literal
ambient-group chart.  No varying-E centralizer naturality is assumed. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace Sharpness.FusionSystem.CentricLinkingSystem
open CategoryTheory CategoryTheory.Limits Opposite

variable {S : Type u} [Group S] [Finite S] {F : FusionSystem S}
    (L : F.CentricLinkingSystem) (p : ℕ) [Fact p.Prime]
    (hS : IsPGroup p S) (sat : F.Saturated p)

def BLOCohomologyCentralizerStableIso (n : ℕ) (E : F.ElementaryCategory p) :
    BLOCohomologyCategory (PrimeField.{u} p)
      (ModuleCat.of (PrimeField.{u} p) (PrimeField.{u} p)) n
      (L.BLODiagramCentralizerLinking p hS sat E).Object ≅
      limit ((F.centralizerSystem p E).cohomologyCoefficient
        (R := PrimeField.{u} p) (A := PrimeField.{u} p) n) :=
  V29.nativeOrdinaryRestrictionIso (L.BLODiagramCentralizerLinking p hS sat E) p
    (hS.to_subgroup (F.centralizerGroup p E))
    (F.centralizerSystem_saturated p hS sat E) (PrimeField.{u} p)
    (ModuleCat.of (PrimeField.{u} p) (PrimeField.{u} p)) n

def BLOCohomologyCentralizerRestriction (n : ℕ) (E : F.ElementaryCategory p) :
    (L.BLOCohomologyDiagram p n).obj E ⟶
      limit ((F.centralizerSystem p E).cohomologyCoefficient
        (R := PrimeField.{u} p) (A := PrimeField.{u} p) n) :=
  BLOCohomologyPull (PrimeField.{u} p)
    (ModuleCat.of (PrimeField.{u} p) (PrimeField.{u} p)) n
    (L.BLODiagramCentralizerInclusion p hS sat E) ≫
    (L.BLOCohomologyCentralizerStableIso p hS sat n E).hom

@[reassoc] theorem BLOCohomologyCentralizerRestriction_component (n : ℕ)
    (E : F.ElementaryCategory p) (P : (F.centralizerSystem p E).CentricOrbit) :
    L.BLOCohomologyCentralizerRestriction p hS sat n E ≫ limit.π _ (op P) =
      L.BLOCohomologyRestriction (PrimeField.{u} p)
        (ModuleCat.of (PrimeField.{u} p) (PrimeField.{u} p)) n
        (L.BLODiagramCentralizerPair p hS sat E ⟨P.obj.as.subgroup, P.property⟩) ≫
        OrdinaryCohomology.pull (R := PrimeField.{u} p) (A := PrimeField.{u} p)
          (subgroupAmbientEquiv (F.centralizerGroup p E) P.obj.as.subgroup).toMonoidHom n := by
  unfold BLOCohomologyCentralizerRestriction BLOCohomologyCentralizerStableIso
  rw [Category.assoc, V29.nativeOrdinaryRestrictionIso_component]
  change BLOCohomologyPull (PrimeField.{u} p)
      (ModuleCat.of (PrimeField.{u} p) (PrimeField.{u} p)) n
      (L.BLODiagramCentralizerInclusion p hS sat E) ≫
      BLOCohomologyGroupRestriction (PrimeField.{u} p)
        (ModuleCat.of (PrimeField.{u} p) (PrimeField.{u} p)) n P.obj.as.subgroup
        ((L.BLODiagramCentralizerLinking p hS sat E).distinguishedFunctor
          ((L.BLODiagramCentralizerLinking p hS sat E).linkingObjectOfOrbit P)) = _
  rw [BLOCohomologyGroupRestriction_precomp,
    L.BLODiagramCentralizerDistinguishedCompatibility,
    BLOCohomologyGroupRestriction_group]
  rfl

theorem BLOCohomologyToRightKan_centralizerRestriction (n : ℕ)
    (E : F.ElementaryCategory p) :
    (L.BLOCohomologyToRightKan p n).app E ≫
        (V28.rightKanCohomologyLimitIso p F hS sat n E).hom =
      L.BLOCohomologyCentralizerRestriction p hS sat n E := by
  apply limit.hom_ext
  intro P
  rw [Category.assoc, L.BLOCohomologyToRightKan_centralizerPair,
    L.BLOCohomologyCentralizerRestriction_component]

end Sharpness.FusionSystem.CentricLinkingSystem
