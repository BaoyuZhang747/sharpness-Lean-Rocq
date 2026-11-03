import Sharpness.BLO.BLOCohomologyCentralizer
import Sharpness.BLO.BLODiagramCentralizerEquivalence

/-! The full natural identification of the actual enlarged-linking native
cohomology diagram with the existing E3 right Kan extension.  The forward
map is the canonical map already fixed by all distinguished BP restrictions.
Centralizer choices prove that map invertible; they do not define its arrows. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace Sharpness.FusionSystem.CentricLinkingSystem
open CategoryTheory CategoryTheory.Limits Opposite

variable {S : Type u} [Group S] [Finite S] {F : FusionSystem S}
    (L : F.CentricLinkingSystem) (p : ℕ) [Fact p.Prime]
    (hS : IsPGroup p S) (sat : F.Saturated p)

def BLOCohomologyCentralizerInclusionIso (n : ℕ) (E : F.ElementaryCategory p) :
    (L.BLOCohomologyDiagram p n).obj E ≅
      BLOCohomologyCategory (PrimeField.{u} p)
        (ModuleCat.of (PrimeField.{u} p) (PrimeField.{u} p)) n
        (L.BLODiagramCentralizerLinking p hS sat E).Object :=
  BLOCohomologyEquivalenceIso (PrimeField.{u} p)
    (ModuleCat.of (PrimeField.{u} p) (PrimeField.{u} p)) n
    (L.BLODiagramCentralizerEquivalence p hS sat E)

theorem BLOCohomologyCentralizerInclusionIso_hom (n : ℕ) (E : F.ElementaryCategory p) :
    (L.BLOCohomologyCentralizerInclusionIso p hS sat n E).hom =
      BLOCohomologyPull (PrimeField.{u} p)
        (ModuleCat.of (PrimeField.{u} p) (PrimeField.{u} p)) n
        (L.BLODiagramCentralizerInclusion p hS sat E) := rfl

def BLOCohomologyCentralizerLimitIso (n : ℕ) (E : F.ElementaryCategory p) :
    (L.BLOCohomologyDiagram p n).obj E ≅
      limit ((F.centralizerSystem p E).cohomologyCoefficient
        (R := PrimeField.{u} p) (A := PrimeField.{u} p) n) :=
  L.BLOCohomologyCentralizerInclusionIso p hS sat n E ≪≫
    L.BLOCohomologyCentralizerStableIso p hS sat n E

theorem BLOCohomologyCentralizerLimitIso_hom (n : ℕ) (E : F.ElementaryCategory p) :
    (L.BLOCohomologyCentralizerLimitIso p hS sat n E).hom =
      L.BLOCohomologyCentralizerRestriction p hS sat n E := rfl

def BLOCohomologyRightKanComponentIso (n : ℕ) (E : F.ElementaryCategory p) :
    (L.BLOCohomologyDiagram p n).obj E ≅ (V28.rightKanCohomology p F n).obj E :=
  L.BLOCohomologyCentralizerLimitIso p hS sat n E ≪≫
    (V28.rightKanCohomologyLimitIso p F hS sat n E).symm

theorem BLOCohomologyRightKanComponentIso_hom (n : ℕ) (E : F.ElementaryCategory p) :
    (L.BLOCohomologyRightKanComponentIso p hS sat n E).hom =
      (L.BLOCohomologyToRightKan p n).app E := by
  have h := congrArg
    (fun t => t ≫ (V28.rightKanCohomologyLimitIso p F hS sat n E).inv)
    (L.BLOCohomologyToRightKan_centralizerRestriction p hS sat n E)
  simpa only [BLOCohomologyRightKanComponentIso, Iso.trans_hom, Iso.symm_hom,
    BLOCohomologyCentralizerLimitIso_hom, Category.assoc, Iso.hom_inv_id,
    Category.comp_id] using h.symm

def BLOCohomologyRightKanIso (n : ℕ) :
    L.BLOCohomologyDiagram p n ≅ V28.rightKanCohomology p F n :=
  NatIso.ofComponents (L.BLOCohomologyRightKanComponentIso p hS sat n) (by
    intro E E' v
    rw [L.BLOCohomologyRightKanComponentIso_hom,
      L.BLOCohomologyRightKanComponentIso_hom]
    exact (L.BLOCohomologyToRightKan p n).naturality v)

theorem BLOCohomologyRightKanIso_hom (n : ℕ) :
    (L.BLOCohomologyRightKanIso p hS sat n).hom = L.BLOCohomologyToRightKan p n := by
  apply NatTrans.ext
  funext E
  exact L.BLOCohomologyRightKanComponentIso_hom p hS sat n E

include hS sat in
theorem BLOCohomologyToRightKan_isIso (n : ℕ) :
    IsIso (L.BLOCohomologyToRightKan p n) := by
  rw [← L.BLOCohomologyRightKanIso_hom p hS sat n]
  infer_instance

theorem BLOCohomologyRightKanIso_naturality (n : ℕ)
    {E E' : F.ElementaryCategory p} (v : E ⟶ E') :
    (L.BLOCohomologyDiagram p n).map v ≫
        (L.BLOCohomologyRightKanIso p hS sat n).hom.app E' =
      (L.BLOCohomologyRightKanIso p hS sat n).hom.app E ≫
        (V28.rightKanCohomology p F n).map v :=
  (L.BLOCohomologyRightKanIso p hS sat n).hom.naturality v

@[reassoc] theorem BLOCohomologyRightKanIso_counit (n : ℕ)
    (X : (F.CentralizedCentralizerCover p)ᵒᵖ) :
    (L.BLOCohomologyRightKanIso p hS sat n).hom.app
        ((F.centralizerCoverFibration p).obj X) ≫
        ((F.centralizerCoverFibration p).ranCounit.app
          (V28.centralizerCoverCohomology p F n)).app X =
      (L.BLOCohomologyCoverRestriction p n).app X := by
  rw [L.BLOCohomologyRightKanIso_hom]
  exact L.BLOCohomologyToRightKan_counit_app p n X

end Sharpness.FusionSystem.CentricLinkingSystem
