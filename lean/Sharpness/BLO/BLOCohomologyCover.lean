import Sharpness.BLO.BLOCohomologyRestrictions
import Sharpness.V28.RightKanCohomology
import Sharpness.LinkingOrbitLifts

/-! The canonical natural comparison to the existing E3 right Kan extension.
Its cover components are literal BP restrictions.  Orbit representatives and
linking lifts occur only in the proof that these components are natural. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace Sharpness.FusionSystem.CentricLinkingSystem
open CategoryTheory CategoryTheory.Limits Opposite

variable {S : Type u} [Group S] [Finite S] {F : FusionSystem S}
    (L : F.CentricLinkingSystem) (p : ℕ) [Fact p.Prime]

def BLOCohomologyCoverPoint (X : F.CentralizedCentralizerCover p) :
    L.BLODiagramObject (F.centralizedCoverElementary p X).obj where
  point := L.linkingObjectOfOrbit X.obj.centric
  label := F.inclusion X.obj.le_subgroup
  central e := by
    apply Subgroup.mem_center_iff.mpr
    intro x
    apply Subtype.ext
    exact (Subgroup.mem_centralizer_iff.mp (X.obj.centralizes e.property)) x.val x.property

def BLOCohomologyCoverLift {X Y : F.CentralizedCentralizerCover p} (f : X ⟶ Y) :
    (L.BLODiagramPrecomp (X.obj.inverseRestriction Y.obj f.hom)).obj
        (L.BLOCohomologyCoverPoint p X) ⟶ L.BLOCohomologyCoverPoint p Y := by
  refine ⟨L.liftOrbitArrow f.hom.val, ?_⟩
  apply Subtype.ext
  apply MonoidHom.ext
  intro e
  apply Subtype.ext
  exact X.obj.inverseRestriction_spec Y.obj f.hom
    (L.projection.map (L.liftOrbitArrow f.hom.val))
    (by rw [L.projection_liftOrbitArrow]; exact F.orbitRepresentative_map _) e

def BLOCohomologyCoverRestriction (n : ℕ) :
    F.centralizerCoverFibration p ⋙ L.BLOCohomologyDiagram p n ⟶
      V28.centralizerCoverCohomology p F n where
  app X := L.BLOCohomologyRestriction (PrimeField.{u} p)
    (ModuleCat.of (PrimeField.{u} p) (PrimeField.{u} p)) n
    (L.BLOCohomologyCoverPoint p X.unop)
  naturality {X Y} f := by
    change BLOCohomologyPull (PrimeField.{u} p)
        (ModuleCat.of (PrimeField.{u} p) (PrimeField.{u} p)) n
        (L.BLODiagramPrecomp (Y.unop.obj.inverseRestriction X.unop.obj f.unop.hom)) ≫
        L.BLOCohomologyRestriction (PrimeField.{u} p)
          (ModuleCat.of (PrimeField.{u} p) (PrimeField.{u} p)) n
          (L.BLOCohomologyCoverPoint p Y.unop) = _
    rw [L.BLOCohomologyRestriction_precomp]
    have h := L.BLOCohomologyRestriction_arrow (PrimeField.{u} p)
      (ModuleCat.of (PrimeField.{u} p) (PrimeField.{u} p)) n
      (L.BLOCohomologyCoverLift p f.unop)
    have hd : (V28.centralizerCoverCohomology p F n).map f =
        OrdinaryCohomology.pull (R := PrimeField.{u} p) (A := PrimeField.{u} p)
          (L.projection.map (L.liftOrbitArrow f.unop.hom.val)).val n := by
      rw [L.projection_liftOrbitArrow]
      rfl
    rw [hd]
    exact h

theorem BLOCohomologyCoverRestriction_app (n : ℕ)
    (X : (F.CentralizedCentralizerCover p)ᵒᵖ) :
    (L.BLOCohomologyCoverRestriction p n).app X =
      SingularCohomology.pull (PrimeField.{u} p)
        (L.BLODiagramSubgroupClassifyingMap (L.BLOCohomologyCoverPoint p X.unop))
        (ModuleCat.of (PrimeField.{u} p) (PrimeField.{u} p)) n ≫
        (OrdinaryCohomology.groupClassifyingCohomologyIso (PrimeField.{u} p)
          X.unop.obj.centric.obj.as.subgroup
          (ModuleCat.of (PrimeField.{u} p) (PrimeField.{u} p)) n).hom := rfl

def BLOCohomologyToRightKan (n : ℕ) :
    L.BLOCohomologyDiagram p n ⟶ V28.rightKanCohomology p F n :=
  ((F.centralizerCoverFibration p).ran.obj
    (V28.centralizerCoverCohomology p F n)).liftOfIsRightKanExtension
    ((F.centralizerCoverFibration p).ranCounit.app
      (V28.centralizerCoverCohomology p F n))
    (L.BLOCohomologyDiagram p n) (L.BLOCohomologyCoverRestriction p n)

theorem BLOCohomologyToRightKan_counit (n : ℕ) :
    Functor.whiskerLeft (F.centralizerCoverFibration p) (L.BLOCohomologyToRightKan p n) ≫
        (F.centralizerCoverFibration p).ranCounit.app
          (V28.centralizerCoverCohomology p F n) =
      L.BLOCohomologyCoverRestriction p n := by
  unfold BLOCohomologyToRightKan
  exact Functor.liftOfIsRightKanExtension_fac
    ((F.centralizerCoverFibration p).ran.obj (V28.centralizerCoverCohomology p F n))
    ((F.centralizerCoverFibration p).ranCounit.app (V28.centralizerCoverCohomology p F n))
    (L.BLOCohomologyDiagram p n) (L.BLOCohomologyCoverRestriction p n)

@[reassoc] theorem BLOCohomologyToRightKan_counit_app (n : ℕ)
    (X : (F.CentralizedCentralizerCover p)ᵒᵖ) :
    (L.BLOCohomologyToRightKan p n).app ((F.centralizerCoverFibration p).obj X) ≫
        ((F.centralizerCoverFibration p).ranCounit.app
          (V28.centralizerCoverCohomology p F n)).app X =
      (L.BLOCohomologyCoverRestriction p n).app X :=
  congr_app (L.BLOCohomologyToRightKan_counit p n) X

theorem BLOCohomologyToRightKan_naturality (n : ℕ)
    {E E' : F.ElementaryCategory p} (v : E ⟶ E') :
    (L.BLOCohomologyDiagram p n).map v ≫ (L.BLOCohomologyToRightKan p n).app E' =
      (L.BLOCohomologyToRightKan p n).app E ≫ (V28.rightKanCohomology p F n).map v :=
  (L.BLOCohomologyToRightKan p n).naturality v

@[reassoc] theorem BLOCohomologyCoverRestriction_forget (n : ℕ)
    (X : (F.CentralizedCentralizerCover p)ᵒᵖ) :
    BLOCohomologyPull (PrimeField.{u} p)
        (ModuleCat.of (PrimeField.{u} p) (PrimeField.{u} p)) n
        (L.BLODiagramForget (F.centralizedCoverElementary p X.unop).obj) ≫
        (L.BLOCohomologyCoverRestriction p n).app X =
      SingularCohomology.pull (PrimeField.{u} p)
        (L.subgroupClassifyingMap (L.linkingObjectOfOrbit X.unop.obj.centric))
        (ModuleCat.of (PrimeField.{u} p) (PrimeField.{u} p)) n ≫
        (OrdinaryCohomology.groupClassifyingCohomologyIso (PrimeField.{u} p)
          X.unop.obj.centric.obj.as.subgroup
          (ModuleCat.of (PrimeField.{u} p) (PrimeField.{u} p)) n).hom :=
  L.BLOCohomologyRestriction_forget (PrimeField.{u} p)
    (ModuleCat.of (PrimeField.{u} p) (PrimeField.{u} p)) n
    (L.BLOCohomologyCoverPoint p X.unop)

end Sharpness.FusionSystem.CentricLinkingSystem
