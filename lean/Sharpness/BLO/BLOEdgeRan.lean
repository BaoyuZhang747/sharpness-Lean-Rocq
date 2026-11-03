import Sharpness.V28.RightKanCohomology

/-! Ordinary limits of the actual E3 right Kan extension.  These maps carry
the counit component formula; no degree-zero Ext comparison is substituted
for the canonical ordinary-limit map. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace Sharpness.FusionSystem.BLO
open CategoryTheory CategoryTheory.Limits Opposite

variable {S : Type u} [Group S] [Finite S] (p : ℕ) [Fact p.Prime]
    (F : FusionSystem S)

def BLOEdgeRanLimitIso (n : ℕ) :
    limit (V28.rightKanCohomology p F n) ≅
      limit (V28.centralizerCoverCohomology p F n) :=
  Functor.limitIsoOfIsRightKanExtension _
    ((F.centralizerCoverFibration p).ranCounit.app
      (V28.centralizerCoverCohomology p F n))

@[reassoc] theorem BLOEdgeRanLimitIso_component (n : ℕ)
    (X : (F.CentralizedCentralizerCover p)ᵒᵖ) :
    (BLOEdgeRanLimitIso p F n).hom ≫
        limit.π (V28.centralizerCoverCohomology p F n) X =
      limit.π (V28.rightKanCohomology p F n)
          ((F.centralizerCoverFibration p).obj X) ≫
        ((F.centralizerCoverFibration p).ranCounit.app
          (V28.centralizerCoverCohomology p F n)).app X :=
  Functor.limitIsoOfIsRightKanExtension_hom_π _ _ X

variable [Nontrivial S] (hS : IsPGroup p S) (sat : F.Saturated p)

include hS sat in
theorem BLOEdgeCoverOpposite_initial :
    (F.centralizedCoverToCentric p).op.Initial := by
  letI : (F.centralizerCoverForget p).Final :=
    Functor.final_of_adjunction (F.centralizerCoverSectionAdjunction p hS)
  letI : (F.centralizedCentralizerCoverInclusion p).IsEquivalence :=
    (F.centralizedCentralizerCoverEquivalence p sat).isEquivalence_functor
  change ((F.centralizedCentralizerCoverInclusion p).op ⋙
    (F.centralizerCoverForget p).op).Initial
  infer_instance

def BLOEdgeAmbientCoverLimitIso (n : ℕ) :
    limit (F.cohomologyCoefficient
      (R := PrimeField.{u} p) (A := PrimeField.{u} p) n) ≅
      limit (V28.centralizerCoverCohomology p F n) := by
  letI := BLOEdgeCoverOpposite_initial p F hS sat
  exact asIso (limit.pre
    (F.cohomologyCoefficient (R := PrimeField.{u} p) (A := PrimeField.{u} p) n)
    (F.centralizedCoverToCentric p).op)

@[reassoc] theorem BLOEdgeAmbientCoverLimitIso_component (n : ℕ)
    (X : (F.CentralizedCentralizerCover p)ᵒᵖ) :
    (BLOEdgeAmbientCoverLimitIso p F hS sat n).hom ≫
        limit.π (V28.centralizerCoverCohomology p F n) X =
      limit.π (F.cohomologyCoefficient
        (R := PrimeField.{u} p) (A := PrimeField.{u} p) n)
        ((F.centralizedCoverToCentric p).op.obj X) :=
  limit.pre_π _ _ _

def BLOEdgeAmbientRanLimitIso (n : ℕ) :
    limit (F.cohomologyCoefficient
      (R := PrimeField.{u} p) (A := PrimeField.{u} p) n) ≅
      limit (V28.rightKanCohomology p F n) :=
  BLOEdgeAmbientCoverLimitIso p F hS sat n ≪≫
    (BLOEdgeRanLimitIso p F n).symm

@[reassoc] theorem BLOEdgeAmbientRanLimitIso_counit (n : ℕ)
    (X : (F.CentralizedCentralizerCover p)ᵒᵖ) :
    (BLOEdgeAmbientRanLimitIso p F hS sat n).hom ≫
        limit.π (V28.rightKanCohomology p F n)
          ((F.centralizerCoverFibration p).obj X) ≫
        ((F.centralizerCoverFibration p).ranCounit.app
          (V28.centralizerCoverCohomology p F n)).app X =
      limit.π (F.cohomologyCoefficient
        (R := PrimeField.{u} p) (A := PrimeField.{u} p) n)
        ((F.centralizedCoverToCentric p).op.obj X) := by
  rw [← BLOEdgeRanLimitIso_component]
  simp only [BLOEdgeAmbientRanLimitIso, Iso.trans_hom, Iso.symm_hom,
    Category.assoc, Iso.inv_hom_id_assoc]
  exact BLOEdgeAmbientCoverLimitIso_component p F hS sat n X

end Sharpness.FusionSystem.BLO
