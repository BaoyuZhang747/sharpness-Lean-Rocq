import Sharpness.BLO.BLOEdgeNative
import Sharpness.BLO.BLOCohomologyCover
import Sharpness.V29.MainSubgroup

/-! The canonical restriction square, before any invertibility assertion for
the native BLO coefficient. Its proof uses actual subgroup restrictions and
the defining right Kan counit, not an abstract all-degree Ext comparison. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace Sharpness.FusionSystem.CentricLinkingSystem
open CategoryTheory CategoryTheory.Limits Opposite
variable {S : Type u} [Group S] [Finite S] {F : FusionSystem S}
    (L : F.CentricLinkingSystem) (p : ℕ) [Fact p.Prime]

def BLOEdgeLimitComparison (n : ℕ) :
    limit (L.BLOCohomologyDiagram p n) ⟶ limit (V28.centralizerCoverCohomology p F n) :=
  limMap (L.BLOCohomologyToRightKan p n) ≫ (BLO.BLOEdgeRanLimitIso p F n).hom

@[reassoc] theorem BLOEdgeLimitComparison_component (n : ℕ)
    (X : (F.CentralizedCentralizerCover p)ᵒᵖ) :
    L.BLOEdgeLimitComparison p n ≫ limit.π (V28.centralizerCoverCohomology p F n) X =
      limit.π (L.BLOCohomologyDiagram p n) ((F.centralizerCoverFibration p).obj X) ≫
        (L.BLOCohomologyCoverRestriction p n).app X := by
  simp only [BLOEdgeLimitComparison, Category.assoc, BLO.BLOEdgeRanLimitIso_component,
    limMap_π_assoc, L.BLOCohomologyToRightKan_counit_app]

variable [Nontrivial S] (hS : IsPGroup p S) (sat : F.Saturated p)

theorem BLOEdgeRestrictionToLimit_square (n : ℕ) :
    L.BLOEdgeRestrictionToLimit p n ≫ L.BLOEdgeLimitComparison p n =
      L.nativeOrdinaryRestrictionToLimit p hS sat (PrimeField.{u} p)
        (ModuleCat.of (PrimeField.{u} p) (PrimeField.{u} p)) n ≫
          (BLO.BLOEdgeAmbientCoverLimitIso p F hS sat n).hom := by
  apply limit.hom_ext
  intro X
  rw [Category.assoc, L.BLOEdgeLimitComparison_component, ← Category.assoc,
    L.BLOEdgeRestrictionToLimit_component]
  rw [Category.assoc, BLO.BLOEdgeAmbientCoverLimitIso_component]
  rw [show L.nativeOrdinaryRestrictionToLimit p hS sat (PrimeField.{u} p)
      (ModuleCat.of (PrimeField.{u} p) (PrimeField.{u} p)) n ≫
      limit.π (F.cohomologyCoefficient
        (R := PrimeField.{u} p) (A := PrimeField.{u} p) n)
        ((F.centralizedCoverToCentric p).op.obj X) = _ from
    L.nativeOrdinaryRestrictionToLimit_component p hS sat (PrimeField.{u} p)
      (ModuleCat.of (PrimeField.{u} p) (PrimeField.{u} p)) n X.unop.obj.centric]
  exact L.BLOCohomologyCoverRestriction_forget p n X

include hS sat in
theorem BLOEdgeRestrictionToLimit_isIso_of_comparison (n : ℕ)
    [IsIso (L.BLOCohomologyToRightKan p n)] :
    IsIso (L.BLOEdgeRestrictionToLimit p n) := by
  haveI : IsIso (L.BLOEdgeLimitComparison p n) := by
    unfold BLOEdgeLimitComparison
    infer_instance
  haveI := V29.nativeOrdinaryRestrictionToLimit_isIso L p hS sat (PrimeField.{u} p)
    (ModuleCat.of (PrimeField.{u} p) (PrimeField.{u} p)) n
  apply (isIso_comp_right_iff (L.BLOEdgeRestrictionToLimit p n)
    (L.BLOEdgeLimitComparison p n)).mp
  rw [L.BLOEdgeRestrictionToLimit_square p hS sat n]
  infer_instance

end Sharpness.FusionSystem.CentricLinkingSystem
