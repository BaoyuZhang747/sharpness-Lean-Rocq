import Sharpness.V29.MainCohomology
import Sharpness.Unconditional.NormalizerHigherLimitComparisonRan
import Sharpness.Unconditional.NormalizerOrbitHigherLimits
import Sharpness.Unconditional.NormalizerOrbitProjectionCommaHigherLimits
import Sharpness.Unconditional.RightKanAcyclicComparison

/-! Native normalizer higher limits from local chain-normalizer acyclicity. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace Sharpness.FusionSystem.CentricLinkingSystem.V29
open CategoryTheory CategoryTheory.Limits Opposite
variable {S : Type u} [Group S] [Finite S] {F : FusionSystem S}
    (L : F.CentricLinkingSystem) (p : ℕ) [Fact p.Prime]
    (hS : IsPGroup p S) (sat : F.Saturated p)
    (k : Type u) [Field k] [CharP k p]

include L p hS sat

theorem normalizerRepresentativeAtChainHigherLimit_isZero
    {A : Type u} [AddCommGroup A] [Module k A]
    (d : F.NormalizerCategory) (n i : ℕ) (hi : 0 < i) :
    IsZero (higherLimit (F.normalizerAtChainCohomologyCoefficient k A
      (L.normalizerSylowRepresentative p hS sat d) n) i) :=
  IsZero.of_iso
    (FusionSystem.V29.cohomology_acyclic p k
      (L.chainNormalizerFusion (L.normalizerSylowRepresentative p hS sat d))
      (hS.to_subgroup _) (L.normalizerRepresentativeFusion_saturated p hS sat d)
      (A := A) n i hi)
    (L.normalizerRepresentativeAtChainHigherLimitIso p hS sat d n i)

theorem normalizerProjectionCommaHigherLimit_isZero
    {A : Type u} [AddCommGroup A] [Module k A]
    (d : F.NormalizerCategory) (n i : ℕ) (hi : 0 < i) :
    IsZero (covariantHigherLimit k
      (StructuredArrow.proj (op d) F.normalizerOrbitPairProjection.op ⋙
        F.normalizerOrbitPairForget.op ⋙ F.cohomologyCoefficient (R := k) (A := A) n) i) :=
  IsZero.of_iso
    (normalizerRepresentativeAtChainHigherLimit_isZero L p hS sat k d n i hi)
    (L.normalizerProjectionCommaCohomologyHigherLimitIso p hS sat k A d n i)

variable (A : ModuleCat.{u} k)

def normalizerPairRanHigherLimitIso (n i : ℕ) :
    higherLimit (F.normalizerOrbitPairForget.op ⋙
      F.cohomologyCoefficient (R := k) (A := A) n) i ≅
        higherLimit (F.normalizerOrbitPairProjection.op.ran.obj
          (F.normalizerOrbitPairForget.op ⋙ F.cohomologyCoefficient (R := k) (A := A) n)) i :=
  covariantHigherLimitRanIsoOfCommaAcyclicity k F.normalizerOrbitPairProjection.op
    (F.normalizerOrbitPairForget.op ⋙ F.cohomologyCoefficient (R := k) (A := A) n)
    (fun d j => normalizerProjectionCommaHigherLimit_isZero L p hS sat k
      (A := A) d.unop n (j + 1) (Nat.succ_pos j)) i

def normalizerNativeHigherLimitIso (n i : ℕ) :
    higherLimit (L.normalizerOrdinaryDiagram k A n) i ≅
      higherLimit (F.cohomologyCoefficient (R := k) (A := A) n) i :=
  Sharpness.higherLimitIso (L.normalizerRanNativeIso p hS sat k A n).symm i ≪≫
    (normalizerPairRanHigherLimitIso L p hS sat k A n i).symm ≪≫
      (F.normalizerOrbitHigherLimitIso p hS sat k
        (F.cohomologyCoefficient (R := k) (A := A) n) i).symm

theorem normalizerOrdinary_acyclic (n : ℕ) :
    Acyclic (L.normalizerOrdinaryDiagram k A n) := by
  intro i hi
  exact IsZero.of_iso
    (FusionSystem.V29.cohomology_acyclic p k F hS sat (A := A) n i hi)
    (normalizerNativeHigherLimitIso L p hS sat k A n i)

end Sharpness.FusionSystem.CentricLinkingSystem.V29
