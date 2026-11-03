import Sharpness.Unconditional.NormalizerOrbitProjectionCommaReflection
import Sharpness.Unconditional.CentralizerDetectionComparison
import Sharpness.Unconditional.NormalizerHigherLimitComparisonLocalZero

/-! The actual structured-arrow higher limits used by right Kan extension
reduce to the already-proved fixed-chain local higher limits. This uses the
constructed reflection and the literal comma-op equivalence, in every degree. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace Sharpness.FusionSystem.CentricLinkingSystem
open CategoryTheory CategoryTheory.Limits Opposite
variable {S : Type u} [Group S] [Finite S] {F : FusionSystem S}
  (L : F.CentricLinkingSystem) (p : ℕ) [Fact p.Prime]
  (hS : IsPGroup p S) (sat : F.Saturated p)
  (R : Type u) [CommRing R]

/-- The exact derived comma comparison for arbitrary module-valued diagrams. -/
def normalizerProjectionCommaHigherLimitIso (d : F.NormalizerCategory)
    (M : StructuredArrow (op d) F.normalizerOrbitPairProjection.op ⥤ ModuleCat.{u} R) (i : ℕ) :
    covariantHigherLimit R M i ≅
      higherLimit (F.normalizerAtChainToStructuredComma
        (L.normalizerSylowRepresentative p hS sat d) d
        (L.normalizerSylowRepresentative_class p hS sat d) ⋙ M) i :=
  covariantHigherLimitEquivalenceIso R
      (costructuredArrowOpEquivalence F.normalizerOrbitPairProjection d) M i ≪≫
    higherLimitRightAdjointIso R (L.normalizerOrbitCommaReflection p hS sat d)
      (L.normalizerRepresentativeCommaInclusion p hS sat d)
      (L.normalizerOrbitCommaReflectionAdjunction p hS sat d) _ i

variable (A : Type u) [AddCommGroup A] [Module R A]

/-- The comparison restricts the literal ambient cohomology coefficient to
the literal same-chain category, with no replacement of coefficients. -/
def normalizerProjectionCommaCohomologyHigherLimitIso (d : F.NormalizerCategory) (n i : ℕ) :
    covariantHigherLimit R
      (StructuredArrow.proj (op d) F.normalizerOrbitPairProjection.op ⋙
        F.normalizerOrbitPairForget.op ⋙ F.cohomologyCoefficient (R := R) (A := A) n) i ≅
      higherLimit (F.normalizerAtChainCohomologyCoefficient R A
        (L.normalizerSylowRepresentative p hS sat d) n) i :=
  L.normalizerProjectionCommaHigherLimitIso p hS sat R d _ i

variable (k : Type u) [Field k] [CharP k p]
  {B : Type u} [AddCommGroup B] [Module k B]

include L hS sat in
/-- Exact positive local acyclicity required by the right-Kan comparison.
The cohomology degree n and positive higher-limit degree i are independent. -/
theorem normalizerProjectionCommaHigherLimit_isZero (d : F.NormalizerCategory)
    (n i : ℕ) (hi : 0 < i) :
    IsZero (covariantHigherLimit k
      (StructuredArrow.proj (op d) F.normalizerOrbitPairProjection.op ⋙
        F.normalizerOrbitPairForget.op ⋙ F.cohomologyCoefficient (R := k) (A := B) n) i) :=
  IsZero.of_iso
    (L.normalizerRepresentativeAtChainHigherLimit_isZero p hS sat k d n i hi)
    (L.normalizerProjectionCommaCohomologyHigherLimitIso p hS sat k B d n i)

/-- Degree zero is retained: it is the actual cohomology of the compatible
linking-chain automorphism group at the constructed Sylow representative. -/
def normalizerProjectionCommaHigherLimitZeroIso (d : F.NormalizerCategory) (n : ℕ) :
    covariantHigherLimit k
      (StructuredArrow.proj (op d) F.normalizerOrbitPairProjection.op ⋙
        F.normalizerOrbitPairForget.op ⋙ F.cohomologyCoefficient (R := k) (A := B) n) 0 ≅
      OrdinaryCohomology.value k (L.ChainAut (L.normalizerSylowRepresentative p hS sat d)) B n :=
  L.normalizerProjectionCommaCohomologyHigherLimitIso p hS sat k B d n 0 ≪≫
    L.normalizerRepresentativeAtChainHigherLimitZeroIso p hS sat k d n

end Sharpness.FusionSystem.CentricLinkingSystem
