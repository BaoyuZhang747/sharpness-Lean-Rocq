import Sharpness.Unconditional.NormalizerHigherLimitComparisonRan
import Sharpness.Unconditional.NormalizerOrbitHigherLimits
import Sharpness.Unconditional.NormalizerOrbitProjectionCommaHigherLimits
import Sharpness.Unconditional.RightKanAcyclicComparison

/-! Unconditional native normalizer higher-limit comparison and vanishing.
The actual pair forgetful functor is homologically cofinal; the actual
projection commas are acyclic for these native coefficients; and its
right Kan extension is naturally the actual normalizer diagram. All three
premises have been proved, including their diagram maps and degree zero. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace Sharpness.FusionSystem.CentricLinkingSystem
open CategoryTheory CategoryTheory.Limits Opposite
variable {S : Type u} [Group S] [Finite S] {F : FusionSystem S}
    (L : F.CentricLinkingSystem) (p : ℕ) [Fact p.Prime]
    (hS : IsPGroup p S) (sat : F.Saturated p)
    (k : Type u) [Field k] [CharP k p] (A : ModuleCat.{u} k)

/-- The actual native pair coefficient and its actual right Kan extension
have isomorphic higher limits in every degree. Local acyclicity is proved,
not supplied as an additional comparison hypothesis. -/
def normalizerPairRanHigherLimitIso (n i : ℕ) :
    higherLimit (F.normalizerOrbitPairForget.op ⋙
      F.cohomologyCoefficient (R := k) (A := A) n) i ≅
        higherLimit (F.normalizerOrbitPairProjection.op.ran.obj
          (F.normalizerOrbitPairForget.op ⋙ F.cohomologyCoefficient (R := k) (A := A) n)) i :=
  covariantHigherLimitRanIsoOfCommaAcyclicity k F.normalizerOrbitPairProjection.op
    (F.normalizerOrbitPairForget.op ⋙ F.cohomologyCoefficient (R := k) (A := A) n)
    (fun d j => L.normalizerProjectionCommaHigherLimit_isZero
      (B := A) p hS sat k d.unop n (j + 1) (Nat.succ_pos j)) i

/-- Every higher limit of the native normalizer diagram is identified with
the corresponding native centric-orbit cohomology higher limit. The middle
comparison uses the genuine natural Ran isomorphism, not pointwise choices. -/
def normalizerNativeHigherLimitIso (n i : ℕ) :
    higherLimit (L.normalizerOrdinaryDiagram k A n) i ≅
      higherLimit (F.cohomologyCoefficient (R := k) (A := A) n) i :=
  Sharpness.higherLimitIso (L.normalizerRanNativeIso p hS sat k A n).symm i ≪≫
    (L.normalizerPairRanHigherLimitIso p hS sat k A n i).symm ≪≫
      (F.normalizerOrbitHigherLimitIso p hS sat k
        (F.cohomologyCoefficient (R := k) (A := A) n) i).symm

include p hS sat in
/-- Native normalizer sharpness for every cohomology degree, every field of
characteristic p, and every trivial module, with no auxiliary comparison input. -/
theorem normalizerOrdinary_acyclic_unconditional (n : ℕ) :
    Acyclic (L.normalizerOrdinaryDiagram k A n) := by
  intro i hi
  exact IsZero.of_iso
    (F.cohomology_acyclic_unconditional p k hS sat (A := A) n i hi)
    (L.normalizerNativeHigherLimitIso p hS sat k A n i)

include p hS sat in
theorem normalizerOrdinary_higherLimit_isZero (n i : ℕ) (hi : 0 < i) :
    IsZero (higherLimit (L.normalizerOrdinaryDiagram k A n) i) :=
  L.normalizerOrdinary_acyclic_unconditional p hS sat k A n i hi

end Sharpness.FusionSystem.CentricLinkingSystem
