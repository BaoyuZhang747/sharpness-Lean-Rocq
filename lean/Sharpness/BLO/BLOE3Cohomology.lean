import Sharpness.V29.MainCohomology
import Sharpness.V28.RightKanCohomology

/-!
E3 companions using the Task 1 cohomology corollary, at the actual centraliser
fusion systems and at the ambient system. The coefficient is the unchanged
existing right Kan extension, including its arrow maps.

All coefficients below are covariant on `F.ElementaryCategory p`. Thus their
`covariantHigherLimit` is computed in that covariant functor category, or
equivalently with the contravariant coefficient convention on its opposite.
Only positive derived degrees vanish; degree zero is retained in the comparison.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace Sharpness.FusionSystem.BLO
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite

variable {S : Type u} [Group S] [Finite S] (p : ℕ) [Fact p.Prime]
    (F : FusionSystem S) (hS : IsPGroup p S) (sat : F.Saturated p)

/-- Corollary 1.2 applies to each actual saturated centraliser fusion system;
the ambient restriction coefficient is identified with its native cohomology. -/
theorem centralizerCohomology_acyclic (n : ℕ) (E : F.ElementaryCategory p) :
    Acyclic (F.centralizerRestriction p hS sat
      (F.cohomologyCoefficient (R := PrimeField.{u} p) (A := PrimeField.{u} p) n) E) :=
  acyclic_of_iso (V28.centralizerCohomologyCoefficientIso p F hS sat n E)
    (V29.cohomology_primeField_acyclic p (F.centralizerSystem p E)
      (hS.to_subgroup (F.centralizerGroup p E))
      (F.centralizerSystem_saturated p hS sat E) n)

include hS sat in
/-- The strict fibres of the actual centraliser-cover coefficient have zero
positive higher limits. No assertion is made about their ordinary limits. -/
theorem centralizerCoverCohomologyFiber_positive (n : ℕ) (E : F.ElementaryCategory p)
    (s : ℕ) (hs : 0 < s) :
    IsZero (covariantHigherLimit (PrimeField.{u} p)
      (Fiber.fiberInclusion (p := F.centralizerCoverFibration p) (S := E) ⋙
        V28.centralizerCoverCohomology p F n) s) :=
  IsZero.of_iso (centralizerCohomology_acyclic p F hS sat n E s hs)
    (F.centralizerFiberHigherLimitIso (PrimeField.{u} p) p hS sat E
      (F.akoCentralizerInput p hS sat E)
      (F.cohomologyCoefficient (R := PrimeField.{u} p) (A := PrimeField.{u} p) n) s)

variable [Nontrivial S]

/-- The actual E3 right Kan extension has the ambient higher limits in every
degree. This companion uses the new corollary on centralisers through the
positive-exactness comparison, and preserves the degree-zero resolution term. -/
def rightKanCohomologyHigherLimitIso (n s : ℕ) :
    covariantHigherLimit (PrimeField.{u} p) (V28.rightKanCohomology p F n) s ≅
      higherLimit (F.cohomologyCoefficient
        (R := PrimeField.{u} p) (A := PrimeField.{u} p) n) s := by
  letI := V28.centralizerCover_isPreFibered p F sat
  exact (covariantHigherLimitRanIsoOfFiberAcyclicity (PrimeField.{u} p)
    (F.centralizerCoverFibration p) (V28.centralizerCoverCohomology p F n)
    (fun E t => centralizerCoverCohomologyFiber_positive p F hS sat n E (t + 1)
      (Nat.zero_lt_succ t)) s).symm ≪≫
    (F.centralizerCoverHigherLimitIso (PrimeField.{u} p) p hS sat
      (F.cohomologyCoefficient (R := PrimeField.{u} p) (A := PrimeField.{u} p) n) s).symm

include hS sat in
/-- Positive derived limits of the actual Ran coefficient vanish by the new
ambient cohomology corollary and the new centraliser-dependent comparison. -/
theorem rightKanCohomology_positive_isZero (n s : ℕ) (hs : 0 < s) :
    IsZero (covariantHigherLimit (PrimeField.{u} p) (V28.rightKanCohomology p F n) s) :=
  IsZero.of_iso (V29.cohomology_primeField_acyclic p F hS sat n s hs)
    (rightKanCohomologyHigherLimitIso p F hS sat n s)

/-- Transport the actual derived-limit comparison through a natural
coefficient isomorphism. The native BLO endpoint must supply its proved
diagram comparison, rather than assume this argument as a new hypothesis. -/
def cohomologyHigherLimitIso_of_natIso (n : ℕ)
    {K : F.ElementaryCategory p ⥤ ModuleCat.{u} (PrimeField.{u} p)}
    (e : K ≅ V28.rightKanCohomology p F n) (s : ℕ) :
    covariantHigherLimit (PrimeField.{u} p) K s ≅
      higherLimit (F.cohomologyCoefficient
        (R := PrimeField.{u} p) (A := PrimeField.{u} p) n) s :=
  ((Ext (PrimeField.{u} p)
      (F.ElementaryCategory p ⥤ ModuleCat.{u} (PrimeField.{u} p)) s).obj
      (op ((Functor.const (F.ElementaryCategory p)).obj
        (ModuleCat.of (PrimeField.{u} p) (PrimeField.{u} p))))).mapIso e ≪≫
    rightKanCohomologyHigherLimitIso p F hS sat n s

include hS sat in
/-- Generic natural-isomorphism transport of positive derived-limit vanishing,
with explicit covariant variance and no degree-zero vanishing premise. -/
theorem cohomology_positive_isZero_of_natIso (n : ℕ)
    {K : F.ElementaryCategory p ⥤ ModuleCat.{u} (PrimeField.{u} p)}
    (e : K ≅ V28.rightKanCohomology p F n) (s : ℕ) (hs : 0 < s) :
    IsZero (covariantHigherLimit (PrimeField.{u} p) K s) :=
  IsZero.of_iso (V29.cohomology_primeField_acyclic p F hS sat n s hs)
    (cohomologyHigherLimitIso_of_natIso p F hS sat n e s)

end Sharpness.FusionSystem.BLO
