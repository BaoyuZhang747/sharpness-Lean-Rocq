import Sharpness.V28.Cohomology
import Sharpness.V28.CentralizerComma
import Sharpness.Unconditional.CentralizerDetectionLocal
import Sharpness.Unconditional.SubsystemCohomologyTransport
import Sharpness.Unconditional.RightKanAcyclicComparisonFiber
import Mathlib.CategoryTheory.Limits.Final

/-! Right Kan extension of native prime-field cohomology to the elementary
category. Its arrows are the actual right Kan extension arrows. Positive fibre
acyclicity gives an all-degree comparison, retaining degree zero. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace Sharpness.FusionSystem.V28
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite

variable {S : Type u} [Group S] [Finite S] (p : ℕ) [Fact p.Prime]
    (F : FusionSystem S)

omit [Fact p.Prime] in
/-- The pre-fibred structure follows from the proved cartesian factorisation
of the actual centralizer cover. -/
theorem centralizerCover_isPreFibered (sat : F.Saturated p) :
    (F.centralizerCoverFibration p).IsPreFibered := by
  letI := F.centralizerCoverFibration_isFibered p sat
  infer_instance

/-- The native cohomology coefficient pulled back to the fully centralised cover. -/
def centralizerCoverCohomology (n : ℕ) :
    (F.CentralizedCentralizerCover p)ᵒᵖ ⥤ ModuleCat.{u} (PrimeField.{u} p) :=
  (F.centralizedCoverToCentric p).op ⋙
    F.cohomologyCoefficient (R := PrimeField.{u} p) (A := PrimeField.{u} p) n

/-- Native cohomology on the elementary category, defined by actual right Kan extension. -/
def rightKanCohomology (n : ℕ) :
    F.ElementaryCategory p ⥤ ModuleCat.{u} (PrimeField.{u} p) :=
  (F.centralizerCoverFibration p).ran.obj (centralizerCoverCohomology p F n)

/-- H_n uses the actual Ran arrows; no separately chosen limit diagram is used. -/
theorem rightKanCohomology_map (n : ℕ) {E E' : F.ElementaryCategory p} (f : E ⟶ E') :
    (rightKanCohomology p F n).map f =
      ((F.centralizerCoverFibration p).ran.obj
        (centralizerCoverCohomology p F n)).map f := rfl

/-- The actual Ran value is the ordinary limit of its strict-fibre coefficient. -/
def rightKanCohomologyFiberIso (sat : F.Saturated p) (n : ℕ)
    (E : F.ElementaryCategory p) :
    (rightKanCohomology p F n).obj E ≅
      limit (Fiber.fiberInclusion (p := F.centralizerCoverFibration p) (S := E) ⋙
        centralizerCoverCohomology p F n) := by
  letI := centralizerCover_isPreFibered p F sat
  exact ranFiberIso (PrimeField.{u} p) (F.centralizerCoverFibration p) E
    (centralizerCoverCohomology p F n)

/-- The fibre-limit comparison is the concrete right Kan counit comparison. -/
theorem rightKanCohomologyFiberIso_hom_projection (sat : F.Saturated p) (n : ℕ)
    (E : F.ElementaryCategory p) (X : Fiber (F.centralizerCoverFibration p) E) :
    (rightKanCohomologyFiberIso p F sat n E).hom ≫ limit.π _ X =
      (rightKanCohomology p F n).map (eqToHom X.property.symm) ≫
        ((F.centralizerCoverFibration p).ranCounit.app
          (centralizerCoverCohomology p F n)).app X.val := by
  letI := centralizerCover_isPreFibered p F sat
  exact ranFiberIso_hom_π (PrimeField.{u} p) (F.centralizerCoverFibration p) E
    (centralizerCoverCohomology p F n) X

variable (hS : IsPGroup p S) (sat : F.Saturated p)

/-- Restriction of the ambient native coefficient is naturally isomorphic to
the native cohomology coefficient of the actual centralizer fusion system. -/
def centralizerCohomologyCoefficientIso (n : ℕ) (E : F.ElementaryCategory p) :
    F.centralizerRestriction p hS sat
        (F.cohomologyCoefficient (R := PrimeField.{u} p) (A := PrimeField.{u} p) n) E ≅
      (F.centralizerSystem p E).cohomologyCoefficient
        (R := PrimeField.{u} p) (A := PrimeField.{u} p) n :=
  Functor.isoWhiskerLeft (F.centralizerSystem p E).centricInclusion.op
    (F.subsystemCohomologyOrbitIso (R := PrimeField.{u} p) (A := PrimeField.{u} p)
      (F.centralizerGroup p E) (F.centralizerSystem p E)
      (F.akoCentralizerInput p hS sat E).embedding n)

/-- The component of the coefficient identification is native pullback along
the literal subgroup-image equivalence. -/
theorem centralizerCohomologyCoefficientIso_hom_app (n : ℕ)
    (E : F.ElementaryCategory p) (P : (F.centralizerSystem p E).CentricOrbit) :
    (centralizerCohomologyCoefficientIso p F hS sat n E).hom.app (op P) =
      OrdinaryCohomology.pull
        (subgroupAmbientEquiv (F.centralizerGroup p E) P.obj.as.subgroup).toMonoidHom n := rfl

/-- Positive fibre acyclicity uses the new cohomology theorem for the saturated
actual centralizer, transported by the natural coefficient isomorphism. -/
theorem centralizerCohomology_acyclic (n : ℕ) (E : F.ElementaryCategory p) :
    Acyclic (F.centralizerRestriction p hS sat
      (F.cohomologyCoefficient (R := PrimeField.{u} p) (A := PrimeField.{u} p) n) E) :=
  acyclic_of_iso (centralizerCohomologyCoefficientIso p F hS sat n E)
    (cohomology_primeField_acyclic p (F.centralizerSystem p E)
      (hS.to_subgroup (F.centralizerGroup p E))
      (F.centralizerSystem_saturated p hS sat E) n)

include hS sat in
/-- Only positive strict-fibre higher limits are asserted to vanish. -/
theorem centralizerCoverCohomologyFiber_positive (n : ℕ) (E : F.ElementaryCategory p)
    (s : ℕ) (hs : 0 < s) :
    IsZero (covariantHigherLimit (PrimeField.{u} p)
      (Fiber.fiberInclusion (p := F.centralizerCoverFibration p) (S := E) ⋙
        centralizerCoverCohomology p F n) s) :=
  IsZero.of_iso (centralizerCohomology_acyclic p F hS sat n E s hs)
    (F.centralizerFiberHigherLimitIso (PrimeField.{u} p) p hS sat E
      (F.akoCentralizerInput p hS sat E)
      (F.cohomologyCoefficient (R := PrimeField.{u} p) (A := PrimeField.{u} p) n) s)

/-- A right Kan value is the limit of the actual ambient restriction to the centralizer. -/
def rightKanCohomologyRestrictionLimitIso (n : ℕ) (E : F.ElementaryCategory p) :
    (rightKanCohomology p F n).obj E ≅
      limit (F.centralizerRestriction p hS sat
        (F.cohomologyCoefficient (R := PrimeField.{u} p) (A := PrimeField.{u} p) n) E) :=
  rightKanCohomologyFiberIso p F sat n E ≪≫
    (Functor.Initial.limitIso
      (F.centralizerCoverFibrationFiberEquivalence p hS sat E
        (F.akoCentralizerInput p hS sat E)).functor
      (Fiber.fiberInclusion (p := F.centralizerCoverFibration p) (S := E) ⋙
        centralizerCoverCohomology p F n)).symm

/-- A right Kan value is the limit of native centralizer cohomology in every degree. -/
def rightKanCohomologyLimitIso (n : ℕ) (E : F.ElementaryCategory p) :
    (rightKanCohomology p F n).obj E ≅
      limit ((F.centralizerSystem p E).cohomologyCoefficient
        (R := PrimeField.{u} p) (A := PrimeField.{u} p) n) :=
  rightKanCohomologyRestrictionLimitIso p F hS sat n E ≪≫
    HasLimit.isoOfNatIso (centralizerCohomologyCoefficientIso p F hS sat n E)

variable [Nontrivial S]

/-- All higher limits, including degree zero, agree with the ambient
cohomology coefficient. Positive exactness preserves H_n in degree zero. -/
def rightKanCohomologyHigherLimitIso (n s : ℕ) :
    covariantHigherLimit (PrimeField.{u} p) (rightKanCohomology p F n) s ≅
      higherLimit (F.cohomologyCoefficient
        (R := PrimeField.{u} p) (A := PrimeField.{u} p) n) s := by
  letI := centralizerCover_isPreFibered p F sat
  exact (covariantHigherLimitRanIsoOfFiberAcyclicity (PrimeField.{u} p)
    (F.centralizerCoverFibration p) (centralizerCoverCohomology p F n)
    (fun E t => centralizerCoverCohomologyFiber_positive p F hS sat n E (t + 1)
      (Nat.zero_lt_succ t)) s).symm ≪≫
    (F.centralizerCoverHigherLimitIso (PrimeField.{u} p) p hS sat
      (F.cohomologyCoefficient (R := PrimeField.{u} p) (A := PrimeField.{u} p) n) s).symm

include hS sat in
/-- Positive higher limits of the right Kan extension vanish by ambient cohomology acyclicity. -/
theorem rightKanCohomology_positive_isZero (n s : ℕ) (hs : 0 < s) :
    IsZero (covariantHigherLimit (PrimeField.{u} p) (rightKanCohomology p F n) s) :=
  IsZero.of_iso (cohomology_primeField_acyclic p F hS sat n s hs)
    (rightKanCohomologyHigherLimitIso p F hS sat n s)

end Sharpness.FusionSystem.V28
