import Sharpness.V28.InclusionMackey
import Sharpness.Manuscript.CohomologyUnconditional

/-! Native group cohomology sharpness through the new local-to-field theorem.
The values, restrictions and transfers are the existing native constructions;
no old cohomology sharpness endpoint is used. -/
set_option autoImplicit false
noncomputable section
universe u

namespace Sharpness.FusionSystem.V28
open CategoryTheory CategoryTheory.Limits

/-- Native cohomology with arbitrary trivial module coefficients over every
characteristic-p field, obtained from the new field-from-local deduction. -/
theorem cohomology_acyclic (p : ℕ) [Fact p.Prime]
    (k : Type u) [Field k] [CharP k p]
    {S : Type u} [Group S] [Finite S] (F : FusionSystem S)
    (hS : IsPGroup p S) (sat : F.Saturated p)
    {A : Type u} [AddCommGroup A] [Module k A] (n : ℕ) :
    Acyclic (F.cohomologyCoefficient (R := k) (A := A) n) :=
  acyclic_of_iso (F.nativeCohomologyMackeyCentricIso (R := k) (A := A) n)
    (field_sharpness_of_primeLocal p k F hS sat
      (F.nativeGroupCohomologyMackey (R := k) (A := A) n))

/-- Ordinary prime-field cohomology, in every cohomological degree. -/
theorem cohomology_primeField_acyclic (p : ℕ) [Fact p.Prime]
    {S : Type u} [Group S] [Finite S] (F : FusionSystem S)
    (hS : IsPGroup p S) (sat : F.Saturated p) (n : ℕ) :
    Acyclic (F.cohomologyCoefficient
      (R := PrimeField.{u} p) (A := PrimeField.{u} p) n) :=
  cohomology_acyclic p (PrimeField.{u} p) F hS sat n

/-- All positive higher limits of the ordinary prime-field cohomology functor vanish. -/
theorem cohomology_primeField_higherLimit_isZero (p : ℕ) [Fact p.Prime]
    {S : Type u} [Group S] [Finite S] (F : FusionSystem S)
    (hS : IsPGroup p S) (sat : F.Saturated p)
    (n i : ℕ) (hi : 0 < i) :
    IsZero (higherLimit (F.cohomologyCoefficient
      (R := PrimeField.{u} p) (A := PrimeField.{u} p) n) i) :=
  cohomology_primeField_acyclic p F hS sat n i hi

variable {S R A : Type u} [Group S] [Finite S] [CommRing R]
    [AddCommGroup A] [Module R A] (F : FusionSystem S)

/-- The native cohomology restriction and transfer functors before a Mackey
identity is added, using the proved native transfer laws. -/
def nativeCohomologyFunctorData (n : ℕ) : MackeyFunctorData.{u,u} R F.Orbit :=
  F.groupCohomologyFunctorData (F.cohomologyTransferLaws (R := R) (A := A) n)

/-- The actual inclusion double-coset identity for the native cohomology data. -/
theorem nativeCohomologyFunctorData_hasInclusionMackeyFormula (n : ℕ) :
    F.HasInclusionMackeyFormula (nativeCohomologyFunctorData (R := R) (A := A) F n) := by
  intro P Q T hP hQ
  exact F.groupCohomologyFunctorData_raw_identity
    (F.cohomologyTransferLaws (R := R) (A := A) n) (F.inclusion hP) (F.inclusion hQ)

/-- The inclusion-form assembly has the actual native cohomology coefficient
as its centric contravariant part. The native comparison is used explicitly. -/
def nativeCohomologyInclusionCentricIso (n : ℕ) :
    F.centricCoefficient (F.fullMackeyOfInclusionIdentity
      (nativeCohomologyFunctorData (R := R) (A := A) F n)
      (nativeCohomologyFunctorData_hasInclusionMackeyFormula F n)) ≅
      F.cohomologyCoefficient (R := R) (A := A) n :=
  F.nativeCohomologyMackeyCentricIso (R := R) (A := A) n

/-- The cohomology corollary also follows directly through the inclusion-form
endpoint with its concrete data, proved identity and native comparison. -/
theorem cohomology_primeField_acyclic_from_inclusionMackey
    (p : ℕ) [Fact p.Prime]
    {S : Type u} [Group S] [Finite S] (F : FusionSystem S)
    (hS : IsPGroup p S) (sat : F.Saturated p) (n : ℕ) :
    Acyclic (F.cohomologyCoefficient
      (R := PrimeField.{u} p) (A := PrimeField.{u} p) n) :=
  acyclic_of_iso
    (nativeCohomologyInclusionCentricIso (R := PrimeField.{u} p) (A := PrimeField.{u} p) F n)
    (inclusion_field_acyclic p (PrimeField.{u} p) F hS sat
      (nativeCohomologyFunctorData (R := PrimeField.{u} p) (A := PrimeField.{u} p) F n)
      (nativeCohomologyFunctorData_hasInclusionMackeyFormula F n))

end Sharpness.FusionSystem.V28
