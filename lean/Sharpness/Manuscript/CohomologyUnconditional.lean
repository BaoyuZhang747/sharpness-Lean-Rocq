import Sharpness.Manuscript.CohomologyMackeyAssembly
import Sharpness.Manuscript.CohomologySharpness
import Sharpness.Unconditional.FusionCohomologyPushComposition
import Sharpness.Unconditional.FusionCohomologyDoubleCosetIdentity
import Sharpness.PrimeFieldScalars

/-! The ordinary-cohomology corollary, with the actual native transfer laws
constructed from the proved trace, Shapiro, conjugation and double-coset
identities. No published-result, transfer-law or comparison input is assumed.
The construction works over every commutative ring with arbitrary trivial
module coefficients; sharpness specializes to fields of characteristic p. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness.FusionSystem
open CategoryTheory CategoryTheory.Limits

variable {S R A : Type u} [Group S] [Finite S] [CommRing R]
    [AddCommGroup A] [Module R A] (F : FusionSystem S)

/-- All transfer laws on fixed native cohomology values, now constructed. -/
def cohomologyTransferLaws (n : ℕ) : F.GroupCohomologyTransferLaws (R := R) A n :=
  F.cohomologyTransferLawsOfInclusions n
    (fun f g => F.nativeGroupCohomologyRawPush_comp f g n)
    (F.cohomologyFunctorDataOfPush_hasInclusionMackeyFormula n
      (fun f g => F.nativeGroupCohomologyRawPush_comp f g n))

theorem cohomologyTransferLaws_transfer (n : ℕ) :
    (F.cohomologyTransferLaws (R := R) (A := A) n).transfer =
      nativeGroupCohomologyTransfer n := rfl

/-- The native ordinary-cohomology Mackey functor for arbitrary trivial modules. -/
def nativeGroupCohomologyMackey (n : ℕ) : MackeyModule R F.Orbit F.mackeyShape :=
  F.groupCohomologyMackey (F.cohomologyTransferLaws (R := R) (A := A) n)

def nativeCohomologyMackeyCentricIso (n : ℕ) :
    F.centricCoefficient (F.nativeGroupCohomologyMackey (R := R) (A := A) n) ≅
      F.cohomologyCoefficient (R := R) (A := A) n :=
  F.cohomologyMackeyCentricIso n (F.cohomologyTransferLaws n)

/-- The original DP example, with its transfer record actually inhabited. -/
def nativeDPGroupCohomologyInput (n : ℕ) : F.DPGroupCohomologyInput (R := R) n :=
  F.cohomologyTransferLaws (A := R) n

/-- Ordinary cohomology sharpness, for every degree and arbitrary trivial
module coefficients over any field of characteristic p. -/
theorem cohomology_acyclic_unconditional
    (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p]
    {S : Type u} [Group S] [Finite S] (F : FusionSystem S)
    (hS : IsPGroup p S) (sat : F.Saturated p)
    {A : Type u} [AddCommGroup A] [Module k A] (n : ℕ) :
    Acyclic (F.cohomologyCoefficient (R := k) (A := A) n) :=
  F.cohomology_acyclic_of_transferLaws p k hS sat n (F.cohomologyTransferLaws n)

/-- Corollary `cor:cohomology` of the supplied manuscript, literally with F_p. -/
theorem cohomology_primeField_acyclic
    (p : ℕ) [Fact p.Prime] {S : Type u} [Group S] [Finite S]
    (F : FusionSystem S) (hS : IsPGroup p S) (sat : F.Saturated p) (n : ℕ) :
    Acyclic (F.cohomologyCoefficient (R := PrimeField.{u} p) (A := PrimeField.{u} p) n) :=
  F.cohomology_acyclic_unconditional p (PrimeField.{u} p) hS sat n

theorem cohomology_primeField_higherLimit_isZero
    (p : ℕ) [Fact p.Prime] {S : Type u} [Group S] [Finite S]
    (F : FusionSystem S) (hS : IsPGroup p S) (sat : F.Saturated p)
    (n i : ℕ) (hi : 0 < i) :
    IsZero (higherLimit
      (F.cohomologyCoefficient (R := PrimeField.{u} p) (A := PrimeField.{u} p) n) i) :=
  F.cohomology_primeField_acyclic p hS sat n i hi

end Sharpness.FusionSystem
