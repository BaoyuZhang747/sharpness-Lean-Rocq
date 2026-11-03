import Sharpness.Manuscript.CohomologyCoefficient
import Sharpness.Unconditional.MainTheorem

/-! The final algebraic deduction for the ordinary-cohomology corollary.
This intermediate theorem still requires an actual transfer-law structure;
the ongoing construction must supply that structure before the manuscript's
unconditional corollary can be exported. No published-result or bar-comparison
input is used in this deduction. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness.FusionSystem
open CategoryTheory

theorem cohomology_acyclic_of_transferLaws
    (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p]
    {S : Type u} [Group S] [Finite S] (F : FusionSystem S)
    (hS : IsPGroup p S) (sat : F.Saturated p)
    {A : Type u} [AddCommGroup A] [Module k A] (n : ℕ)
    (I : F.GroupCohomologyTransferLaws (R := k) A n) :
    Acyclic (F.cohomologyCoefficient (R := k) (A := A) n) :=
  acyclic_of_iso (F.cohomologyMackeyCentricIso n I)
    (F.saturated_fusion_sharpness_unconditional p k hS sat (F.groupCohomologyMackey I))

end Sharpness.FusionSystem
