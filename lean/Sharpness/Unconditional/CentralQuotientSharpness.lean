import Sharpness.Unconditional.CentralQuotientCriterion
import Sharpness.Unconditional.FusionAtomicVanishing
import Sharpness.Unconditional.QuotientSaturationComplete

/-! The manuscript's central-quotient implication for the actual quotient
fusion system. All structural, atomic and bar comparisons are constructed. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness.FusionSystem

variable {S : Type u} [Group S] [Finite S] (F : FusionSystem S)
    {Z : Subgroup S} [Z.Normal] (hZ : F.CentralSubgroup Z)
    (p : ℕ) [Fact p.Prime] (hS : IsPGroup p S) (sat : F.Saturated p)
    {k : Type u} [Field k] [CharP k p]

include hS sat

/-- Sharpness of the constructed central quotient implies sharpness of F,
with no separate reference-input hypotheses. -/
theorem central_quotient_sharpness_unconditional
    (sharp : (F.centralQuotient hZ).Sharp (R := k)) : F.Sharp (R := k) :=
  F.central_quotient_sharpness_of_atomic hZ p hS sat (F.akoQuotientInput hZ p hS sat)
    (F.nonradical_atomic_higherLimits_zero p hS sat k) sharp

end Sharpness.FusionSystem
