import Sharpness.Unconditional.InductionAssembly
import Sharpness.Unconditional.FusionAtomicVanishing

/-! The main proof now reduces solely to centric supported acyclicity.
Atomic vanishing and every structural and homological comparison used in
the induction are supplied by constructions in this project. The final
`Unconditional.MainTheorem` supplies `CentricTheoremA` to this reduction. -/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness.FusionSystem
open CategoryTheory

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p]

theorem sharpness_of_supported_acyclicity
    (supported : ∀ (U : Type u) [Group U] [Finite U] (G : FusionSystem U),
      IsPGroup p U → G.Saturated p → G.SupportedCentricBridge (k := k))
    {S : Type u} [Group S] [Finite S] (F : FusionSystem S)
    (hS : IsPGroup p S) (sat : F.Saturated p) : F.Sharp (R := k) :=
  F.sharpness_of_supported_and_atomic p k supported
    (fun U _ _ G hU hG => G.nonradical_atomic_higherLimits_zero p hU hG k) hS sat

/-- A constructed bar comparison turns restricted centric acyclicity over
the localized integers into the supported full-Mackey statement over k. -/
def supportedCentricBridge_of_theoremA
    {S : Type u} [Group S] [Finite S] (F : FusionSystem S)
    (hS : IsPGroup p S) (sat : F.Saturated p)
    (DP : F.DiazParkTheoremAInput p hS sat) : F.SupportedCentricBridge (k := k) :=
  let B := Unconditional.barCalculationInput p k
  F.supportedCentricBridge p hS sat DP
    (B.model (PrimeLocalRing.{u} p) F.CentricOrbit)
    (B.comparison (PrimeLocalRing.{u} p) F.CentricOrbit)
    (B.model k F.CentricOrbit) (B.comparison k F.CentricOrbit)
    (B.scalar F.CentricOrbit)

/-- This intermediate implication is specialized to the constructed
centric restricted-Mackey theorem in `Unconditional.MainTheorem`. -/
theorem sharpness_of_centric_acyclicity
    (centric : ∀ (U : Type u) [Group U] [Finite U] (G : FusionSystem U)
      (hU : IsPGroup p U) (hG : G.Saturated p), G.DiazParkTheoremAInput p hU hG)
    {S : Type u} [Group S] [Finite S] (F : FusionSystem S)
    (hS : IsPGroup p S) (sat : F.Saturated p) : F.Sharp (R := k) :=
  F.sharpness_of_supported_acyclicity p k
    (fun U _ _ G hU hG => G.supportedCentricBridge_of_theoremA p k hU hG
      (centric U G hU hG)) hS sat

end Sharpness.FusionSystem
