import Sharpness.Manuscript.SimpleStatements
import Sharpness.Unconditional.CentricTheoremA
import Sharpness.Unconditional.CentricReduction
import Sharpness.PrimeFieldScalars

/-! Manuscript Lemma `lem:reduction`, with its literal noncentric-simple
hypothesis and arbitrary coefficient values. Centric simple functors are
handled by the constructed centric theorem, and all other simple functors by
the stated hypothesis. The general simple-to-arbitrary reduction is proved
using finite generation and the actual bar calculation. -/
set_option autoImplicit false
noncomputable section
universe u

namespace Sharpness.FusionSystem
open CategoryTheory

variable {S : Type u} [Group S] [Finite S] (F : FusionSystem S)

/-- The exact hypothesis and conclusion of Lemma `lem:reduction`. -/
theorem noncentric_simple_reduction (p : ℕ) [Fact p.Prime]
    (hS : IsPGroup p S) (sat : F.Saturated p)
    (h : ∀ N : MackeyModule.{u,u,u} (PrimeField.{u} p) F.Orbit F.mackeyShape,
      N.IsSimple →
      (∀ Q : Subgroup S, F.IsMinimalSupport N Q → ¬ F.IsCentric Q) →
      Acyclic (F.centricCoefficient N)) :
    F.Sharp (R := PrimeField.{u} p) := by
  classical
  let B := Unconditional.barCalculationInput p (PrimeField.{u} p)
  apply F.arbitrary_acyclic_of_simple (B.model (PrimeField.{u} p) F.CentricOrbit)
    (B.comparison (PrimeField.{u} p) F.CentricOrbit)
  intro M hM
  let label := F.simpleLabel M hM
  by_cases hc : F.IsCentric label.Q.as.subgroup
  · exact F.centric_simple_acyclic F.diazParkInputs
      (F.supportedCentricBridge_of_theoremA p (PrimeField.{u} p) hS sat
        (F.provedDiazParkTheoremAInput p hS sat)) M label hc
  · apply h M hM
    intro Q hQ hQc
    obtain ⟨e, he⟩ := F.isConjugate_of_isMinimalSupport M label.Q.as.subgroup
      hM label.nonzero (fun L hL => label.small_zero (F.toOrbit.obj ⟨L⟩) hL) Q hQ
    exact hc ((F.isoSystem.centricIn_iff_of_iso e he).mpr hQc)

end Sharpness.FusionSystem
