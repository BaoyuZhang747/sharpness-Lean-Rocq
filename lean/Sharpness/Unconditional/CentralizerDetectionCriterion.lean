import Sharpness.Unconditional.CentralizerDetection
import Sharpness.Unconditional.Alperin
import Sharpness.Unconditional.DegreeZero
import Sharpness.Unconditional.SimpleMackey
import Sharpness.Unconditional.TraceFormulaInput
import Sharpness.SubsystemStableZero
import Sharpness.ArbitraryCoefficients
import Sharpness.TrivialSharpness

/-! The centralizer sharpness criterion with the actual centralizer systems
and the proved all-degree detection theorem. The noncentric simple case has
no published inputs; the centric simple case is separated as the existing
supported-coefficient bridge. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

universe u
namespace Sharpness.FusionSystem
open CategoryTheory CategoryTheory.Limits

variable {S : Type u} [Group S] [Finite S] (F : FusionSystem S)
    (p : ℕ) [Fact p.Prime] (hS : IsPGroup p S) (sat : F.Saturated p)
    {k : Type u} [Field k] [CharP k p]

include hS sat

/-- Every derived limit of a simple coefficient with noncentric minimal label
vanishes, provided the actual elementary centralizer systems are sharp. -/
theorem centralizer_simple_noncentric_all_limits_zero_unconditional [Nontrivial S]
    (M : MackeyModule.{u,u,u} k F.Orbit F.mackeyShape) (label : F.SimpleLabel M)
    (noncentric : ¬ F.IsCentric label.Q.as.subgroup)
    (sharp : ∀ E : F.ElementaryCategory p, (F.centralizerSystem p E).Sharp (R := k))
    (n : ℕ) : IsZero (higherLimit (F.centricCoefficient M) n) := by
  apply F.centralizer_higherLimits_zero_of_local p hS sat (F.centricCoefficient M) _ n
  intro E m
  let C := F.akoCentralizerInput p hS sat E
  let centric := (F.yalcinCentralizerCentricInput p hS sat E C).centric
  cases m with
  | zero =>
    exact F.simple_native_subsystem_higherLimit_zero_degree
      (F.centralizerGroup p E) C.system C.embedding M label F.diazParkTraceInput p hS centric
      (C.system.alperinInput p (hS.to_subgroup _) C.AKO_I_5_5)
      C.system.provedDegreeZeroInput noncentric
  | succ m =>
    exact F.subsystemCoefficient_acyclic_of_sharp
      (F.centralizerGroup p E) C.system C.embedding centric M (sharp E) (m+1) (by omega)

/-- Sharpness reduces to the centric supported-coefficient result and sharpness
of the actual centralizer systems. Classification, trace, Alperin, centralizer
saturation, and detection are all proved inside this criterion. -/
theorem centralizer_sharpness_of_local
    (supported : F.SupportedCentricBridge (k := k))
    (bar : FiniteBarModel k F.CentricOrbit) (cmp : bar.Comparison)
    (sharp : ∀ E : F.ElementaryCategory p, (F.centralizerSystem p E).Sharp (R := k)) :
    F.Sharp (R := k) := by
  classical
  apply F.arbitrary_acyclic_of_simple bar cmp
  intro M hM
  obtain ⟨label⟩ := F.diazParkInputs.propositions_3_1_3_2 M hM
  by_cases hc : F.IsCentric label.Q.as.subgroup
  · exact F.centric_simple_acyclic F.diazParkInputs supported M label hc
  · cases subsingleton_or_nontrivial S with
    | inl hs =>
      letI := hs
      exact (hc (F.isCentric_of_subsingleton _)).elim
    | inr hn =>
      letI := hn
      intro n _
      exact F.centralizer_simple_noncentric_all_limits_zero_unconditional
        p hS sat M label hc sharp n

end Sharpness.FusionSystem
