import Sharpness.SubsystemStableZero
import Sharpness.Unconditional.TraceFormulaInput
import Sharpness.Unconditional.Alperin
import Sharpness.Unconditional.DegreeZero
import Sharpness.Unconditional.ProjectiveCoefficients

set_option autoImplicit false
noncomputable section
universe u

namespace Sharpness.Revised.Baseline
open CategoryTheory CategoryTheory.Limits

variable {S : Type u} [Group S] [Finite S] (F : FusionSystem S)
    (T : Subgroup S) (H : FusionSystem T) (h : F.SubsystemEmbedding T H)
    {k : Type u} [Field k]
    (M : MackeyModule.{u,u,u} k F.Orbit F.mackeyShape) (label : F.SimpleLabel M)

/-- Subsystem stable elements vanish, with the trace and fusion inputs proved. -/
theorem subsystemLimitZero
    (p : ℕ) [Fact p.Prime] [CharP k p] (hS : IsPGroup p S)
    (satH : H.Saturated p)
    (centric : ∀ P : Subgroup T,
      H.IsCentric P → F.IsCentric (ambientSubgroup T P))
    (noncentric : ¬ F.IsCentric label.Q.as.subgroup) :
    Subsingleton (((H.coefficientData (F.subsystemMackey T H h M)).onFull
      H.centricProperty).limit) :=
  F.simple_native_subsystem_limit_zero T H h M label
    F.diazParkTraceInput p hS centric
    (H.alperinInput p (hS.to_subgroup T) satH) noncentric

/-- The zeroth subsystem higher limit vanishes using proved coefficient machinery. -/
theorem subsystemHigherLimitZero
    (p : ℕ) [Fact p.Prime] [CharP k p] (hS : IsPGroup p S)
    (satH : H.Saturated p)
    (centric : ∀ P : Subgroup T,
      H.IsCentric P → F.IsCentric (ambientSubgroup T P))
    (noncentric : ¬ F.IsCentric label.Q.as.subgroup) :
    IsZero (higherLimit
      ((F.subsystemCentricFunctor T H h centric).op ⋙ F.centricCoefficient M) 0) :=
  F.simple_native_subsystem_higherLimit_zero_degree T H h M label
    F.diazParkTraceInput p hS centric
    (H.alperinInput p (hS.to_subgroup T) satH) H.provedDegreeZeroInput noncentric

end Sharpness.Revised.Baseline
