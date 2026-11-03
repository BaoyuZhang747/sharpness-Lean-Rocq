import Sharpness.V28.CentralizerRouteB
import Sharpness.V29.SubsystemDegreeZero
import Sharpness.V29.ReductionArbitrary
import Sharpness.TrivialSharpness

/-! The centraliser criterion using the v2.9 simple-summand degree-zero
argument and the composition-factor/direct-limit reduction. -/
set_option autoImplicit false
noncomputable section
universe u

namespace Sharpness.FusionSystem.V29
open CategoryTheory CategoryTheory.Limits

variable {S : Type u} [Group S] [Finite S] (F : FusionSystem S)
    (p : ℕ) [Fact p.Prime] (hS : IsPGroup p S) (sat : F.Saturated p)

include hS sat

theorem simple_noncentric_all_limits_zero
    [Nontrivial S]
    (M : MackeyModule.{u,u,u} (PrimeField.{u} p) F.Orbit F.mackeyShape)
    (label : F.SimpleLabel M)
    (noncentric : ¬ F.IsCentric label.Q.as.subgroup)
    (sharp : ∀ E : F.ElementaryCategory p,
      (F.centralizerSystem p E).Sharp (R := PrimeField.{u} p))
    (n : ℕ) : IsZero (higherLimit (F.centricCoefficient M) n) := by
  apply V28.centralizer_higherLimits_zero_routeB F p hS sat
    (F.centricCoefficient M) _ n
  intro E m
  let C := F.akoCentralizerInput p hS sat E
  let centric := (F.yalcinCentralizerCentricInput p hS sat E C).centric
  cases m with
  | zero =>
    exact subsystemHigherLimitZero F
      (F.centralizerGroup p E) C.system C.embedding M label p hS C.AKO_I_5_5
      centric noncentric
  | succ m =>
    exact F.subsystemCoefficient_acyclic_of_sharp
      (F.centralizerGroup p E) C.system C.embedding centric M (sharp E) (m + 1) (by omega)

theorem centralizer_sharpness_of_local
    (sharp : ∀ E : F.ElementaryCategory p,
      (F.centralizerSystem p E).Sharp (R := PrimeField.{u} p)) :
    F.Sharp (R := PrimeField.{u} p) := by
  classical
  apply noncentric_simple_reduction F p hS sat
  intro M hM hbad
  let label := F.simpleLabel M hM
  have hmin := simpleLabel_isMinimalSupport F p M hM
  have noncentric : ¬ F.IsCentric label.Q.as.subgroup := hbad _ hmin
  cases subsingleton_or_nontrivial S with
  | inl hs =>
    letI := hs
    exact (noncentric (F.isCentric_of_subsingleton _)).elim
  | inr hn =>
    letI := hn
    intro n _
    exact simple_noncentric_all_limits_zero F p hS sat M label noncentric sharp n

end Sharpness.FusionSystem.V29
