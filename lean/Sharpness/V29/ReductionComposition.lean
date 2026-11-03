import Sharpness.V29.CompositionExact
import Sharpness.Manuscript.SimpleStatements
import Sharpness.Unconditional.CentricTheoremA
import Sharpness.Unconditional.CentricReduction
import Sharpness.PrimeFieldScalars

/-! The finite-dimensional, particular-composition-factor part of
Diaz--Park Proposition 4.3.  Only the noncentric factors of this M occur
in the premise.  Centric factors use the independently proved restricted
centric Mackey theorem. -/
set_option autoImplicit false
noncomputable section
universe u

namespace Sharpness.FusionSystem.V29
open CategoryTheory CategoryTheory.Limits
open MackeyModule.V29

variable {S : Type u} [Group S] [Finite S] (F : FusionSystem S)
    (p : ℕ) [Fact p.Prime] (hS : IsPGroup p S) (sat : F.Saturated p)

/-- The chosen least-order nonzero label is a minimal subgroup in the
manuscript's inclusion-minimal sense. -/
theorem simpleLabel_isMinimalSupport
    (M : MackeyModule.{u,u,u} (PrimeField.{u} p) F.Orbit F.mackeyShape)
    (hs : M.IsSimple) :
    F.IsMinimalSupport M (F.simpleLabel M hs).Q.as.subgroup := by
  let label := F.simpleLabel M hs
  exact F.isMinimalSupport_of_isConjugate M label.Q.as.subgroup label.nonzero
    (fun L hL => label.small_zero (F.toOrbit.obj ⟨L⟩) hL)
    label.Q.as.subgroup ⟨MulEquiv.refl _, F.isoSystem.id_mem _⟩

/-- If one minimal subgroup of a simple functor is noncentric, all are.
This is Lemma 2.8(i) plus invariance of centricity under fusion conjugacy. -/
theorem all_minimal_noncentric_of_one
    (M : MackeyModule.{u,u,u} (PrimeField.{u} p) F.Orbit F.mackeyShape)
    (hs : M.IsSimple) (Q : Subgroup S) (hQ : F.IsMinimalSupport M Q)
    (hbad : ¬ F.IsCentric Q) :
    ∀ L : Subgroup S, F.IsMinimalSupport M L → ¬ F.IsCentric L := by
  intro L hL hLc
  have heq := (F.simple_minimalSupport_class M hs Q hQ).1
  have hc : F.isoSystem.IsConjugate Q L := by
    have hm : L ∈ {P : Subgroup S | F.IsMinimalSupport M P} := hL
    rw [heq] at hm
    exact hm
  obtain ⟨e, he⟩ := hc
  exact hbad ((F.isoSystem.centricIn_iff_of_iso e he).mpr hLc)

include hS sat

/-- For a given finite composition series, only its noncentric-minimal
factors need an acyclicity hypothesis.  Each induction step uses its actual
pointwise short exact sequence and the higher-limit long exact sequence. -/
theorem composition_factors_noncentric_reduction
    (M : MackeyModule.{u,u,u} (PrimeField.{u} p) F.Orbit F.mackeyShape)
    (series : CompositionSeries M)
    (h : ∀ N ∈ series.factors,
      (∃ Q : Subgroup S, F.IsMinimalSupport N Q ∧ ¬ F.IsCentric Q) →
      Acyclic (F.centricCoefficient N)) : Acyclic (F.centricCoefficient M) := by
  apply acyclic_of_compositionSeries F M series
  intro N hN
  have hs : N.IsSimple := series.factors_simple N hN
  let label := F.simpleLabel N hs
  by_cases hc : F.IsCentric label.Q.as.subgroup
  · exact F.centric_simple_acyclic F.diazParkInputs
      (F.supportedCentricBridge_of_theoremA p (PrimeField.{u} p) hS sat
        (F.provedDiazParkTheoremAInput p hS sat)) N label hc
  · exact h N hN ⟨label.Q.as.subgroup, simpleLabel_isMinimalSupport F p N hs, hc⟩

/-- A specific finite-dimensional M, with a constructed finite composition
series. The assumption concerns only the noncentric simple factors of that
series, rather than all simple Mackey functors. -/
theorem finite_dimensional_noncentric_factors_reduction
    (M : MackeyModule.{u,u,u} (PrimeField.{u} p) F.Orbit F.mackeyShape)
    [∀ P, FiniteDimensional (PrimeField.{u} p) (M.Value P)] :
    ∃ series : CompositionSeries M,
      (∀ N ∈ series.factors,
        (∃ Q : Subgroup S, F.IsMinimalSupport N Q ∧ ¬ F.IsCentric Q) →
        Acyclic (F.centricCoefficient N)) → Acyclic (F.centricCoefficient M) := by
  classical
  letI : Fintype F.Orbit := Fintype.ofFinite _
  let series := compositionSeries M
  exact ⟨series, composition_factors_noncentric_reduction F p hS sat M series⟩

end Sharpness.FusionSystem.V29
