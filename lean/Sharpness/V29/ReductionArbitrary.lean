import Sharpness.V29.ReductionComposition
import Sharpness.V29.FilteredLimitsMackey

/-! Lemma 2.9 through the actual filtered-direct-limit comparison and a
finite composition series of each finitely generated full Mackey subfunctor. -/
set_option autoImplicit false
noncomputable section
universe u

namespace Sharpness.FusionSystem.V29
open CategoryTheory CategoryTheory.Limits
open MackeyModule.V29

variable {S : Type u} [Group S] [Finite S] (F : FusionSystem S)

/-- The literal arbitrary-value conclusion of Lemma 2.9.  The only
simple-functor premise is the manuscript's noncentric-minimal case.
The finite-dimensional step is restricted to each given subfunctor's
composition factors; the arbitrary-value step uses the new colimit route. -/
theorem noncentric_simple_reduction (p : ℕ) [Fact p.Prime]
    (hS : IsPGroup p S) (sat : F.Saturated p)
    (h : ∀ N : MackeyModule.{u,u,u} (PrimeField.{u} p) F.Orbit F.mackeyShape,
      N.IsSimple →
      (∀ Q : Subgroup S, F.IsMinimalSupport N Q → ¬ F.IsCentric Q) →
      Acyclic (F.centricCoefficient N)) :
    F.Sharp (R := PrimeField.{u} p) := by
  classical
  intro M n hn
  apply F.higherLimit_isZero_of_fg_subfunctors_v29 M n
  intro N hfg
  haveI (P : F.Orbit) : FiniteDimensional (PrimeField.{u} p)
      ((M.submodule N).Value P) :=
    (Submodule.fg_iff_finiteDimensional _).mp (hfg P)
  obtain ⟨series, reduction⟩ :=
    finite_dimensional_noncentric_factors_reduction F p hS sat (M.submodule N)
  apply reduction _ n hn
  intro A hA hbad
  obtain ⟨Q, hQ, hQc⟩ := hbad
  have hs := series.factors_simple A hA
  exact h A hs (all_minimal_noncentric_of_one F p A hs Q hQ hQc)

/-- The all-simple specialisation, for use in the central quotient
proposition. It still follows the noncentric-factor composition-series
and filtered-colimit route. -/
theorem simple_reduction (p : ℕ) [Fact p.Prime]
    (hS : IsPGroup p S) (sat : F.Saturated p)
    (h : ∀ N : MackeyModule.{u,u,u} (PrimeField.{u} p) F.Orbit F.mackeyShape,
      N.IsSimple → Acyclic (F.centricCoefficient N)) :
    F.Sharp (R := PrimeField.{u} p) :=
  noncentric_simple_reduction F p hS sat (fun N hs _ => h N hs)

end Sharpness.FusionSystem.V29
