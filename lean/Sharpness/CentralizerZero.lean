import Sharpness.NormalizerAction

/-!
Manuscript Lemma 2.6. The input is precisely the relative-trace value and
restriction description in DP Section 3, equations (4) and (6), pp.153--154.
The characteristic-p cancellation on actual normalizer quotient groups is
proved in NormalizerAction, not assumed as a literature theorem.
-/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness.FusionSystem
open CategoryTheory
variable {S : Type u} [Group S] [Finite S] (F : FusionSystem S)
    {k : Type u} [Field k]

/-- At a minimal-class subgroup L, equation (6) projects onto the L trace
summand of equation (4). Thus the restriction has image in that trace.
This statement has no characteristic-p or centralizer hypothesis. -/
structure DiazParkTraceInput where
  equations_4_6 : ∀ (M : MackeyModule.{u,u,u} k F.Orbit F.mackeyShape)
    (label : F.SimpleLabel M) (T L : Subgroup S) (hLT : L ≤ T),
    Nonempty (label.Q ≅ F.toOrbit.obj ⟨L⟩) →
      LinearMap.range (M.pull (F.toOrbit.map (F.inclusion hLT))) ≤
        LinearMap.range (F.normalizerTrace M T L)

/-- The actual restriction vanishes; no centralizer-zero conclusion is
present among the reference inputs. -/
theorem simple_centralizer_zero (DP : F.DiazParkTraceInput (k := k))
    (p : ℕ) [Fact p.Prime] [CharP k p] (hS : IsPGroup p S)
    (M : MackeyModule.{u,u,u} k F.Orbit F.mackeyShape) (label : F.SimpleLabel M)
    (T L : Subgroup S) (hLT : L ≤ T)
    (hL : Nonempty (label.Q ≅ F.toOrbit.obj ⟨L⟩))
    (bad : ¬ Subgroup.centralizer (L : Set S) ⊓ T ≤ L) :
    M.pull (F.toOrbit.map (F.inclusion hLT)) = 0 := by
  apply LinearMap.ext
  intro x
  have hx := DP.equations_4_6 M label T L hLT hL ⟨x, rfl⟩
  rw [F.normalizerTrace_zero M p hS T L bad, LinearMap.range_zero] at hx
  exact hx

end Sharpness.FusionSystem
