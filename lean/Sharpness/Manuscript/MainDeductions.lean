import Sharpness.Unconditional.LocalSharpness
import Sharpness.Unconditional.ScalarHigherLimits

/-! The literal finite-dimensional Díaz–Park conjecture and the manuscript's
deduction of characteristic-p field sharpness from localized-integer sharpness.
The latter uses the actual scalar comparison, not a direct second invocation
of the characteristic-p sharpness theorem. -/
set_option autoImplicit false
noncomputable section
universe u

namespace Sharpness.FusionSystem
open CategoryTheory CategoryTheory.Limits

/-- Conjecture `conj:dp`, including its finite-dimensional-value hypothesis. -/
theorem diaz_park_conjecture (p : ℕ) [Fact p.Prime]
    {S : Type u} [Group S] [Finite S] (F : FusionSystem S)
    (hS : IsPGroup p S) (sat : F.Saturated p)
    (M : MackeyModule.{u,u,u} (PrimeField.{u} p) F.Orbit F.mackeyShape)
    [∀ P, FiniteDimensional (PrimeField.{u} p) (M.Value P)] :
    Acyclic (F.centricCoefficient M) :=
  F.saturated_fusion_sharpness_unconditional p (PrimeField.{u} p) hS sat M

/-- Corollary `cor:field`, deduced from Theorem `thm:main` by restriction of
scalars along the canonical map from the localized integers. -/
theorem field_sharpness_of_primeLocal (p : ℕ) [Fact p.Prime]
    (k : Type u) [Field k] [CharP k p]
    {S : Type u} [Group S] [Finite S] (F : FusionSystem S)
    (hS : IsPGroup p S) (sat : F.Saturated p) : F.Sharp (R := k) := by
  intro M
  have hM := F.saturated_fusion_sharpness_primeLocal_unconditional p hS sat
    (M.restrictScalars (PrimeLocalRing.{u} p))
  have hrestricted : Acyclic
      (F.centricCoefficient M ⋙ ModuleCat.restrictScalars
        (algebraMap (PrimeLocalRing.{u} p) k)) :=
    acyclic_of_iso (F.centricRestrictScalarsIso M).symm hM
  intro n hn
  have hz : IsZero ((ModuleCat.restrictScalars
      (algebraMap (PrimeLocalRing.{u} p) k)).obj
        (higherLimit (F.centricCoefficient M) n)) :=
    IsZero.of_iso (hrestricted n hn)
      (Unconditional.scalarHigherLimitIso (R := PrimeLocalRing.{u} p)
        (F.centricCoefficient M) n)
  have hzsub := (ModuleCat.isZero_iff_subsingleton
    (R := PrimeLocalRing.{u} p)).mp hz
  exact (ModuleCat.isZero_iff_subsingleton (R := k)).mpr hzsub

end Sharpness.FusionSystem
