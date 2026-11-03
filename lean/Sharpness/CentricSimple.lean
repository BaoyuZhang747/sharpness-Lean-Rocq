import Sharpness.ReferenceInputs
import Sharpness.Saturation
import Sharpness.PrimeLocalRing
import Sharpness.ScalarMackey
import Sharpness.ScalarBar

/-!
Manuscript Proposition 2.3. DP Theorem A is imported only at its actual
Z_(p)-valued restricted-Mackey statement. The supported restriction,
scalar restriction and transfer of vanishing back to k are proved here.
-/
set_option autoImplicit false
noncomputable section
universe u
namespace Sharpness.FusionSystem
open CategoryTheory
variable {S : Type u} [Group S] [Finite S] (F : FusionSystem S)
    (p : ℕ) [Fact p.Prime]
    (hS : IsPGroup p S) (saturated : F.Saturated p)
    [EnoughProjectives (CoefficientCategory (PrimeLocalRing.{u} p) F.CentricOrbit)]

/-- Precisely the ground ring and restricted Mackey hypothesis in the
published Theorem A. No supported-full-Mackey conclusion is assumed. -/
structure DiazParkTheoremAInput (hS : IsPGroup p S) (saturated : F.Saturated p) where
  theorem_A : ∀ A : RestrictedMackeyModule.{u,u,u} (PrimeLocalRing.{u} p)
      F.Orbit F.mackeyShape F.centricProperty,
    Acyclic A.coefficient

variable {k : Type u} [Field k] [CharP k p]
    [EnoughProjectives (CoefficientCategory k F.CentricOrbit)]
    (DP : F.DiazParkTheoremAInput p hS saturated)
    (barR : FiniteBarModel (PrimeLocalRing.{u} p) F.CentricOrbit) (cmpR : barR.Comparison)
    (barK : FiniteBarModel k F.CentricOrbit) (cmpK : barK.Comparison)
    (scalar : ScalarBarComparison barR barK)

include DP cmpR cmpK scalar

theorem acyclic_of_centric_support
    (M : MackeyModule.{u,u,u} k F.Orbit F.mackeyShape)
    (supported : ∀ P, ¬ F.IsCentric P.as.subgroup → ∀ x : M.Value P, x = 0) :
    Acyclic (F.centricCoefficient M) := by
  let R := PrimeLocalRing.{u} p
  let A := M.restrictScalars R
  have hs : ∀ P, ¬ F.centricProperty P → ∀ x : A.Value P, x = 0 := supported
  let N := A.restrictSupported F.centricProperty hs
  have hN := DP.theorem_A N
  let e : N.coefficient ≅ F.centricCoefficient A :=
    NatIso.ofComponents (fun _ => Iso.refl _) (by intros; rfl)
  have hA : Acyclic (F.centricCoefficient A) := acyclic_of_iso e.symm hN
  have hR : Acyclic (restrictCoefficientScalars (R := R) (F.centricCoefficient M)) :=
    acyclic_of_iso (F.centricRestrictScalarsIso (R := R) M).symm hA
  exact scalar.acyclic_of_restrict (F.centricCoefficient M) cmpR cmpK hR

/-- The formerly missing bridge is now constructed from the exact published
input and general bar comparison. It is no longer a hypothesis. -/
def supportedCentricBridge : F.SupportedCentricBridge (k := k) where
  acyclic_of_supported := F.acyclic_of_centric_support p hS saturated DP barR cmpR barK cmpK scalar

theorem centric_simple_acyclic_from_references
    (classification : F.DiazParkInputs (k := k))
    (M : MackeyModule.{u,u,u} k F.Orbit F.mackeyShape) (label : F.SimpleLabel M)
    (centric : F.IsCentric label.Q.as.subgroup) : Acyclic (F.centricCoefficient M) :=
  F.centric_simple_acyclic classification
    (F.supportedCentricBridge p hS saturated DP barR cmpR barK cmpK scalar) M label centric

end Sharpness.FusionSystem
